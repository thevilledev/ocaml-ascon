---------------------------- MODULE AeadDecrypt ----------------------------
(***************************************************************************)
(* Statement-level model of Ascon.Aead128.decrypt / decrypt_combined       *)
(* (lib/ascon.ml:116-175) and Constant_time.equal                          *)
(* (lib/internal/constant_time.ml), with the cryptography abstracted:      *)
(*                                                                         *)
(* * The expected tag is an uninterpreted function of (key, nonce, ad,     *)
(*   ciphertext).  Each behaviour performs one call, so choosing its value *)
(*   nondeterministically at finalisation quantifies over ALL such         *)
(*   functions.                                                            *)
(* * The keystream byte at rate position r after the ciphertext prefix s  *)
(*   has been absorbed is the free atom <<"ks", s, r>> (key, nonce and ad  *)
(*   are fixed per call); a byte is a set of atoms and XOR is symmetric    *)
(*   difference, exactly as in Sponge.tla.                                 *)
(* * An adversary chooses the ciphertext, a tag of arbitrary (possibly     *)
(*   wrong) length and arbitrary content, or an arbitrary combined input. *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS
    Word,       \* bytes per 64-bit word (real: 8); the AEAD rate is 2*Word
    TagSize,    \* Aead128.tag_size (real: 16)
    CtLens,     \* ciphertext lengths for direct decrypt calls
    TagLens,    \* adversarial tag lengths for direct decrypt calls
    CombLens,   \* lengths of decrypt_combined inputs
    ByteVals,   \* byte values (naturals < 256) for tags / combined inputs
    EqLens,     \* lengths for the stand-alone Constant_time.equal checks
    EqVals,     \* byte values for the stand-alone Constant_time.equal checks
    Entries     \* subset of {"decrypt", "combined", "equal"}

ASSUME /\ Word \in Nat \ {0} /\ TagSize \in Nat \ {0}
       /\ ByteVals \subseteq 0..255 /\ EqVals \subseteq 0..255
       /\ Entries \subseteq {"decrypt", "combined", "equal"}

Rate == 2 * Word                                    \* ascon.ml: 16-byte blocks

Bits(n) == {<<"bit", k>> : k \in {j \in 0..7 : (n \div (2^j)) % 2 = 1}}
Xor(a, b) == (a \ b) \cup (b \ a)                   \* lxor on bytes
Lor(a, b) == a \cup b                               \* lor on bytes
ZeroByte == {}
Undef == {<<"uninitialised">>}                      \* Bytes.create content
Zeros(n) == [j \in 1..n |-> ZeroByte]
ByteSets == {Bits(v) : v \in ByteVals}
EqSets == {Bits(v) : v \in EqVals}
Min(a, b) == IF a < b THEN a ELSE b

(* Keystream byte r (0-based rate position) after absorbing prefix s.     *)
KS(s, r) == {<<"ks", s, r>>}
(* Store n bytes of (keystream from rate position r0) XOR ciphertext into *)
(* plaintext at 0-based offset `off` (store64_le / store_partial_le).     *)
StoreKs(pt, off, s, r0, n, ct) ==
    [j \in 1..Len(pt) |-> IF j > off /\ j <= off + n
                          THEN Xor(KS(s, r0 + (j - off - 1)), ct[j])
                          ELSE pt[j]]
(* SP 800-232 decryption: P_i = S[0:127] xor C_i, and the rate is replaced *)
(* by C_i before each p[8]: the keystream for byte j depends on the        *)
(* ciphertext prefix up to the start of j's block.                         *)
SpecPt(ct) ==
    [j \in 1..Len(ct) |->
        Xor(KS(SubSeq(ct, 1, ((j - 1) \div Rate) * Rate), (j - 1) % Rate), ct[j])]
StoreOK(off, n, total) == off >= 0 /\ n >= 0 /\ n <= Word /\ off + n <= total

(***************************************************************************
--fair algorithm AeadDecrypt {
variables
    heap = << >>,           \* OCaml heap: object id -> bytes value
    entry = "none",         \* API function invoked by the caller
    combObj = 0,            \* caller's `combined` argument
    ctObj = 0,              \* `ciphertext` argument of decrypt
    tagObj = 0,             \* `tag` argument of decrypt
    ptObj = 0,              \* `plaintext` candidate buffer
    etObj = 0,              \* `expected_tag`
    expTag = << >>,         \* ghost: value of the abstract MAC for this call
    st = << >>,             \* symbolic state: ciphertext prefix absorbed
    len = 0,                \* `length`
    off = 0,                \* `!offset`
    rem = 0,                \* `remaining`
    result = [r |-> "pending"],
    visible = {},           \* heap objects reachable from caller-held values
    events = << >>,         \* ghost: trace of processing steps
    ctRes = FALSE,          \* return value of Constant_time.equal
    ctLog = [done |-> FALSE];  \* ghost: record of the last equal call

\* ------------- Constant_time.equal (constant_time.ml:1-11) -------------
procedure CtEqual(a, b)
variables ctLen = 0, diff = ZeroByte, ci = 0, iters = 0, trace = << >>;
{
ct_len:         \* constant_time.ml:2-3
    if (Len(heap[a]) # Len(heap[b])) {
        ctRes := FALSE;
        ctLog := [done |-> TRUE, a |-> heap[a], b |-> heap[b], res |-> FALSE,
                  iters |-> 0, trace |-> << >>];
        return;
    } else {
        ctLen := Len(heap[a]);
    };
ct_loop:        \* constant_time.ml:5-10, one step per iteration
    while (ci < ctLen) {
        diff := Lor(diff, Xor(heap[a][ci + 1], heap[b][ci + 1]));
        iters := iters + 1;
        trace := Append(trace, ci);
        ci := ci + 1;
    };
ct_ret:         \* constant_time.ml:11  !difference = 0
    ctRes := (diff = ZeroByte);
    ctLog := [done |-> TRUE, a |-> heap[a], b |-> heap[b], res |-> (diff = ZeroByte),
              iters |-> iters, trace |-> trace];
    return;
}

{
start:
    either {
        \* adversary calls decrypt ~ciphertext ~tag
        await "decrypt" \in Entries;
        with (n \in CtLens, tl \in TagLens) {
            with (t \in [1..tl -> ByteSets]) {
                entry := "decrypt";
                heap := <<[j \in 1..n |-> {<<"c", j>>}], t>>;
                ctObj := 1;
                tagObj := 2;
                visible := {1, 2};
            }
        };
        goto d_check;
    } or {
        \* adversary calls decrypt_combined with arbitrary bytes
        await "combined" \in Entries;
        with (n \in CombLens) {
            with (c \in [1..n -> ByteSets]) {
                entry := "combined";
                heap := <<c>>;
                combObj := 1;
                visible := {1};
            }
        };
        goto dc_len;
    } or {
        \* stand-alone Constant_time.equal on arbitrary byte strings
        await "equal" \in Entries;
        with (n1 \in EqLens, n2 \in EqLens) {
            with (x \in [1..n1 -> EqSets], y \in [1..n2 -> EqSets]) {
                entry := "equal";
                heap := <<x, y>>;
                visible := {1, 2};
            }
        };
        call CtEqual(1, 2);
        goto Done;
    };

\* ---------------- decrypt_combined (ascon.ml:168-175) ----------------
dc_len:         \* ascon.ml:169-170
    if (Len(heap[combObj]) < TagSize) {
        result := [r |-> "Invalid_tag_length"];
        events := events \o <<"combined_len_check", "return">>;
        goto Done;
    } else {
        events := Append(events, "combined_len_check");
    };
dc_sub_ct:      \* ascon.ml:172-173  Bytes.sub combined 0 ciphertext_length
    with (id = Len(heap) + 1,
          v = SubSeq(heap[combObj], 1, Len(heap[combObj]) - TagSize)) {
        heap := Append(heap, v);
        ctObj := id;
    };
dc_sub_tag:     \* ascon.ml:174  Bytes.sub combined ciphertext_length tag_size
    with (id = Len(heap) + 1,
          v = SubSeq(heap[combObj], Len(heap[combObj]) - TagSize + 1,
                     Len(heap[combObj]))) {
        heap := Append(heap, v);
        tagObj := id;
    };
    \* ascon.ml:175 tail call of decrypt

\* ---------------- decrypt (ascon.ml:116-156) ----------------
d_check:        \* ascon.ml:117
    if (Len(heap[tagObj]) # TagSize) {
        result := [r |-> "Invalid_tag_length"];
        events := events \o <<"tag_len_check", "return">>;
        goto Done;
    } else {
        events := Append(events, "tag_len_check");
    };
d_init:         \* ascon.ml:119  initialize key nonce
    st := << >>;
    events := Append(events, "initialize");
d_ad:           \* ascon.ml:120  absorb_associated_data (+ domain separation)
    events := Append(events, "absorb_ad");
d_alloc:        \* ascon.ml:121-123
    len := Len(heap[ctObj]);
    with (id = Len(heap) + 1, v = [j \in 1..Len(heap[ctObj]) |-> Undef]) {
        heap := Append(heap, v);
        ptObj := id;
    };
    off := 0;
    events := Append(events, "alloc_plaintext");
d_loop:         \* ascon.ml:124
    while (len - off >= Rate) {
d_blk_lo:       \* ascon.ml:125,127  store64_le plaintext off (x0 xor c0)
        assert StoreOK(off, Word, len);
        heap[ptObj] := StoreKs(heap[ptObj], off, st, 0, Word, heap[ctObj]);
d_blk_hi:       \* ascon.ml:126,128  store64_le plaintext (off+8) (x1 xor c1)
        assert StoreOK(off + Word, Word, len);
        heap[ptObj] := StoreKs(heap[ptObj], off + Word, st, Word, Word, heap[ctObj]);
d_blk_st:       \* ascon.ml:129-132  x0 <- c0; x1 <- c1; p8; offset += 16
        st := st \o SubSeq(heap[ctObj], off + 1, off + Rate);
        off := off + Rate;
    };
d_tail:         \* ascon.ml:134-135
    rem := len - off;
    if (len - off >= Word) {
d_tA_lo:        \* ascon.ml:136,139  store64_le plaintext off (x0 xor c0)
        assert StoreOK(off, Word, len);
        heap[ptObj] := StoreKs(heap[ptObj], off, st, 0, Word, heap[ctObj]);
d_tA_hi:        \* ascon.ml:137-138,140-141  store_partial_le (off+8) .. tail
        assert StoreOK(off + Word, rem - Word, len);
        heap[ptObj] := StoreKs(heap[ptObj], off + Word, st, Word, rem - Word, heap[ctObj]);
d_tA_st:        \* ascon.ml:142-144  state rate := c, padding
        st := st \o SubSeq(heap[ctObj], off + 1, len);
    } else {
d_tB:           \* ascon.ml:146-148  store_partial_le plaintext off .. remaining
        assert StoreOK(off, rem, len);
        heap[ptObj] := StoreKs(heap[ptObj], off, st, 0, rem, heap[ctObj]);
d_tB_st:        \* ascon.ml:149-150  state rate := c, padding
        st := st \o SubSeq(heap[ctObj], off + 1, len);
    };
d_final:        \* ascon.ml:151  let expected_tag = finalize state k0 k1
    with (t \in [1..TagSize -> ByteSets], id = Len(heap) + 1) {
        heap := Append(heap, t);
        etObj := id;
        expTag := t;
    };
    events := Append(events, "finalize");
d_cmp:          \* ascon.ml:152  Constant_time.equal expected_tag tag
    events := Append(events, "compare");
    call CtEqual(etObj, tagObj);
d_branch:       \* ascon.ml:152-153
    if (ctRes) {
        result := [r |-> "Ok", pt |-> ptObj];
        visible := visible \cup {ptObj};
        events := Append(events, "return");
        goto Done;
    };
d_fill:         \* ascon.ml:155  Bytes.fill plaintext 0 length '\000'
    heap[ptObj] := Zeros(len);
    events := Append(events, "zero_fill");
d_fail:         \* ascon.ml:156
    result := [r |-> "Authentication_failure"];
    events := Append(events, "return");
}
}
 ***************************************************************************)
\* BEGIN TRANSLATION
CONSTANT defaultInitValue
VARIABLES heap, entry, combObj, ctObj, tagObj, ptObj, etObj, expTag, st, len, 
          off, rem, result, visible, events, ctRes, ctLog, pc, stack, a, b, 
          ctLen, diff, ci, iters, trace

vars == << heap, entry, combObj, ctObj, tagObj, ptObj, etObj, expTag, st, len, 
           off, rem, result, visible, events, ctRes, ctLog, pc, stack, a, b, 
           ctLen, diff, ci, iters, trace >>

Init == (* Global variables *)
        /\ heap = << >>
        /\ entry = "none"
        /\ combObj = 0
        /\ ctObj = 0
        /\ tagObj = 0
        /\ ptObj = 0
        /\ etObj = 0
        /\ expTag = << >>
        /\ st = << >>
        /\ len = 0
        /\ off = 0
        /\ rem = 0
        /\ result = [r |-> "pending"]
        /\ visible = {}
        /\ events = << >>
        /\ ctRes = FALSE
        /\ ctLog = [done |-> FALSE]
        (* Procedure CtEqual *)
        /\ a = defaultInitValue
        /\ b = defaultInitValue
        /\ ctLen = 0
        /\ diff = ZeroByte
        /\ ci = 0
        /\ iters = 0
        /\ trace = << >>
        /\ stack = << >>
        /\ pc = "start"

ct_len == /\ pc = "ct_len"
          /\ IF Len(heap[a]) # Len(heap[b])
                THEN /\ ctRes' = FALSE
                     /\ ctLog' = [done |-> TRUE, a |-> heap[a], b |-> heap[b], res |-> FALSE,
                                  iters |-> 0, trace |-> << >>]
                     /\ pc' = Head(stack).pc
                     /\ ctLen' = Head(stack).ctLen
                     /\ diff' = Head(stack).diff
                     /\ ci' = Head(stack).ci
                     /\ iters' = Head(stack).iters
                     /\ trace' = Head(stack).trace
                     /\ a' = Head(stack).a
                     /\ b' = Head(stack).b
                     /\ stack' = Tail(stack)
                ELSE /\ ctLen' = Len(heap[a])
                     /\ pc' = "ct_loop"
                     /\ UNCHANGED << ctRes, ctLog, stack, a, b, diff, ci, 
                                     iters, trace >>
          /\ UNCHANGED << heap, entry, combObj, ctObj, tagObj, ptObj, etObj, 
                          expTag, st, len, off, rem, result, visible, events >>

ct_loop == /\ pc = "ct_loop"
           /\ IF ci < ctLen
                 THEN /\ diff' = Lor(diff, Xor(heap[a][ci + 1], heap[b][ci + 1]))
                      /\ iters' = iters + 1
                      /\ trace' = Append(trace, ci)
                      /\ ci' = ci + 1
                      /\ pc' = "ct_loop"
                 ELSE /\ pc' = "ct_ret"
                      /\ UNCHANGED << diff, ci, iters, trace >>
           /\ UNCHANGED << heap, entry, combObj, ctObj, tagObj, ptObj, etObj, 
                           expTag, st, len, off, rem, result, visible, events, 
                           ctRes, ctLog, stack, a, b, ctLen >>

ct_ret == /\ pc = "ct_ret"
          /\ ctRes' = (diff = ZeroByte)
          /\ ctLog' = [done |-> TRUE, a |-> heap[a], b |-> heap[b], res |-> (diff = ZeroByte),
                       iters |-> iters, trace |-> trace]
          /\ pc' = Head(stack).pc
          /\ ctLen' = Head(stack).ctLen
          /\ diff' = Head(stack).diff
          /\ ci' = Head(stack).ci
          /\ iters' = Head(stack).iters
          /\ trace' = Head(stack).trace
          /\ a' = Head(stack).a
          /\ b' = Head(stack).b
          /\ stack' = Tail(stack)
          /\ UNCHANGED << heap, entry, combObj, ctObj, tagObj, ptObj, etObj, 
                          expTag, st, len, off, rem, result, visible, events >>

CtEqual == ct_len \/ ct_loop \/ ct_ret

start == /\ pc = "start"
         /\ \/ /\ "decrypt" \in Entries
               /\ \E n \in CtLens:
                    \E tl \in TagLens:
                      \E t \in [1..tl -> ByteSets]:
                        /\ entry' = "decrypt"
                        /\ heap' = <<[j \in 1..n |-> {<<"c", j>>}], t>>
                        /\ ctObj' = 1
                        /\ tagObj' = 2
                        /\ visible' = {1, 2}
               /\ pc' = "d_check"
               /\ UNCHANGED <<combObj, stack, a, b, ctLen, diff, ci, iters, trace>>
            \/ /\ "combined" \in Entries
               /\ \E n \in CombLens:
                    \E c \in [1..n -> ByteSets]:
                      /\ entry' = "combined"
                      /\ heap' = <<c>>
                      /\ combObj' = 1
                      /\ visible' = {1}
               /\ pc' = "dc_len"
               /\ UNCHANGED <<ctObj, tagObj, stack, a, b, ctLen, diff, ci, iters, trace>>
            \/ /\ "equal" \in Entries
               /\ \E n1 \in EqLens:
                    \E n2 \in EqLens:
                      \E x \in [1..n1 -> EqSets]:
                        \E y \in [1..n2 -> EqSets]:
                          /\ entry' = "equal"
                          /\ heap' = <<x, y>>
                          /\ visible' = {1, 2}
               /\ /\ a' = 1
                  /\ b' = 2
                  /\ stack' = << [ procedure |->  "CtEqual",
                                   pc        |->  "Done",
                                   ctLen     |->  ctLen,
                                   diff      |->  diff,
                                   ci        |->  ci,
                                   iters     |->  iters,
                                   trace     |->  trace,
                                   a         |->  a,
                                   b         |->  b ] >>
                               \o stack
               /\ ctLen' = 0
               /\ diff' = ZeroByte
               /\ ci' = 0
               /\ iters' = 0
               /\ trace' = << >>
               /\ pc' = "ct_len"
               /\ UNCHANGED <<combObj, ctObj, tagObj>>
         /\ UNCHANGED << ptObj, etObj, expTag, st, len, off, rem, result, 
                         events, ctRes, ctLog >>

dc_len == /\ pc = "dc_len"
          /\ IF Len(heap[combObj]) < TagSize
                THEN /\ result' = [r |-> "Invalid_tag_length"]
                     /\ events' = events \o <<"combined_len_check", "return">>
                     /\ pc' = "Done"
                ELSE /\ events' = Append(events, "combined_len_check")
                     /\ pc' = "dc_sub_ct"
                     /\ UNCHANGED result
          /\ UNCHANGED << heap, entry, combObj, ctObj, tagObj, ptObj, etObj, 
                          expTag, st, len, off, rem, visible, ctRes, ctLog, 
                          stack, a, b, ctLen, diff, ci, iters, trace >>

dc_sub_ct == /\ pc = "dc_sub_ct"
             /\ LET id == Len(heap) + 1 IN
                  LET v == SubSeq(heap[combObj], 1, Len(heap[combObj]) - TagSize) IN
                    /\ heap' = Append(heap, v)
                    /\ ctObj' = id
             /\ pc' = "dc_sub_tag"
             /\ UNCHANGED << entry, combObj, tagObj, ptObj, etObj, expTag, st, 
                             len, off, rem, result, visible, events, ctRes, 
                             ctLog, stack, a, b, ctLen, diff, ci, iters, trace >>

dc_sub_tag == /\ pc = "dc_sub_tag"
              /\ LET id == Len(heap) + 1 IN
                   LET v == SubSeq(heap[combObj], Len(heap[combObj]) - TagSize + 1,
                                   Len(heap[combObj])) IN
                     /\ heap' = Append(heap, v)
                     /\ tagObj' = id
              /\ pc' = "d_check"
              /\ UNCHANGED << entry, combObj, ctObj, ptObj, etObj, expTag, st, 
                              len, off, rem, result, visible, events, ctRes, 
                              ctLog, stack, a, b, ctLen, diff, ci, iters, 
                              trace >>

d_check == /\ pc = "d_check"
           /\ IF Len(heap[tagObj]) # TagSize
                 THEN /\ result' = [r |-> "Invalid_tag_length"]
                      /\ events' = events \o <<"tag_len_check", "return">>
                      /\ pc' = "Done"
                 ELSE /\ events' = Append(events, "tag_len_check")
                      /\ pc' = "d_init"
                      /\ UNCHANGED result
           /\ UNCHANGED << heap, entry, combObj, ctObj, tagObj, ptObj, etObj, 
                           expTag, st, len, off, rem, visible, ctRes, ctLog, 
                           stack, a, b, ctLen, diff, ci, iters, trace >>

d_init == /\ pc = "d_init"
          /\ st' = << >>
          /\ events' = Append(events, "initialize")
          /\ pc' = "d_ad"
          /\ UNCHANGED << heap, entry, combObj, ctObj, tagObj, ptObj, etObj, 
                          expTag, len, off, rem, result, visible, ctRes, ctLog, 
                          stack, a, b, ctLen, diff, ci, iters, trace >>

d_ad == /\ pc = "d_ad"
        /\ events' = Append(events, "absorb_ad")
        /\ pc' = "d_alloc"
        /\ UNCHANGED << heap, entry, combObj, ctObj, tagObj, ptObj, etObj, 
                        expTag, st, len, off, rem, result, visible, ctRes, 
                        ctLog, stack, a, b, ctLen, diff, ci, iters, trace >>

d_alloc == /\ pc = "d_alloc"
           /\ len' = Len(heap[ctObj])
           /\ LET id == Len(heap) + 1 IN
                LET v == [j \in 1..Len(heap[ctObj]) |-> Undef] IN
                  /\ heap' = Append(heap, v)
                  /\ ptObj' = id
           /\ off' = 0
           /\ events' = Append(events, "alloc_plaintext")
           /\ pc' = "d_loop"
           /\ UNCHANGED << entry, combObj, ctObj, tagObj, etObj, expTag, st, 
                           rem, result, visible, ctRes, ctLog, stack, a, b, 
                           ctLen, diff, ci, iters, trace >>

d_loop == /\ pc = "d_loop"
          /\ IF len - off >= Rate
                THEN /\ pc' = "d_blk_lo"
                ELSE /\ pc' = "d_tail"
          /\ UNCHANGED << heap, entry, combObj, ctObj, tagObj, ptObj, etObj, 
                          expTag, st, len, off, rem, result, visible, events, 
                          ctRes, ctLog, stack, a, b, ctLen, diff, ci, iters, 
                          trace >>

d_blk_lo == /\ pc = "d_blk_lo"
            /\ Assert(StoreOK(off, Word, len), 
                      "Failure of assertion at line 201, column 9.")
            /\ heap' = [heap EXCEPT ![ptObj] = StoreKs(heap[ptObj], off, st, 0, Word, heap[ctObj])]
            /\ pc' = "d_blk_hi"
            /\ UNCHANGED << entry, combObj, ctObj, tagObj, ptObj, etObj, 
                            expTag, st, len, off, rem, result, visible, events, 
                            ctRes, ctLog, stack, a, b, ctLen, diff, ci, iters, 
                            trace >>

d_blk_hi == /\ pc = "d_blk_hi"
            /\ Assert(StoreOK(off + Word, Word, len), 
                      "Failure of assertion at line 204, column 9.")
            /\ heap' = [heap EXCEPT ![ptObj] = StoreKs(heap[ptObj], off + Word, st, Word, Word, heap[ctObj])]
            /\ pc' = "d_blk_st"
            /\ UNCHANGED << entry, combObj, ctObj, tagObj, ptObj, etObj, 
                            expTag, st, len, off, rem, result, visible, events, 
                            ctRes, ctLog, stack, a, b, ctLen, diff, ci, iters, 
                            trace >>

d_blk_st == /\ pc = "d_blk_st"
            /\ st' = st \o SubSeq(heap[ctObj], off + 1, off + Rate)
            /\ off' = off + Rate
            /\ pc' = "d_loop"
            /\ UNCHANGED << heap, entry, combObj, ctObj, tagObj, ptObj, etObj, 
                            expTag, len, rem, result, visible, events, ctRes, 
                            ctLog, stack, a, b, ctLen, diff, ci, iters, trace >>

d_tail == /\ pc = "d_tail"
          /\ rem' = len - off
          /\ IF len - off >= Word
                THEN /\ pc' = "d_tA_lo"
                ELSE /\ pc' = "d_tB"
          /\ UNCHANGED << heap, entry, combObj, ctObj, tagObj, ptObj, etObj, 
                          expTag, st, len, off, result, visible, events, ctRes, 
                          ctLog, stack, a, b, ctLen, diff, ci, iters, trace >>

d_tA_lo == /\ pc = "d_tA_lo"
           /\ Assert(StoreOK(off, Word, len), 
                     "Failure of assertion at line 214, column 9.")
           /\ heap' = [heap EXCEPT ![ptObj] = StoreKs(heap[ptObj], off, st, 0, Word, heap[ctObj])]
           /\ pc' = "d_tA_hi"
           /\ UNCHANGED << entry, combObj, ctObj, tagObj, ptObj, etObj, expTag, 
                           st, len, off, rem, result, visible, events, ctRes, 
                           ctLog, stack, a, b, ctLen, diff, ci, iters, trace >>

d_tA_hi == /\ pc = "d_tA_hi"
           /\ Assert(StoreOK(off + Word, rem - Word, len), 
                     "Failure of assertion at line 217, column 9.")
           /\ heap' = [heap EXCEPT ![ptObj] = StoreKs(heap[ptObj], off + Word, st, Word, rem - Word, heap[ctObj])]
           /\ pc' = "d_tA_st"
           /\ UNCHANGED << entry, combObj, ctObj, tagObj, ptObj, etObj, expTag, 
                           st, len, off, rem, result, visible, events, ctRes, 
                           ctLog, stack, a, b, ctLen, diff, ci, iters, trace >>

d_tA_st == /\ pc = "d_tA_st"
           /\ st' = st \o SubSeq(heap[ctObj], off + 1, len)
           /\ pc' = "d_final"
           /\ UNCHANGED << heap, entry, combObj, ctObj, tagObj, ptObj, etObj, 
                           expTag, len, off, rem, result, visible, events, 
                           ctRes, ctLog, stack, a, b, ctLen, diff, ci, iters, 
                           trace >>

d_tB == /\ pc = "d_tB"
        /\ Assert(StoreOK(off, rem, len), 
                  "Failure of assertion at line 223, column 9.")
        /\ heap' = [heap EXCEPT ![ptObj] = StoreKs(heap[ptObj], off, st, 0, rem, heap[ctObj])]
        /\ pc' = "d_tB_st"
        /\ UNCHANGED << entry, combObj, ctObj, tagObj, ptObj, etObj, expTag, 
                        st, len, off, rem, result, visible, events, ctRes, 
                        ctLog, stack, a, b, ctLen, diff, ci, iters, trace >>

d_tB_st == /\ pc = "d_tB_st"
           /\ st' = st \o SubSeq(heap[ctObj], off + 1, len)
           /\ pc' = "d_final"
           /\ UNCHANGED << heap, entry, combObj, ctObj, tagObj, ptObj, etObj, 
                           expTag, len, off, rem, result, visible, events, 
                           ctRes, ctLog, stack, a, b, ctLen, diff, ci, iters, 
                           trace >>

d_final == /\ pc = "d_final"
           /\ \E t \in [1..TagSize -> ByteSets]:
                LET id == Len(heap) + 1 IN
                  /\ heap' = Append(heap, t)
                  /\ etObj' = id
                  /\ expTag' = t
           /\ events' = Append(events, "finalize")
           /\ pc' = "d_cmp"
           /\ UNCHANGED << entry, combObj, ctObj, tagObj, ptObj, st, len, off, 
                           rem, result, visible, ctRes, ctLog, stack, a, b, 
                           ctLen, diff, ci, iters, trace >>

d_cmp == /\ pc = "d_cmp"
         /\ events' = Append(events, "compare")
         /\ /\ a' = etObj
            /\ b' = tagObj
            /\ stack' = << [ procedure |->  "CtEqual",
                             pc        |->  "d_branch",
                             ctLen     |->  ctLen,
                             diff      |->  diff,
                             ci        |->  ci,
                             iters     |->  iters,
                             trace     |->  trace,
                             a         |->  a,
                             b         |->  b ] >>
                         \o stack
         /\ ctLen' = 0
         /\ diff' = ZeroByte
         /\ ci' = 0
         /\ iters' = 0
         /\ trace' = << >>
         /\ pc' = "ct_len"
         /\ UNCHANGED << heap, entry, combObj, ctObj, tagObj, ptObj, etObj, 
                         expTag, st, len, off, rem, result, visible, ctRes, 
                         ctLog >>

d_branch == /\ pc = "d_branch"
            /\ IF ctRes
                  THEN /\ result' = [r |-> "Ok", pt |-> ptObj]
                       /\ visible' = (visible \cup {ptObj})
                       /\ events' = Append(events, "return")
                       /\ pc' = "Done"
                  ELSE /\ pc' = "d_fill"
                       /\ UNCHANGED << result, visible, events >>
            /\ UNCHANGED << heap, entry, combObj, ctObj, tagObj, ptObj, etObj, 
                            expTag, st, len, off, rem, ctRes, ctLog, stack, a, 
                            b, ctLen, diff, ci, iters, trace >>

d_fill == /\ pc = "d_fill"
          /\ heap' = [heap EXCEPT ![ptObj] = Zeros(len)]
          /\ events' = Append(events, "zero_fill")
          /\ pc' = "d_fail"
          /\ UNCHANGED << entry, combObj, ctObj, tagObj, ptObj, etObj, expTag, 
                          st, len, off, rem, result, visible, ctRes, ctLog, 
                          stack, a, b, ctLen, diff, ci, iters, trace >>

d_fail == /\ pc = "d_fail"
          /\ result' = [r |-> "Authentication_failure"]
          /\ events' = Append(events, "return")
          /\ pc' = "Done"
          /\ UNCHANGED << heap, entry, combObj, ctObj, tagObj, ptObj, etObj, 
                          expTag, st, len, off, rem, visible, ctRes, ctLog, 
                          stack, a, b, ctLen, diff, ci, iters, trace >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == CtEqual \/ start \/ dc_len \/ dc_sub_ct \/ dc_sub_tag \/ d_check
           \/ d_init \/ d_ad \/ d_alloc \/ d_loop \/ d_blk_lo \/ d_blk_hi
           \/ d_blk_st \/ d_tail \/ d_tA_lo \/ d_tA_hi \/ d_tA_st \/ d_tB
           \/ d_tB_st \/ d_final \/ d_cmp \/ d_branch \/ d_fill \/ d_fail
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

\* END TRANSLATION

-----------------------------------------------------------------------------
(***************************************************************************)
(* Properties                                                              *)
(***************************************************************************)
Finished == result.r # "pending"
Processing == {"initialize", "absorb_ad", "alloc_plaintext", "finalize",
               "compare", "zero_fill"}
Occurs(ev) == \E j \in 1..Len(events) : events[j] = ev
Before(e1, e2) == \E j1, j2 \in 1..Len(events) :
                      j1 < j2 /\ events[j1] = e1 /\ events[j2] = e2

TypeOK ==
    /\ result.r \in {"pending", "Ok", "Authentication_failure", "Invalid_tag_length"}
    /\ \A o \in visible : o \in 1..Len(heap)
    /\ off \in Nat /\ len \in Nat

(* The tag-length check is the first thing decrypt does, and a wrong      *)
(* length returns Invalid_tag_length without any state or plaintext       *)
(* processing (no initialise, no allocation, no comparison).               *)
TagLenCheckedFirst ==
    entry = "decrypt" /\ events # << >> => events[1] = "tag_len_check"
BadTagLenRejectedEarly ==
    (Finished /\ tagObj # 0 /\ Len(heap[tagObj]) # TagSize) =>
        /\ result.r = "Invalid_tag_length"
        /\ \A ev \in Processing : ~Occurs(ev)
        /\ ptObj = 0
InvalidLenOnlyIfBadLen ==
    result.r = "Invalid_tag_length" =>
        \/ tagObj # 0 /\ Len(heap[tagObj]) # TagSize
        \/ entry = "combined" /\ Len(heap[combObj]) < TagSize

(* Plaintext is released only if the FULL expected tag equals the tag,    *)
(* and (completeness) a correct tag is never rejected.                     *)
ReleaseOnlyIfTagValid ==
    result.r = "Ok" => Len(heap[tagObj]) = TagSize /\ heap[tagObj] = expTag
RejectOnlyIfTagInvalid ==
    result.r = "Authentication_failure" => heap[tagObj] # expTag
(* A released plaintext is the fully initialised SP 800-232 decryption.   *)
OkPlaintextCorrect ==
    result.r = "Ok" => heap[result.pt] = SpecPt(heap[ctObj])
(* On failure the candidate is zero-filled BEFORE the error is returned.  *)
FailureZeroFilled ==
    result.r = "Authentication_failure" =>
        /\ heap[ptObj] = Zeros(len)
        /\ Before("zero_fill", "return")
        /\ events[Len(events)] = "return"
(* The candidate buffer is never reachable by the caller unless decrypt   *)
(* returned Ok (no partial / unauthenticated plaintext is observable).    *)
NoPartialRelease ==
    /\ ptObj # 0 /\ ptObj \in visible => result.r = "Ok"
    /\ result.r # "Ok" => ptObj \notin visible
(* The comparison happens after the whole ciphertext has been processed   *)
(* and before either outcome.                                              *)
CompareBeforeOutcome ==
    result.r \in {"Ok", "Authentication_failure"} =>
        /\ Before("finalize", "compare") /\ Before("compare", "return")

(* Constant_time.equal: correct result; for equal-length inputs exactly   *)
(* len iterations touching indices 0..len-1 in order, whatever the         *)
(* contents (the trace is a function of the lengths only, so no            *)
(* data-dependent early exit); unequal lengths return FALSE immediately.  *)
CtEqualCorrect ==
    ctLog.done => ctLog.res = (ctLog.a = ctLog.b)
CtEqualNoEarlyExit ==
    ctLog.done =>
        IF Len(ctLog.a) = Len(ctLog.b)
        THEN /\ ctLog.iters = Len(ctLog.a)
             /\ ctLog.trace = [j \in 1..Len(ctLog.a) |-> j - 1]
        ELSE ctLog.iters = 0 /\ ctLog.res = FALSE

(* decrypt_combined: inputs shorter than the tag are Invalid_tag_length   *)
(* without processing; otherwise the split is ciphertext || tag with a    *)
(* tag of exactly TagSize bytes, so Invalid_tag_length never follows.      *)
CombinedShortRejected ==
    (entry = "combined" /\ Finished /\ Len(heap[combObj]) < TagSize) =>
        /\ result.r = "Invalid_tag_length"
        /\ ctObj = 0 /\ tagObj = 0
        /\ \A ev \in Processing : ~Occurs(ev)
CombinedSplit ==
    (entry = "combined" /\ tagObj # 0) =>
        /\ heap[ctObj] \o heap[tagObj] = heap[combObj]
        /\ Len(heap[tagObj]) = TagSize
        /\ result.r # "Invalid_tag_length"

-----------------------------------------------------------------------------
(* Non-vacuity witnesses (`run.sh --witnesses` checks TLC refutes each).   *)
NoW_OkMultiBlockTailA ==       \* Ok after >= 1 full block and a tail >= Word
    ~(result.r = "Ok" /\ len >= Rate + Word)
NoW_OkTailB ==                 \* Ok with a short (< Word) non-empty tail
    ~(result.r = "Ok" /\ len % Rate # 0 /\ len % Rate < Word)
NoW_AuthFailureNonEmpty == ~(result.r = "Authentication_failure" /\ len > 0)
NoW_BadTagLength == ~(entry = "decrypt" /\ result.r = "Invalid_tag_length")
NoW_CombinedOk == ~(entry = "combined" /\ result.r = "Ok" /\ Len(heap[ctObj]) > 0)
NoW_CombinedShort == ~(entry = "combined" /\ result.r = "Invalid_tag_length")
NoW_CtEqualTrue == ~(ctLog.done /\ ctLog.res /\ Len(ctLog.a) > 1)
NoW_CtEqualLateDiff ==         \* strings differing only in their last byte
    ~(ctLog.done /\ Len(ctLog.a) = Len(ctLog.b) /\ Len(ctLog.a) > 1
      /\ SubSeq(ctLog.a, 1, Len(ctLog.a) - 1) = SubSeq(ctLog.b, 1, Len(ctLog.b) - 1)
      /\ ctLog.a # ctLog.b)

AllSafety ==
    /\ TypeOK /\ TagLenCheckedFirst /\ BadTagLenRejectedEarly
    /\ InvalidLenOnlyIfBadLen /\ ReleaseOnlyIfTagValid /\ RejectOnlyIfTagInvalid
    /\ OkPlaintextCorrect /\ FailureZeroFilled /\ NoPartialRelease
    /\ CompareBeforeOutcome /\ CtEqualCorrect /\ CtEqualNoEarlyExit
    /\ CombinedShortRejected /\ CombinedSplit
=============================================================================
