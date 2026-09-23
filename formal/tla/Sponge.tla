------------------------------- MODULE Sponge -------------------------------
(***************************************************************************)
(* Statement-level model of lib/internal/sponge.ml (the persistent        *)
(* absorb/finish/squeeze machinery behind Hash256, Xof128 and Cxof128)    *)
(* together with an abstract SP 800-232 specification that it must       *)
(* refine.                                                                 *)
(*                                                                         *)
(* * The rate is a parameter (real code: 8 bytes).                         *)
(* * Ascon-p[12] is abstracted symbolically: a State.t value is the        *)
(*   sequence of 64-bit XOR masks that were applied to x0 before each p12  *)
(*   since the IV (`perms`) plus the mask XORed into x0 since the last     *)
(*   p12 (`acc`).  This pair determines all five words for ANY fixed       *)
(*   permutation, so symbolic equality implies concrete equality.  An     *)
(*   output byte j of x0 is the free atom <<"P", perms, j>> XOR acc[j].    *)
(* * A byte is a finite set of atoms and XOR is symmetric difference (the *)
(*   free GF(2) vector space over the atoms).  In "alphabet" mode, byte n *)
(*   is the set of its bit positions, so XOR is exact bytewise XOR; in    *)
(*   "tagged" mode every input byte is a fresh atom, which is maximally   *)
(*   discriminating for this data-independent code.                       *)
(* * The OCaml heap is explicit: `heap` maps object ids to State.t or     *)
(*   bytes values; contexts held by the user are records of object ids.   *)
(*   Every heap-touching OCaml statement is one PlusCal label.            *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS
    Rate,          \* sponge rate in bytes (sponge.ml hard-codes 8)
    Domains,       \* OCaml 5 domains running operations concurrently
    MaxOps,        \* operations per domain
    ChunkLens,     \* lengths of inputs passed to absorb
    SqLens,        \* lengths requested from squeeze
    Alphabet,      \* byte values (naturals < 256) used when ~Tagged
    Tagged,        \* TRUE: each input byte is a fresh distinct symbol
    Lazy,          \* TRUE: the current lazy squeeze; FALSE: the eager code before the fix
    DigestBlocks,  \* Hash256.get squeezes DigestBlocks*Rate bytes (real: 4)
    OpKinds,       \* subset of {"absorb","finish","squeeze","get","reinit"}
    MaxPerms       \* only for the PermBound state constraint (mutation runs)

ASSUME /\ Rate \in Nat \ {0}
       /\ MaxOps \in Nat
       /\ ChunkLens \subseteq Nat /\ SqLens \subseteq Nat
       /\ Alphabet \subseteq 0..255
       /\ Tagged \in BOOLEAN /\ Lazy \in BOOLEAN
       /\ DigestBlocks \in Nat \ {0}
       /\ OpKinds \subseteq {"absorb", "finish", "squeeze", "get", "reinit"}

Min(a, b) == IF a < b THEN a ELSE b

-----------------------------------------------------------------------------
(* Bytes as sets of atoms; XOR is symmetric difference.                    *)
Xor(a, b) == (a \ b) \cup (b \ a)
Bits(n) == {<<"bit", k>> : k \in {j \in 0..7 : (n \div (2^j)) % 2 = 1}}
ZeroByte == {}
PadByte == Bits(1)                       \* the 0x01 padding byte
Undef == {<<"uninitialised">>}           \* content of Bytes.create

ZeroMask == [j \in 1..Rate |-> ZeroByte]
XorMask(m1, m2) == [j \in 1..Rate |-> Xor(m1[j], m2[j])]
Zeros(n) == [j \in 1..n |-> ZeroMask]

(* Input chunks of length n.  `tag` makes tagged bytes unique per op.      *)
Chunks(n, tag) ==
    IF Tagged THEN {[j \in 1..n |-> {<<"in", tag, j>>}]}
              ELSE [1..n -> {Bits(a) : a \in Alphabet}]

-----------------------------------------------------------------------------
(* endian.ml (offsets are 0-based as in OCaml, sequences are 1-based)      *)
LoadPartialOK(b, off, n) ==                          \* endian.ml:4
    off >= 0 /\ n >= 0 /\ n <= Rate /\ off <= Len(b) - n
LoadPartial(b, off, n) ==                            \* endian.ml:3-10
    [j \in 1..Rate |-> IF j <= n THEN b[off + j] ELSE ZeroByte]
Load64(b, off) == LoadPartial(b, off, Rate)          \* endian.ml:12
PaddingOK(p) == p \in 0..(Rate - 1)                  \* endian.ml:27
Padding(p) ==                                        \* endian.ml:26-28
    [j \in 1..Rate |-> IF j = p + 1 THEN PadByte ELSE ZeroByte]

(* Bytes.blit src so dst do n (OCaml stdlib)                               *)
BlitOK(src, so, dst, do, n) ==
    n >= 0 /\ so >= 0 /\ so + n <= Len(src) /\ do >= 0 /\ do + n <= Len(dst)
Blit(src, so, dst, do, n) ==
    [j \in 1..Len(dst) |-> IF j > do /\ j <= do + n THEN src[so + (j - do)]
                                                    ELSE dst[j]]

(* Symbolic Ascon-p[12] and the byte extraction of squeeze (sponge.ml:71-75) *)
P12(s) == [perms |-> Append(s.perms, s.acc), acc |-> ZeroMask]
X0Byte(s, j) == Xor({<<"P", s.perms, j>>}, s.acc[j + 1])

-----------------------------------------------------------------------------
(***************************************************************************)
(* Abstract SP 800-232 sponge (Hash256 / XOF128 / CXOF128, byte inputs).   *)
(* An absorbing context means a pair (pre, m): `pre` is the mask history   *)
(* before the message (<<ZeroMask>> = the IV permutation for Hash/XOF;    *)
(* longer for CXOF after customization) and m the message so far.  A      *)
(* squeezing context means (fin, p): fin = the mask history after the     *)
(* final padded block, p = number of output bytes already emitted.        *)
(***************************************************************************)
PadMsg(m) ==          \* m || 0x01 || 0* up to a multiple of Rate
    m \o <<PadByte>> \o [j \in 1..(Rate - 1 - (Len(m) % Rate)) |-> ZeroByte]
Blocks(s) == [k \in 1..(Len(s) \div Rate) |-> SubSeq(s, (k - 1) * Rate + 1, k * Rate)]
FullBlocks(m) == Blocks(SubSeq(m, 1, (Len(m) \div Rate) * Rate))
TailBytes(m) == SubSeq(m, Len(m) - (Len(m) % Rate) + 1, Len(m))
SpecFin(pre, m) == pre \o Blocks(PadMsg(m))   \* one p12 per padded block
(* Output byte q (0-based): block q \div Rate is read after that many      *)
(* further permutations, byte q % Rate of x0.                               *)
SpecOut(fin, q) == {<<"P", fin \o Zeros(q \div Rate), q % Rate>>}
SpecSeg(fin, p, n) == [j \in 1..n |-> SpecOut(fin, p + j - 1)]
(* Minimum number of squeeze-phase p12 calls needed to emit bytes 0..p-1: *)
(* only the permutations BETWEEN emitted blocks.                           *)
NeedSq(p) == IF p = 0 THEN 0 ELSE (p - 1) \div Rate
DigestLen == DigestBlocks * Rate

(* Abstraction function: the concrete representation the implementation   *)
(* must hold for a given abstract meaning.                                 *)
AbsState(pre, m) == [perms |-> pre \o FullBlocks(m), acc |-> ZeroMask]
SqPermsDone(p) == IF Lazy THEN NeedSq(p) ELSE p \div Rate
SqOffset(p) ==
    IF Lazy THEN (IF p = 0 THEN 0 ELSE ((p - 1) % Rate) + 1) ELSE p % Rate
SqState(fin, p) == [perms |-> fin \o Zeros(SqPermsDone(p)), acc |-> ZeroMask]
OffRange == IF Lazy THEN 0..Rate ELSE 0..(Rate - 1)

-----------------------------------------------------------------------------
(* Heap objects are identified by <<allocator, n, type>> where type is    *)
(* "st" (State.t) or "by" (bytes).  Sponge.init's result (sponge.ml:9-12) *)
(* is pre-allocated: a p12'd IV state and a zero buffer.                   *)
NoObj == <<"none", 0, "none">>
InitSt == <<"init", 1, "st">>
InitBuf == <<"init", 2, "by">>
InitCtx == [k |-> "abs", st |-> InitSt, buf |-> InitBuf, buffered |-> 0]
InitGhost == [pre |-> <<ZeroMask>>, msg |-> << >>]
InitHeap == (InitSt :> [perms |-> <<ZeroMask>>, acc |-> ZeroMask])
            @@ (InitBuf :> [j \in 1..Rate |-> ZeroByte])
NullCtx == [k |-> "none", st |-> NoObj, buf |-> NoObj, buffered |-> 0, off |-> 0]
IsStateObj(o) == o[3] = "st"
(* The value of a context: the heap objects it references, dereferenced.   *)
DerefH(h, c) == IF c.k = "abs"
                THEN [st |-> h[c.st], buf |-> h[c.buf], buffered |-> c.buffered]
                ELSE [st |-> h[c.st], off |-> c.off]

(***************************************************************************
--algorithm Sponge {
variables
    heap = InitHeap,       \* the OCaml heap: object id -> State.t | bytes
    pool = {[ctx |-> InitCtx, g |-> InitGhost,        \* contexts returned
             snap |-> [st |-> InitHeap[InitSt],       \* to the user, with
                       buf |-> InitHeap[InitBuf],     \* ghost meaning and a
                       buffered |-> 0]]},             \* deep snapshot
    outs = {},             \* ghost log of every squeeze/get result
    userObjs = {},         \* bytes owned by the user (inputs, outputs)
    nalloc = [d \in Domains |-> 0];

define {
    AbsPool == {e \in pool : e.ctx.k = "abs"}
    SqPool  == {e \in pool : e.ctx.k = "sq"}
    Reach(c) == CASE c.k = "abs" -> {c.st, c.buf}
                  [] c.k = "sq"  -> {c.st}
                  [] OTHER       -> {}
    PoolReach == UNION {Reach(e.ctx) : e \in pool}
    Deref(c) == DerefH(heap, c)
    NewId(d, t) == <<d, nalloc[d] + 1, t>>
}

\* A write to a field/byte of heap object o (records o in the write set).
macro Write(o, v) {
    heap[o] := v;
    wr := wr \cup {o};
}

\* Allocation of a fresh heap object (State.copy, Bytes.copy, Bytes.create,
\* Bytes.make).  The initialising writes are not writes to shared objects.
macro Alloc(dst, t, v) {
    with (id = NewId(self, t), val = v) {
        heap := heap @@ (id :> val);
        dst := id;
        nalloc[self] := nalloc[self] + 1;
    }
}

\* Publication of a result context to the user (the OCaml function returns).
macro Publish(c, g) {
    pool := pool \cup {[ctx |-> c, g |-> g, snap |-> DerefH(heap, c)]};
}

fair process (Dom \in Domains)
variables
    opsDone = 0,
    kind = "none",
    cIn = NullCtx,      \* the (published) input context of the operation
    gIn = InitGhost,    \* ghost: its abstract meaning
    cSq = NullCtx,      \* input of the squeeze loop (published, or finish's result for get)
    chunk = << >>,      \* ghost: the input bytes
    inObj = NoObj,      \* the user's input `bytes` object
    opBase = 0,         \* allocations with index > opBase are fresh in this op
    wr = {},            \* ghost: objects written by the current operation
    nperm = 0,          \* ghost: p12 calls performed by the current operation
    fin = << >>,        \* ghost: spec mask history after finalisation
    gpos = 0,           \* ghost: spec output position at squeeze start
    \* OCaml locals
    st = NoObj,         \* `state`
    buf = NoObj,        \* `buffer`
    buffered = 0,       \* `!buffered`
    inOff = 0,          \* `!input_offset`
    take = 0,           \* `take`
    offset = 0,         \* `!offset`
    len = 0,            \* squeeze `length`
    outObj = NoObj,     \* squeeze `output`
    written = 0,        \* `!written`
    i = 0;              \* for-loop index
{
pick:
    if (opsDone < MaxOps) {
        either {
            \* user code: allocate an input and call Sponge.absorb ctx input
            await "absorb" \in OpKinds;
            with (e \in AbsPool, n \in ChunkLens) {
                with (c \in Chunks(n, <<self, opsDone>>), id = NewId(self, "by")) {
                    kind := "absorb"; cIn := e.ctx; gIn := e.g; nperm := 0;
                    chunk := c; inObj := id; opBase := id[2];
                    heap := heap @@ (id :> c);
                    userObjs := userObjs \cup {id};
                    nalloc[self] := nalloc[self] + 1;
                }
            };
            goto ab_copy_state;
        } or {
            \* Sponge.finish (Xof/Cxof start_squeezing), Hash256.get, or the
            \* of_state (finish_state _) step of Cxof128.init
            with (e \in AbsPool, k \in OpKinds \cap {"finish", "get", "reinit"}) {
                kind := k; cIn := e.ctx; gIn := e.g; nperm := 0;
                opBase := nalloc[self];
            };
            goto fs_copy;
        } or {
            \* Sponge.squeeze ctx length (Xof128/Cxof128.squeeze)
            await "squeeze" \in OpKinds;
            with (e \in SqPool, n \in SqLens) {
                kind := "squeeze"; cIn := e.ctx; cSq := e.ctx; gIn := e.g;
                nperm := 0; opBase := nalloc[self];
                len := n; fin := e.g.fin; gpos := e.g.pos;
            };
            goto sq_copy;
        }
    } else {
        goto Done;
    };

\* ---------------- Sponge.absorb (sponge.ml:18-40) ----------------
ab_copy_state:    \* sponge.ml:19   let state = State.copy context.state
    Alloc(st, "st", heap[cIn.st]);
ab_copy_buf:      \* sponge.ml:20-23 Bytes.copy context.buffer; locals
    Alloc(buf, "by", heap[cIn.buf]);
    buffered := cIn.buffered;
    inOff := 0;
ab_if:            \* sponge.ml:24-25
    if (buffered # 0) {
        take := Min(Rate - buffered, Len(heap[inObj]));
ab_blit1:         \* sponge.ml:26-29 blit input 0 buffer !buffered take
        assert BlitOK(heap[inObj], 0, heap[buf], buffered, take);
        Write(buf, Blit(heap[inObj], 0, heap[buf], buffered, take));
        buffered := buffered + take;
        inOff := take;
        if (buffered = Rate) {
ab_blk1_xor:      \* sponge.ml:30 -> absorb_block sponge.ml:15
            Write(st, [heap[st] EXCEPT !.acc = XorMask(@, Load64(heap[buf], 0))]);
ab_blk1_p12:      \* sponge.ml:30 -> absorb_block sponge.ml:16; sponge.ml:31
            Write(st, P12(heap[st]));
            nperm := nperm + 1;
            buffered := 0;
        }
    };
ab_loop:          \* sponge.ml:32
    while (Len(heap[inObj]) - inOff >= Rate) {
ab_blk2_xor:      \* sponge.ml:33 -> absorb_block sponge.ml:15
        Write(st, [heap[st] EXCEPT !.acc = XorMask(@, Load64(heap[inObj], inOff))]);
ab_blk2_p12:      \* sponge.ml:33 -> absorb_block sponge.ml:16; sponge.ml:34
        Write(st, P12(heap[st]));
        nperm := nperm + 1;
        inOff := inOff + Rate;
    };
ab_tail:          \* sponge.ml:36-39
    if (Len(heap[inObj]) - inOff # 0) {
        assert BlitOK(heap[inObj], inOff, heap[buf], 0, Len(heap[inObj]) - inOff);
        Write(buf, Blit(heap[inObj], inOff, heap[buf], 0, Len(heap[inObj]) - inOff));
        buffered := Len(heap[inObj]) - inOff;
    };
ab_ret:           \* sponge.ml:40   { state; buffer; buffered = !buffered }
    Publish([k |-> "abs", st |-> st, buf |-> buf, buffered |-> buffered],
            [pre |-> gIn.pre, msg |-> gIn.msg \o chunk]);
    wr := {};
    opsDone := opsDone + 1;
    goto pick;

\* ---------------- Sponge.finish_state (sponge.ml:44-51) ----------------
fs_copy:          \* sponge.ml:45   let state = State.copy context.state
    Alloc(st, "st", heap[cIn.st]);
fs_xor_data:      \* sponge.ml:46-48 x0 ^= load_partial_le context.buffer 0 buffered
    assert LoadPartialOK(heap[cIn.buf], 0, cIn.buffered);
    Write(st, [heap[st] EXCEPT !.acc =
                  XorMask(@, LoadPartial(heap[cIn.buf], 0, cIn.buffered))]);
fs_xor_pad:       \* sponge.ml:49   x0 ^= padding context.buffered
    assert PaddingOK(cIn.buffered);
    Write(st, [heap[st] EXCEPT !.acc = XorMask(@, Padding(cIn.buffered))]);
fs_p12:           \* sponge.ml:50-51
    Write(st, P12(heap[st]));
    nperm := nperm + 1;
    fin := SpecFin(gIn.pre, gIn.msg);
    gpos := 0;
    if (kind = "reinit") { goto os_copy } else { goto sos_copy };

\* ------- Sponge.finish = squeezing_of_state (finish_state _) (sponge.ml:42,53)
sos_copy:         \* sponge.ml:42   { state = State.copy state; offset = 0 }
    Alloc(st, "st", heap[st]);
    if (kind = "finish") {
        Publish([k |-> "sq", st |-> st, off |-> 0], [fin |-> fin, pos |-> 0]);
        wr := {};
        opsDone := opsDone + 1;
        goto pick;
    } else {
        \* Hash256.get (ascon.ml:187-189): squeeze the fresh context
        cSq := [k |-> "sq", st |-> st, off |-> 0];
        len := DigestLen;
        goto sq_copy;
    };

\* ------- Sponge.of_state (finish_state _) as in Cxof128.init (ascon.ml:237-243)
os_copy:          \* sponge.ml:7    State.copy state
    Alloc(st, "st", heap[st]);
os_make:          \* sponge.ml:7    Bytes.make 8 '\000'; buffered = 0; return
    Alloc(buf, "by", [j \in 1..Rate |-> ZeroByte]);
    Publish([k |-> "abs", st |-> st, buf |-> buf, buffered |-> 0],
            [pre |-> fin, msg |-> << >>]);
    wr := {};
    opsDone := opsDone + 1;
    goto pick;

\* ---------------- Sponge.squeeze (sponge.ml:55-80) ----------------
sq_copy:          \* sponge.ml:58-59 State.copy context.state; offset
    Alloc(st, "st", heap[cSq.st]);
    offset := cSq.off;
sq_create:        \* sponge.ml:60-61 Bytes.create length; written := 0
    Alloc(outObj, "by", [j \in 1..len |-> Undef]);
    written := 0;
sq_loop:          \* sponge.ml:62   while !written < length
    while (written < len) {
        if (Lazy /\ offset = Rate) {
sq_lazy_p12:      \* sponge.ml:66-68 (current code): permute only when a new block is needed
            Write(st, P12(heap[st]));
            nperm := nperm + 1;
            offset := 0;
        };
sq_take:          \* sponge.ml:69
        take := Min(Rate - offset, len - written);
        i := 0;
sq_for:           \* sponge.ml:70-76 one step per iteration: output[w+i] := x0 byte
        while (i < take) {
            Write(outObj, [heap[outObj] EXCEPT ![written + i + 1] =
                               X0Byte(heap[st], offset + i)]);
            i := i + 1;
        };
sq_adv:           \* sponge.ml:77-78
        written := written + take;
        offset := offset + take;
        if (~Lazy /\ offset = Rate) {
sq_p12:           \* EAGER VARIANT ONLY (code before the fix): permute as soon as a block is used up
            Write(st, P12(heap[st]));
            nperm := nperm + 1;
            offset := 0;
        };
    };
sq_ret:           \* sponge.ml:80   ({ state; offset }, output)
    with (c = [k |-> "sq", st |-> st, off |-> offset]) {
        outs := outs \cup {[kind |-> kind, fin |-> fin, pos |-> gpos, len |-> len,
                            out |-> heap[outObj], nperm |-> nperm,
                            inSnap |-> DerefH(heap, cSq), outSnap |-> DerefH(heap, c)]};
        if (kind = "squeeze") {
            Publish(c, [fin |-> fin, pos |-> gpos + len]);
        }
    };
    userObjs := userObjs \cup {outObj};
    wr := {};
    opsDone := opsDone + 1;
    goto pick;
}
}
 ***************************************************************************)
\* BEGIN TRANSLATION
VARIABLES heap, pool, outs, userObjs, nalloc, pc

(* define statement *)
AbsPool == {e \in pool : e.ctx.k = "abs"}
SqPool  == {e \in pool : e.ctx.k = "sq"}
Reach(c) == CASE c.k = "abs" -> {c.st, c.buf}
              [] c.k = "sq"  -> {c.st}
              [] OTHER       -> {}
PoolReach == UNION {Reach(e.ctx) : e \in pool}
Deref(c) == DerefH(heap, c)
NewId(d, t) == <<d, nalloc[d] + 1, t>>

VARIABLES opsDone, kind, cIn, gIn, cSq, chunk, inObj, opBase, wr, nperm, fin, 
          gpos, st, buf, buffered, inOff, take, offset, len, outObj, written, 
          i

vars == << heap, pool, outs, userObjs, nalloc, pc, opsDone, kind, cIn, gIn, 
           cSq, chunk, inObj, opBase, wr, nperm, fin, gpos, st, buf, buffered, 
           inOff, take, offset, len, outObj, written, i >>

ProcSet == (Domains)

Init == (* Global variables *)
        /\ heap = InitHeap
        /\ pool = {[ctx |-> InitCtx, g |-> InitGhost,
                    snap |-> [st |-> InitHeap[InitSt],
                              buf |-> InitHeap[InitBuf],
                              buffered |-> 0]]}
        /\ outs = {}
        /\ userObjs = {}
        /\ nalloc = [d \in Domains |-> 0]
        (* Process Dom *)
        /\ opsDone = [self \in Domains |-> 0]
        /\ kind = [self \in Domains |-> "none"]
        /\ cIn = [self \in Domains |-> NullCtx]
        /\ gIn = [self \in Domains |-> InitGhost]
        /\ cSq = [self \in Domains |-> NullCtx]
        /\ chunk = [self \in Domains |-> << >>]
        /\ inObj = [self \in Domains |-> NoObj]
        /\ opBase = [self \in Domains |-> 0]
        /\ wr = [self \in Domains |-> {}]
        /\ nperm = [self \in Domains |-> 0]
        /\ fin = [self \in Domains |-> << >>]
        /\ gpos = [self \in Domains |-> 0]
        /\ st = [self \in Domains |-> NoObj]
        /\ buf = [self \in Domains |-> NoObj]
        /\ buffered = [self \in Domains |-> 0]
        /\ inOff = [self \in Domains |-> 0]
        /\ take = [self \in Domains |-> 0]
        /\ offset = [self \in Domains |-> 0]
        /\ len = [self \in Domains |-> 0]
        /\ outObj = [self \in Domains |-> NoObj]
        /\ written = [self \in Domains |-> 0]
        /\ i = [self \in Domains |-> 0]
        /\ pc = [self \in ProcSet |-> "pick"]

pick(self) == /\ pc[self] = "pick"
              /\ IF opsDone[self] < MaxOps
                    THEN /\ \/ /\ "absorb" \in OpKinds
                               /\ \E e \in AbsPool:
                                    \E n \in ChunkLens:
                                      \E c \in Chunks(n, <<self, opsDone[self]>>):
                                        LET id == NewId(self, "by") IN
                                          /\ kind' = [kind EXCEPT ![self] = "absorb"]
                                          /\ cIn' = [cIn EXCEPT ![self] = e.ctx]
                                          /\ gIn' = [gIn EXCEPT ![self] = e.g]
                                          /\ nperm' = [nperm EXCEPT ![self] = 0]
                                          /\ chunk' = [chunk EXCEPT ![self] = c]
                                          /\ inObj' = [inObj EXCEPT ![self] = id]
                                          /\ opBase' = [opBase EXCEPT ![self] = id[2]]
                                          /\ heap' = heap @@ (id :> c)
                                          /\ userObjs' = (userObjs \cup {id})
                                          /\ nalloc' = [nalloc EXCEPT ![self] = nalloc[self] + 1]
                               /\ pc' = [pc EXCEPT ![self] = "ab_copy_state"]
                               /\ UNCHANGED <<cSq, fin, gpos, len>>
                            \/ /\ \E e \in AbsPool:
                                    \E k \in OpKinds \cap {"finish", "get", "reinit"}:
                                      /\ kind' = [kind EXCEPT ![self] = k]
                                      /\ cIn' = [cIn EXCEPT ![self] = e.ctx]
                                      /\ gIn' = [gIn EXCEPT ![self] = e.g]
                                      /\ nperm' = [nperm EXCEPT ![self] = 0]
                                      /\ opBase' = [opBase EXCEPT ![self] = nalloc[self]]
                               /\ pc' = [pc EXCEPT ![self] = "fs_copy"]
                               /\ UNCHANGED <<heap, userObjs, nalloc, cSq, chunk, inObj, fin, gpos, len>>
                            \/ /\ "squeeze" \in OpKinds
                               /\ \E e \in SqPool:
                                    \E n \in SqLens:
                                      /\ kind' = [kind EXCEPT ![self] = "squeeze"]
                                      /\ cIn' = [cIn EXCEPT ![self] = e.ctx]
                                      /\ cSq' = [cSq EXCEPT ![self] = e.ctx]
                                      /\ gIn' = [gIn EXCEPT ![self] = e.g]
                                      /\ nperm' = [nperm EXCEPT ![self] = 0]
                                      /\ opBase' = [opBase EXCEPT ![self] = nalloc[self]]
                                      /\ len' = [len EXCEPT ![self] = n]
                                      /\ fin' = [fin EXCEPT ![self] = e.g.fin]
                                      /\ gpos' = [gpos EXCEPT ![self] = e.g.pos]
                               /\ pc' = [pc EXCEPT ![self] = "sq_copy"]
                               /\ UNCHANGED <<heap, userObjs, nalloc, chunk, inObj>>
                    ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                         /\ UNCHANGED << heap, userObjs, nalloc, kind, cIn, 
                                         gIn, cSq, chunk, inObj, opBase, nperm, 
                                         fin, gpos, len >>
              /\ UNCHANGED << pool, outs, opsDone, wr, st, buf, buffered, 
                              inOff, take, offset, outObj, written, i >>

ab_copy_state(self) == /\ pc[self] = "ab_copy_state"
                       /\ LET id == NewId(self, "st") IN
                            LET val == heap[cIn[self].st] IN
                              /\ heap' = heap @@ (id :> val)
                              /\ st' = [st EXCEPT ![self] = id]
                              /\ nalloc' = [nalloc EXCEPT ![self] = nalloc[self] + 1]
                       /\ pc' = [pc EXCEPT ![self] = "ab_copy_buf"]
                       /\ UNCHANGED << pool, outs, userObjs, opsDone, kind, 
                                       cIn, gIn, cSq, chunk, inObj, opBase, wr, 
                                       nperm, fin, gpos, buf, buffered, inOff, 
                                       take, offset, len, outObj, written, i >>

ab_copy_buf(self) == /\ pc[self] = "ab_copy_buf"
                     /\ LET id == NewId(self, "by") IN
                          LET val == heap[cIn[self].buf] IN
                            /\ heap' = heap @@ (id :> val)
                            /\ buf' = [buf EXCEPT ![self] = id]
                            /\ nalloc' = [nalloc EXCEPT ![self] = nalloc[self] + 1]
                     /\ buffered' = [buffered EXCEPT ![self] = cIn[self].buffered]
                     /\ inOff' = [inOff EXCEPT ![self] = 0]
                     /\ pc' = [pc EXCEPT ![self] = "ab_if"]
                     /\ UNCHANGED << pool, outs, userObjs, opsDone, kind, cIn, 
                                     gIn, cSq, chunk, inObj, opBase, wr, nperm, 
                                     fin, gpos, st, take, offset, len, outObj, 
                                     written, i >>

ab_if(self) == /\ pc[self] = "ab_if"
               /\ IF buffered[self] # 0
                     THEN /\ take' = [take EXCEPT ![self] = Min(Rate - buffered[self], Len(heap[inObj[self]]))]
                          /\ pc' = [pc EXCEPT ![self] = "ab_blit1"]
                     ELSE /\ pc' = [pc EXCEPT ![self] = "ab_loop"]
                          /\ take' = take
               /\ UNCHANGED << heap, pool, outs, userObjs, nalloc, opsDone, 
                               kind, cIn, gIn, cSq, chunk, inObj, opBase, wr, 
                               nperm, fin, gpos, st, buf, buffered, inOff, 
                               offset, len, outObj, written, i >>

ab_blit1(self) == /\ pc[self] = "ab_blit1"
                  /\ Assert(BlitOK(heap[inObj[self]], 0, heap[buf[self]], buffered[self], take[self]), 
                            "Failure of assertion at line 257, column 9.")
                  /\ heap' = [heap EXCEPT ![buf[self]] = Blit(heap[inObj[self]], 0, heap[buf[self]], buffered[self], take[self])]
                  /\ wr' = [wr EXCEPT ![self] = wr[self] \cup {buf[self]}]
                  /\ buffered' = [buffered EXCEPT ![self] = buffered[self] + take[self]]
                  /\ inOff' = [inOff EXCEPT ![self] = take[self]]
                  /\ IF buffered'[self] = Rate
                        THEN /\ pc' = [pc EXCEPT ![self] = "ab_blk1_xor"]
                        ELSE /\ pc' = [pc EXCEPT ![self] = "ab_loop"]
                  /\ UNCHANGED << pool, outs, userObjs, nalloc, opsDone, kind, 
                                  cIn, gIn, cSq, chunk, inObj, opBase, nperm, 
                                  fin, gpos, st, buf, take, offset, len, 
                                  outObj, written, i >>

ab_blk1_xor(self) == /\ pc[self] = "ab_blk1_xor"
                     /\ heap' = [heap EXCEPT ![st[self]] = [heap[st[self]] EXCEPT !.acc = XorMask(@, Load64(heap[buf[self]], 0))]]
                     /\ wr' = [wr EXCEPT ![self] = wr[self] \cup {st[self]}]
                     /\ pc' = [pc EXCEPT ![self] = "ab_blk1_p12"]
                     /\ UNCHANGED << pool, outs, userObjs, nalloc, opsDone, 
                                     kind, cIn, gIn, cSq, chunk, inObj, opBase, 
                                     nperm, fin, gpos, st, buf, buffered, 
                                     inOff, take, offset, len, outObj, written, 
                                     i >>

ab_blk1_p12(self) == /\ pc[self] = "ab_blk1_p12"
                     /\ heap' = [heap EXCEPT ![st[self]] = P12(heap[st[self]])]
                     /\ wr' = [wr EXCEPT ![self] = wr[self] \cup {st[self]}]
                     /\ nperm' = [nperm EXCEPT ![self] = nperm[self] + 1]
                     /\ buffered' = [buffered EXCEPT ![self] = 0]
                     /\ pc' = [pc EXCEPT ![self] = "ab_loop"]
                     /\ UNCHANGED << pool, outs, userObjs, nalloc, opsDone, 
                                     kind, cIn, gIn, cSq, chunk, inObj, opBase, 
                                     fin, gpos, st, buf, inOff, take, offset, 
                                     len, outObj, written, i >>

ab_loop(self) == /\ pc[self] = "ab_loop"
                 /\ IF Len(heap[inObj[self]]) - inOff[self] >= Rate
                       THEN /\ pc' = [pc EXCEPT ![self] = "ab_blk2_xor"]
                       ELSE /\ pc' = [pc EXCEPT ![self] = "ab_tail"]
                 /\ UNCHANGED << heap, pool, outs, userObjs, nalloc, opsDone, 
                                 kind, cIn, gIn, cSq, chunk, inObj, opBase, wr, 
                                 nperm, fin, gpos, st, buf, buffered, inOff, 
                                 take, offset, len, outObj, written, i >>

ab_blk2_xor(self) == /\ pc[self] = "ab_blk2_xor"
                     /\ heap' = [heap EXCEPT ![st[self]] = [heap[st[self]] EXCEPT !.acc = XorMask(@, Load64(heap[inObj[self]], inOff[self]))]]
                     /\ wr' = [wr EXCEPT ![self] = wr[self] \cup {st[self]}]
                     /\ pc' = [pc EXCEPT ![self] = "ab_blk2_p12"]
                     /\ UNCHANGED << pool, outs, userObjs, nalloc, opsDone, 
                                     kind, cIn, gIn, cSq, chunk, inObj, opBase, 
                                     nperm, fin, gpos, st, buf, buffered, 
                                     inOff, take, offset, len, outObj, written, 
                                     i >>

ab_blk2_p12(self) == /\ pc[self] = "ab_blk2_p12"
                     /\ heap' = [heap EXCEPT ![st[self]] = P12(heap[st[self]])]
                     /\ wr' = [wr EXCEPT ![self] = wr[self] \cup {st[self]}]
                     /\ nperm' = [nperm EXCEPT ![self] = nperm[self] + 1]
                     /\ inOff' = [inOff EXCEPT ![self] = inOff[self] + Rate]
                     /\ pc' = [pc EXCEPT ![self] = "ab_loop"]
                     /\ UNCHANGED << pool, outs, userObjs, nalloc, opsDone, 
                                     kind, cIn, gIn, cSq, chunk, inObj, opBase, 
                                     fin, gpos, st, buf, buffered, take, 
                                     offset, len, outObj, written, i >>

ab_tail(self) == /\ pc[self] = "ab_tail"
                 /\ IF Len(heap[inObj[self]]) - inOff[self] # 0
                       THEN /\ Assert(BlitOK(heap[inObj[self]], inOff[self], heap[buf[self]], 0, Len(heap[inObj[self]]) - inOff[self]), 
                                      "Failure of assertion at line 281, column 9.")
                            /\ heap' = [heap EXCEPT ![buf[self]] = Blit(heap[inObj[self]], inOff[self], heap[buf[self]], 0, Len(heap[inObj[self]]) - inOff[self])]
                            /\ wr' = [wr EXCEPT ![self] = wr[self] \cup {buf[self]}]
                            /\ buffered' = [buffered EXCEPT ![self] = Len(heap'[inObj[self]]) - inOff[self]]
                       ELSE /\ TRUE
                            /\ UNCHANGED << heap, wr, buffered >>
                 /\ pc' = [pc EXCEPT ![self] = "ab_ret"]
                 /\ UNCHANGED << pool, outs, userObjs, nalloc, opsDone, kind, 
                                 cIn, gIn, cSq, chunk, inObj, opBase, nperm, 
                                 fin, gpos, st, buf, inOff, take, offset, len, 
                                 outObj, written, i >>

ab_ret(self) == /\ pc[self] = "ab_ret"
                /\ pool' = (pool \cup {[ctx |-> ([k |-> "abs", st |-> st[self], buf |-> buf[self], buffered |-> buffered[self]]), g |-> ([pre |-> gIn[self].pre, msg |-> gIn[self].msg \o chunk[self]]), snap |-> DerefH(heap, ([k |-> "abs", st |-> st[self], buf |-> buf[self], buffered |-> buffered[self]]))]})
                /\ wr' = [wr EXCEPT ![self] = {}]
                /\ opsDone' = [opsDone EXCEPT ![self] = opsDone[self] + 1]
                /\ pc' = [pc EXCEPT ![self] = "pick"]
                /\ UNCHANGED << heap, outs, userObjs, nalloc, kind, cIn, gIn, 
                                cSq, chunk, inObj, opBase, nperm, fin, gpos, 
                                st, buf, buffered, inOff, take, offset, len, 
                                outObj, written, i >>

fs_copy(self) == /\ pc[self] = "fs_copy"
                 /\ LET id == NewId(self, "st") IN
                      LET val == heap[cIn[self].st] IN
                        /\ heap' = heap @@ (id :> val)
                        /\ st' = [st EXCEPT ![self] = id]
                        /\ nalloc' = [nalloc EXCEPT ![self] = nalloc[self] + 1]
                 /\ pc' = [pc EXCEPT ![self] = "fs_xor_data"]
                 /\ UNCHANGED << pool, outs, userObjs, opsDone, kind, cIn, gIn, 
                                 cSq, chunk, inObj, opBase, wr, nperm, fin, 
                                 gpos, buf, buffered, inOff, take, offset, len, 
                                 outObj, written, i >>

fs_xor_data(self) == /\ pc[self] = "fs_xor_data"
                     /\ Assert(LoadPartialOK(heap[cIn[self].buf], 0, cIn[self].buffered), 
                               "Failure of assertion at line 296, column 5.")
                     /\ heap' = [heap EXCEPT ![st[self]] = [heap[st[self]] EXCEPT !.acc =
                                                               XorMask(@, LoadPartial(heap[cIn[self].buf], 0, cIn[self].buffered))]]
                     /\ wr' = [wr EXCEPT ![self] = wr[self] \cup {st[self]}]
                     /\ pc' = [pc EXCEPT ![self] = "fs_xor_pad"]
                     /\ UNCHANGED << pool, outs, userObjs, nalloc, opsDone, 
                                     kind, cIn, gIn, cSq, chunk, inObj, opBase, 
                                     nperm, fin, gpos, st, buf, buffered, 
                                     inOff, take, offset, len, outObj, written, 
                                     i >>

fs_xor_pad(self) == /\ pc[self] = "fs_xor_pad"
                    /\ Assert(PaddingOK(cIn[self].buffered), 
                              "Failure of assertion at line 300, column 5.")
                    /\ heap' = [heap EXCEPT ![st[self]] = [heap[st[self]] EXCEPT !.acc = XorMask(@, Padding(cIn[self].buffered))]]
                    /\ wr' = [wr EXCEPT ![self] = wr[self] \cup {st[self]}]
                    /\ pc' = [pc EXCEPT ![self] = "fs_p12"]
                    /\ UNCHANGED << pool, outs, userObjs, nalloc, opsDone, 
                                    kind, cIn, gIn, cSq, chunk, inObj, opBase, 
                                    nperm, fin, gpos, st, buf, buffered, inOff, 
                                    take, offset, len, outObj, written, i >>

fs_p12(self) == /\ pc[self] = "fs_p12"
                /\ heap' = [heap EXCEPT ![st[self]] = P12(heap[st[self]])]
                /\ wr' = [wr EXCEPT ![self] = wr[self] \cup {st[self]}]
                /\ nperm' = [nperm EXCEPT ![self] = nperm[self] + 1]
                /\ fin' = [fin EXCEPT ![self] = SpecFin(gIn[self].pre, gIn[self].msg)]
                /\ gpos' = [gpos EXCEPT ![self] = 0]
                /\ IF kind[self] = "reinit"
                      THEN /\ pc' = [pc EXCEPT ![self] = "os_copy"]
                      ELSE /\ pc' = [pc EXCEPT ![self] = "sos_copy"]
                /\ UNCHANGED << pool, outs, userObjs, nalloc, opsDone, kind, 
                                cIn, gIn, cSq, chunk, inObj, opBase, st, buf, 
                                buffered, inOff, take, offset, len, outObj, 
                                written, i >>

sos_copy(self) == /\ pc[self] = "sos_copy"
                  /\ LET id == NewId(self, "st") IN
                       LET val == heap[st[self]] IN
                         /\ heap' = heap @@ (id :> val)
                         /\ st' = [st EXCEPT ![self] = id]
                         /\ nalloc' = [nalloc EXCEPT ![self] = nalloc[self] + 1]
                  /\ IF kind[self] = "finish"
                        THEN /\ pool' = (pool \cup {[ctx |-> ([k |-> "sq", st |-> st'[self], off |-> 0]), g |-> ([fin |-> fin[self], pos |-> 0]), snap |-> DerefH(heap', ([k |-> "sq", st |-> st'[self], off |-> 0]))]})
                             /\ wr' = [wr EXCEPT ![self] = {}]
                             /\ opsDone' = [opsDone EXCEPT ![self] = opsDone[self] + 1]
                             /\ pc' = [pc EXCEPT ![self] = "pick"]
                             /\ UNCHANGED << cSq, len >>
                        ELSE /\ cSq' = [cSq EXCEPT ![self] = [k |-> "sq", st |-> st'[self], off |-> 0]]
                             /\ len' = [len EXCEPT ![self] = DigestLen]
                             /\ pc' = [pc EXCEPT ![self] = "sq_copy"]
                             /\ UNCHANGED << pool, opsDone, wr >>
                  /\ UNCHANGED << outs, userObjs, kind, cIn, gIn, chunk, inObj, 
                                  opBase, nperm, fin, gpos, buf, buffered, 
                                  inOff, take, offset, outObj, written, i >>

os_copy(self) == /\ pc[self] = "os_copy"
                 /\ LET id == NewId(self, "st") IN
                      LET val == heap[st[self]] IN
                        /\ heap' = heap @@ (id :> val)
                        /\ st' = [st EXCEPT ![self] = id]
                        /\ nalloc' = [nalloc EXCEPT ![self] = nalloc[self] + 1]
                 /\ pc' = [pc EXCEPT ![self] = "os_make"]
                 /\ UNCHANGED << pool, outs, userObjs, opsDone, kind, cIn, gIn, 
                                 cSq, chunk, inObj, opBase, wr, nperm, fin, 
                                 gpos, buf, buffered, inOff, take, offset, len, 
                                 outObj, written, i >>

os_make(self) == /\ pc[self] = "os_make"
                 /\ LET id == NewId(self, "by") IN
                      LET val == [j \in 1..Rate |-> ZeroByte] IN
                        /\ heap' = heap @@ (id :> val)
                        /\ buf' = [buf EXCEPT ![self] = id]
                        /\ nalloc' = [nalloc EXCEPT ![self] = nalloc[self] + 1]
                 /\ pool' = (pool \cup {[ctx |-> ([k |-> "abs", st |-> st[self], buf |-> buf'[self], buffered |-> 0]), g |-> ([pre |-> fin[self], msg |-> << >>]), snap |-> DerefH(heap', ([k |-> "abs", st |-> st[self], buf |-> buf'[self], buffered |-> 0]))]})
                 /\ wr' = [wr EXCEPT ![self] = {}]
                 /\ opsDone' = [opsDone EXCEPT ![self] = opsDone[self] + 1]
                 /\ pc' = [pc EXCEPT ![self] = "pick"]
                 /\ UNCHANGED << outs, userObjs, kind, cIn, gIn, cSq, chunk, 
                                 inObj, opBase, nperm, fin, gpos, st, buffered, 
                                 inOff, take, offset, len, outObj, written, i >>

sq_copy(self) == /\ pc[self] = "sq_copy"
                 /\ LET id == NewId(self, "st") IN
                      LET val == heap[cSq[self].st] IN
                        /\ heap' = heap @@ (id :> val)
                        /\ st' = [st EXCEPT ![self] = id]
                        /\ nalloc' = [nalloc EXCEPT ![self] = nalloc[self] + 1]
                 /\ offset' = [offset EXCEPT ![self] = cSq[self].off]
                 /\ pc' = [pc EXCEPT ![self] = "sq_create"]
                 /\ UNCHANGED << pool, outs, userObjs, opsDone, kind, cIn, gIn, 
                                 cSq, chunk, inObj, opBase, wr, nperm, fin, 
                                 gpos, buf, buffered, inOff, take, len, outObj, 
                                 written, i >>

sq_create(self) == /\ pc[self] = "sq_create"
                   /\ LET id == NewId(self, "by") IN
                        LET val == [j \in 1..len[self] |-> Undef] IN
                          /\ heap' = heap @@ (id :> val)
                          /\ outObj' = [outObj EXCEPT ![self] = id]
                          /\ nalloc' = [nalloc EXCEPT ![self] = nalloc[self] + 1]
                   /\ written' = [written EXCEPT ![self] = 0]
                   /\ pc' = [pc EXCEPT ![self] = "sq_loop"]
                   /\ UNCHANGED << pool, outs, userObjs, opsDone, kind, cIn, 
                                   gIn, cSq, chunk, inObj, opBase, wr, nperm, 
                                   fin, gpos, st, buf, buffered, inOff, take, 
                                   offset, len, i >>

sq_loop(self) == /\ pc[self] = "sq_loop"
                 /\ IF written[self] < len[self]
                       THEN /\ IF Lazy /\ offset[self] = Rate
                                  THEN /\ pc' = [pc EXCEPT ![self] = "sq_lazy_p12"]
                                  ELSE /\ pc' = [pc EXCEPT ![self] = "sq_take"]
                       ELSE /\ pc' = [pc EXCEPT ![self] = "sq_ret"]
                 /\ UNCHANGED << heap, pool, outs, userObjs, nalloc, opsDone, 
                                 kind, cIn, gIn, cSq, chunk, inObj, opBase, wr, 
                                 nperm, fin, gpos, st, buf, buffered, inOff, 
                                 take, offset, len, outObj, written, i >>

sq_take(self) == /\ pc[self] = "sq_take"
                 /\ take' = [take EXCEPT ![self] = Min(Rate - offset[self], len[self] - written[self])]
                 /\ i' = [i EXCEPT ![self] = 0]
                 /\ pc' = [pc EXCEPT ![self] = "sq_for"]
                 /\ UNCHANGED << heap, pool, outs, userObjs, nalloc, opsDone, 
                                 kind, cIn, gIn, cSq, chunk, inObj, opBase, wr, 
                                 nperm, fin, gpos, st, buf, buffered, inOff, 
                                 offset, len, outObj, written >>

sq_for(self) == /\ pc[self] = "sq_for"
                /\ IF i[self] < take[self]
                      THEN /\ heap' = [heap EXCEPT ![outObj[self]] = [heap[outObj[self]] EXCEPT ![written[self] + i[self] + 1] =
                                                                          X0Byte(heap[st[self]], offset[self] + i[self])]]
                           /\ wr' = [wr EXCEPT ![self] = wr[self] \cup {outObj[self]}]
                           /\ i' = [i EXCEPT ![self] = i[self] + 1]
                           /\ pc' = [pc EXCEPT ![self] = "sq_for"]
                      ELSE /\ pc' = [pc EXCEPT ![self] = "sq_adv"]
                           /\ UNCHANGED << heap, wr, i >>
                /\ UNCHANGED << pool, outs, userObjs, nalloc, opsDone, kind, 
                                cIn, gIn, cSq, chunk, inObj, opBase, nperm, 
                                fin, gpos, st, buf, buffered, inOff, take, 
                                offset, len, outObj, written >>

sq_adv(self) == /\ pc[self] = "sq_adv"
                /\ written' = [written EXCEPT ![self] = written[self] + take[self]]
                /\ offset' = [offset EXCEPT ![self] = offset[self] + take[self]]
                /\ IF ~Lazy /\ offset'[self] = Rate
                      THEN /\ pc' = [pc EXCEPT ![self] = "sq_p12"]
                      ELSE /\ pc' = [pc EXCEPT ![self] = "sq_loop"]
                /\ UNCHANGED << heap, pool, outs, userObjs, nalloc, opsDone, 
                                kind, cIn, gIn, cSq, chunk, inObj, opBase, wr, 
                                nperm, fin, gpos, st, buf, buffered, inOff, 
                                take, len, outObj, i >>

sq_p12(self) == /\ pc[self] = "sq_p12"
                /\ heap' = [heap EXCEPT ![st[self]] = P12(heap[st[self]])]
                /\ wr' = [wr EXCEPT ![self] = wr[self] \cup {st[self]}]
                /\ nperm' = [nperm EXCEPT ![self] = nperm[self] + 1]
                /\ offset' = [offset EXCEPT ![self] = 0]
                /\ pc' = [pc EXCEPT ![self] = "sq_loop"]
                /\ UNCHANGED << pool, outs, userObjs, nalloc, opsDone, kind, 
                                cIn, gIn, cSq, chunk, inObj, opBase, fin, gpos, 
                                st, buf, buffered, inOff, take, len, outObj, 
                                written, i >>

sq_lazy_p12(self) == /\ pc[self] = "sq_lazy_p12"
                     /\ heap' = [heap EXCEPT ![st[self]] = P12(heap[st[self]])]
                     /\ wr' = [wr EXCEPT ![self] = wr[self] \cup {st[self]}]
                     /\ nperm' = [nperm EXCEPT ![self] = nperm[self] + 1]
                     /\ offset' = [offset EXCEPT ![self] = 0]
                     /\ pc' = [pc EXCEPT ![self] = "sq_take"]
                     /\ UNCHANGED << pool, outs, userObjs, nalloc, opsDone, 
                                     kind, cIn, gIn, cSq, chunk, inObj, opBase, 
                                     fin, gpos, st, buf, buffered, inOff, take, 
                                     len, outObj, written, i >>

sq_ret(self) == /\ pc[self] = "sq_ret"
                /\ LET c == [k |-> "sq", st |-> st[self], off |-> offset[self]] IN
                     /\ outs' = (outs \cup {[kind |-> kind[self], fin |-> fin[self], pos |-> gpos[self], len |-> len[self],
                                             out |-> heap[outObj[self]], nperm |-> nperm[self],
                                             inSnap |-> DerefH(heap, cSq[self]), outSnap |-> DerefH(heap, c)]})
                     /\ IF kind[self] = "squeeze"
                           THEN /\ pool' = (pool \cup {[ctx |-> c, g |-> ([fin |-> fin[self], pos |-> gpos[self] + len[self]]), snap |-> DerefH(heap, c)]})
                           ELSE /\ TRUE
                                /\ pool' = pool
                /\ userObjs' = (userObjs \cup {outObj[self]})
                /\ wr' = [wr EXCEPT ![self] = {}]
                /\ opsDone' = [opsDone EXCEPT ![self] = opsDone[self] + 1]
                /\ pc' = [pc EXCEPT ![self] = "pick"]
                /\ UNCHANGED << heap, nalloc, kind, cIn, gIn, cSq, chunk, 
                                inObj, opBase, nperm, fin, gpos, st, buf, 
                                buffered, inOff, take, offset, len, outObj, 
                                written, i >>

Dom(self) == pick(self) \/ ab_copy_state(self) \/ ab_copy_buf(self)
                \/ ab_if(self) \/ ab_blit1(self) \/ ab_blk1_xor(self)
                \/ ab_blk1_p12(self) \/ ab_loop(self) \/ ab_blk2_xor(self)
                \/ ab_blk2_p12(self) \/ ab_tail(self) \/ ab_ret(self)
                \/ fs_copy(self) \/ fs_xor_data(self) \/ fs_xor_pad(self)
                \/ fs_p12(self) \/ sos_copy(self) \/ os_copy(self)
                \/ os_make(self) \/ sq_copy(self) \/ sq_create(self)
                \/ sq_loop(self) \/ sq_take(self) \/ sq_for(self)
                \/ sq_adv(self) \/ sq_p12(self) \/ sq_lazy_p12(self)
                \/ sq_ret(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Domains: Dom(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Domains : WF_vars(Dom(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

-----------------------------------------------------------------------------
(***************************************************************************)
(* Properties.  Names are referenced from the .cfg files and README.md.    *)
(***************************************************************************)
Idle(d) == pc[d] \in {"pick", "Done"}
Fresh(d) == {o \in DOMAIN heap : o[1] = d /\ o[2] > opBase[d]}
(* Everything the library code of domain d may read or write right now.   *)
Footprint(d) ==
    IF Idle(d) THEN {}
    ELSE Reach(cIn[d]) \cup Reach(cSq[d]) \cup Fresh(d)
         \cup (IF kind[d] = "absorb" THEN {inObj[d]} ELSE {})

TypeOK ==
    /\ \A d \in Domains :
         /\ opsDone[d] \in 0..MaxOps
         /\ buffered[d] \in 0..Rate /\ offset[d] \in 0..Rate
         /\ take[d] \in 0..Rate /\ inOff[d] \in Nat /\ written[d] \in Nat
         /\ wr[d] \subseteq DOMAIN heap
    /\ \A e \in pool : e.ctx.k \in {"abs", "sq"} /\ Reach(e.ctx) \subseteq DOMAIN heap
    /\ \A o \in DOMAIN heap : IsStateObj(o) =>
                                 /\ Len(heap[o].acc) = Rate
                                 /\ \A j \in 1..Len(heap[o].perms) : Len(heap[o].perms[j]) = Rate

(* (a) Range invariants of every context value held by the user.           *)
BufferedRange == \A e \in AbsPool : e.ctx.buffered \in 0..(Rate - 1)
OffsetRange   == \A e \in SqPool  : e.ctx.off \in OffRange
(* (a) buffer[0..buffered) holds exactly the trailing |m| mod Rate bytes.   *)
BufferContents ==
    \A e \in AbsPool :
        /\ Len(heap[e.ctx.buf]) = Rate
        /\ e.ctx.buffered = Len(e.g.msg) % Rate
        /\ SubSeq(heap[e.ctx.buf], 1, e.ctx.buffered) = TailBytes(e.g.msg)

(* (b) Refinement: every held context has exactly the representation the   *)
(* abstract meaning prescribes (this also fixes the permutation count of   *)
(* absorbing contexts: one p12 per full block, plus the IV permutation).  *)
AbsorbRefinement ==
    \A e \in AbsPool : heap[e.ctx.st] = AbsState(e.g.pre, e.g.msg)
SqueezeRefinement ==
    \A e \in SqPool : /\ heap[e.ctx.st] = SqState(e.g.fin, e.g.pos)
                      /\ e.ctx.off = SqOffset(e.g.pos)
(* (b) Every squeeze / get output is the SP 800-232 stream segment.        *)
OutputCorrect == \A o \in outs : o.out = SpecSeg(o.fin, o.pos, o.len)
(* (b) Consecutive squeezes concatenate to the single longer squeeze       *)
(* (checked on every triple of outputs actually produced in a behaviour). *)
SqueezeConcat ==
    \A o1, o2, o3 \in outs :
        (/\ o1.fin = o2.fin /\ o2.fin = o3.fin
         /\ o2.pos = o1.pos + o1.len
         /\ o3.pos = o1.pos /\ o3.len = o1.len + o2.len)
        => o3.out = o1.out \o o2.out
(* (b) A zero-length squeeze returns no bytes, performs no permutation and *)
(* returns a context equal (by value) to its input.                        *)
ZeroSqueezeNoop ==
    \A o \in outs : o.len = 0 =>
        /\ o.out = << >> /\ o.nperm = 0 /\ o.outSnap = o.inSnap

(* Loop invariants of the in-flight operations (also rule out divergence: *)
(* at the loop head offset < Rate (eager), so every iteration makes       *)
(* progress).                                                              *)
AbsorbLoopInv ==
    \A d \in Domains : pc[d] = "ab_loop" =>
        LET consumed == gIn[d].msg \o SubSeq(chunk[d], 1, inOff[d]) IN
        /\ inOff[d] <= Len(chunk[d])
        /\ buffered[d] = 0 \/ inOff[d] = Len(chunk[d])
        /\ heap[st[d]] = AbsState(gIn[d].pre, consumed)
        /\ buffered[d] = Len(consumed) % Rate
        /\ SubSeq(heap[buf[d]], 1, buffered[d]) = TailBytes(consumed)
SqueezeLoopInv ==
    \A d \in Domains : pc[d] = "sq_loop" =>
        LET p == gpos[d] + written[d] IN
        /\ written[d] <= len[d]
        /\ offset[d] \in OffRange
        /\ heap[st[d]] = SqState(fin[d], p)
        /\ offset[d] = SqOffset(p)
        /\ SubSeq(heap[outObj[d]], 1, written[d]) = SpecSeg(fin[d], gpos[d], written[d])

(* (d) Persistence: a context value returned to the user never changes.   *)
Persistence == \A e \in pool : Deref(e.ctx) = e.snap
(* (d) No operation writes an object reachable from a returned context.   *)
NoWriteToPublished == \A d \in Domains : wr[d] \cap PoolReach = {}
(* Contexts never alias user-owned bytes (inputs, returned outputs), and   *)
(* the library never writes a user-owned object.                           *)
NoUserAliasing ==
    /\ PoolReach \cap userObjs = {}
    /\ \A d \in Domains : wr[d] \cap userObjs = {}
(* Ownership discipline: an operation writes only objects it allocated.   *)
WritesOnlyFresh == \A d \in Domains : wr[d] \subseteq Fresh(d)
(* (e) Data-race freedom: no domain ever writes an object that another    *)
(* domain may concurrently read or write.  Because the condition is       *)
(* checked in every interleaved state, any racing pair of accesses would  *)
(* be caught at the later of the two.                                     *)
RaceFree ==
    \A d1, d2 \in Domains : d1 # d2 => wr[d1] \cap Footprint(d2) = {}

(* (c) Permutation economy.                                                *)
(* Absorbing contexts: exactly one p12 per absorbed full block (+ the IV). *)
AbsorbPermMinimal ==
    \A e \in AbsPool : Len(heap[e.ctx.st].perms) = Len(e.g.pre) + Len(e.g.msg) \div Rate
(* Squeezing contexts after p output bytes have performed exactly the     *)
(* minimum NeedSq(p) squeeze permutations.  EXPECTED TO FAIL (eager).      *)
PermMinimal ==
    \A e \in SqPool : Len(heap[e.ctx.st].perms) = Len(e.g.fin) + NeedSq(e.g.pos)
(* Every squeeze/get call performs the minimum number of p12 calls.        *)
(* EXPECTED TO FAIL (eager).                                               *)
OpPermMinimal ==
    \A o \in outs :
        o.nperm = (IF o.kind = "get" THEN 1 ELSE 0) + NeedSq(o.pos + o.len) - NeedSq(o.pos)
(* Hash256.get = finish + squeeze(32 bytes = 4 blocks): SP 800-232 needs   *)
(* 1 + 3 permutations.  EXPECTED TO FAIL (eager).                          *)
HashGetMinimal ==
    \A o \in outs : o.kind = "get" => o.nperm = 1 + (DigestBlocks - 1)
(* Exact characterisation of the eager implementation's overhead: a       *)
(* squeezing context holds exactly one permutation more than needed iff   *)
(* its position is a non-zero multiple of Rate; a get performs exactly    *)
(* one extra p12.  Holds for the eager code.                              *)
EagerExtraPermExact ==
    ~Lazy =>
      /\ \A e \in SqPool :
           Len(heap[e.ctx.st].perms) - Len(e.g.fin) - NeedSq(e.g.pos)
             = IF e.g.pos > 0 /\ e.g.pos % Rate = 0 THEN 1 ELSE 0
      /\ \A o \in outs : o.kind = "get" => o.nperm = 1 + DigestBlocks

(* State constraint used ONLY by the mutation experiments, to keep a       *)
(* diverging mutant finite when the invariant under test does not catch it. *)
PermBound == \A o \in DOMAIN heap : IsStateObj(o) => Len(heap[o].perms) <= MaxPerms

-----------------------------------------------------------------------------
(***************************************************************************)
(* Non-vacuity witnesses.  Each NoW_x claims that situation x is           *)
(* UNREACHABLE; `run.sh --witnesses` checks that TLC refutes every one of  *)
(* them, i.e. that the configurations really exercise these situations.   *)
(***************************************************************************)
(* absorb starting from buffered = Rate-1 that fills the buffer, absorbs a *)
(* full block directly from the input and keeps a non-empty tail.         *)
NoW_FillBlockTail ==
    ~\E d \in Domains : pc[d] = "ab_ret" /\ cIn[d].buffered = Rate - 1
                        /\ Len(chunk[d]) >= 1 + Rate + 1
(* an absorb that ends exactly on a block boundary, then is finalised     *)
(* (message length a non-zero multiple of Rate: full extra padding block) *)
NoW_FullPaddingBlock ==
    ~\E o \in outs : Len(o.fin) >= 3 /\ o.fin[Len(o.fin)] = [j \in 1..Rate |-> IF j = 1 THEN PadByte ELSE ZeroByte]
(* a squeezing context whose position is a non-zero multiple of Rate      *)
NoW_SqueezeAtBoundary == ~\E e \in SqPool : e.g.pos > 0 /\ e.g.pos % Rate = 0
(* a squeeze starting mid-block that crosses a block boundary             *)
NoW_SqueezeCrossing ==
    ~\E o \in outs : o.kind = "squeeze" /\ o.pos % Rate # 0
                     /\ (o.pos % Rate) + o.len > Rate
(* the antecedent of SqueezeConcat with two non-empty parts               *)
NoW_Concat ==
    ~\E o1, o2, o3 \in outs :
        /\ o1.fin = o2.fin /\ o2.fin = o3.fin /\ o2.pos = o1.pos + o1.len
        /\ o3.pos = o1.pos /\ o3.len = o1.len + o2.len
        /\ o1.len > 0 /\ o2.len > 0
(* a zero-length squeeze                                                   *)
NoW_ZeroSqueeze == ~\E o \in outs : o.kind = "squeeze" /\ o.len = 0
(* a non-empty message absorbed after CXOF-style re-initialisation        *)
NoW_AbsorbAfterReinit == ~\E e \in AbsPool : Len(e.g.pre) > 1 /\ e.g.msg # << >>
(* a non-initial held context extended in two different ways (branching) *)
NoW_Branching ==
    ~\E p, e1, e2 \in AbsPool :
        LET n == Len(p.g.msg) IN
        /\ n > 0 /\ p.g.pre = e1.g.pre /\ p.g.pre = e2.g.pre
        /\ Len(e1.g.msg) > n /\ Len(e2.g.msg) > n
        /\ SubSeq(e1.g.msg, 1, n) = p.g.msg /\ SubSeq(e2.g.msg, 1, n) = p.g.msg
        /\ e1.g.msg[n + 1] # e2.g.msg[n + 1]
(* concurrency: both domains inside library code on the SAME context      *)
NoW_ConcurrentSharedInput ==
    ~\E d1, d2 \in Domains : d1 # d2 /\ ~Idle(d1) /\ ~Idle(d2)
        /\ Reach(cIn[d1]) \cap Reach(cIn[d2]) # {}
        /\ wr[d1] # {} /\ wr[d2] # {}
(* concurrency: a domain working on a context published by the other      *)
(* domain while that domain is itself mid-operation                        *)
NoW_CrossDomainHandoff ==
    ~\E d1, d2 \in Domains : d1 # d2 /\ ~Idle(d1) /\ ~Idle(d2)
        /\ cIn[d1].st[1] = d2 /\ wr[d1] # {} /\ wr[d2] # {}

(* Groups used by the configurations. *)
AllSafety ==
    /\ TypeOK /\ BufferedRange /\ OffsetRange /\ BufferContents
    /\ AbsorbRefinement /\ SqueezeRefinement /\ OutputCorrect
    /\ SqueezeConcat /\ ZeroSqueezeNoop /\ AbsorbLoopInv /\ SqueezeLoopInv
    /\ Persistence /\ NoWriteToPublished /\ NoUserAliasing
    /\ WritesOnlyFresh /\ RaceFree /\ AbsorbPermMinimal

=============================================================================
