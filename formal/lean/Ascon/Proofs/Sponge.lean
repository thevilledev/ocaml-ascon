import Ascon.Model.Sponge
import Ascon.Spec.Hash
import Ascon.Proofs.Permutation
import Ascon.Proofs.Endian
import Ascon.Proofs.Parse

/-!
# `sponge.ml` implements the SP 800-232 64-bit-rate sponge

* `absorb_correct`: an absorbing context stands for a message `m` through
  `AbsRep`. `absorb` on further input `x` gives a context that stands for
  `m ++ x`, for every chunking of the input.
* `finishState_correct`: finalization absorbs `pad(final block)`, so a
  context for `m` finishes into the state after absorbing `paddedBlocks 8 m`.
* `squeeze_correct`: a squeezing context stands for a position `p` in the
  output stream through `SqRep`. `squeeze` of `L` bytes returns stream bytes
  `p … p+L-1` and a context for position `p + L`.

The contexts' invariants `0 ≤ buffered < 8` and `0 ≤ offset < 8` are part of
`AbsRep` and `SqRep`.
-/

namespace Ascon.Spec.Hash

theorem absorb_append (S : State) (A B : List (List Byte)) :
    absorb S (A ++ B) = absorb (absorb S A) B :=
  List.foldl_append

end Ascon.Spec.Hash

namespace Ascon.Model

open Spec (wordLE bytesLE parse pad paddedBlocks)
open Permutation

theorem Bytes.ofList_split (x : List Byte) (a : Nat) :
    Bytes.ofList x = Bytes.ofList (x.take a) ++ Bytes.ofList (x.drop a) := by
  rw [← Bytes.ofList_append, List.take_append_drop]

theorem Bytes.ofList_split3 (x : List Byte) (a b : Nat) :
    Bytes.ofList x =
      Bytes.ofList (x.take a) ++ Bytes.ofList ((x.drop a).take b) ++
        Bytes.ofList (x.drop (a + b)) := by
  rw [← Bytes.ofList_append, ← Bytes.ofList_append, List.append_assoc, ← List.drop_drop,
    List.take_append_drop, List.take_append_drop]

theorem Bytes.blit_ok (src dst : List Byte) (so d len : Nat) (hs : so + len ≤ src.length)
    (hd : d + len ≤ dst.length) :
    Bytes.blit (Bytes.ofList src) so (Bytes.ofList dst) d len =
      .ok (Bytes.ofList (dst.take d ++ (src.drop so).take len ++ dst.drop (d + len))) := by
  unfold Bytes.blit
  have hv : Bytes.validRange (Bytes.ofList src) so len ∧ Bytes.validRange (Bytes.ofList dst) d len := by
    simp only [Bytes.validRange, Bytes.length_eq, Bytes.length_ofList]; omega
  rw [ite_eq_left hv]
  simp only [Int.toNat_natCast, show ((d : Int) + (len : Int)).toNat = d + len by omega,
    Bytes.ofList_append, Bytes.ofList_take, Bytes.ofList_drop]
  rfl

theorem Bytes.make_ok (n : Nat) (h : (n : Int) ≤ maxStringLength) (c : Byte) :
    Bytes.make n c = .ok (Bytes.ofList (List.replicate n c)) := by
  simp only [Bytes.make, show ¬ ((n : Int) < 0 ∨ (n : Int) > maxStringLength) by omega,
    ↓reduceIte, Int.toNat_natCast, Bytes.ofList, List.map_replicate]; rfl

namespace Sponge

theorem absorbBlock_ok (st : State) (pre post : List (Option Byte)) (B : List Byte)
    (hB : B.length = 8) :
    absorbBlock st (pre ++ Bytes.ofList B ++ post) pre.length =
      .ok (State.ofSpec (Spec.Hash.absorbBlock st.toSpec B)) := by
  simp only [absorbBlock, Endian.load64Le_ok pre post B hB, bind, Except.bind, p12_correct]
  rfl

/-- The `while` loop of `absorb` absorbs every full block of the rest of the input. -/
theorem absorbLoop_ok (x : List Byte) (st : State) (off : Nat) (hoff : off ≤ x.length) :
    absorbLoop st (Bytes.ofList x) off =
      .ok (State.ofSpec (Spec.Hash.absorb st.toSpec (parse 8 (x.drop off)).1),
        ((off + 8 * (parse 8 (x.drop off)).1.length : Nat) : Int)) := by
  induction h : x.length - off using Nat.strongRecOn generalizing st off with
  | ind n ih =>
    rw [absorbLoop]
    by_cases hlong : 8 ≤ x.length - off
    · have hc : Bytes.length (Bytes.ofList x) - (off : Int) ≥ 8 := by simp; omega
      rw [ite_eq_left hc]
      rw [Bytes.ofList_split3 x off 8]
      have hpre : List.length (Bytes.ofList (x.take off)) = off := by simp; omega
      have hB : ((x.drop off).take 8).length = 8 := by simp; omega
      have hab := absorbBlock_ok st (Bytes.ofList (x.take off)) (Bytes.ofList (x.drop (off + 8)))
        ((x.drop off).take 8) hB
      rw [hpre] at hab
      simp only [hab, bind, Except.bind]
      rw [← Bytes.ofList_split3 x off 8]
      have := ih (x.length - (off + 8)) (by omega)
        (State.ofSpec (Spec.Hash.absorbBlock st.toSpec ((x.drop off).take 8))) (off + 8)
        (by omega) rfl
      rw [show ((off : Int) + 8) = ((off + 8 : Nat) : Int) by push_cast; rfl, this]
      rw [Spec.parse_long (x.drop off) (by decide) (by simp; omega)]
      simp only [List.drop_drop, Spec.Hash.absorb, List.foldl_cons, State.toSpec_ofSpec,
        List.length_cons]
      congr 2
      all_goals omega
    · have hc : ¬ (Bytes.length (Bytes.ofList x) - (off : Int) ≥ 8) := by simp; omega
      rw [ite_eq_right hc, Spec.parse_short (x.drop off) (by simp; omega)]
      rfl

@[simp] theorem State.copy_eq (s : State) : State.copy s = s := rfl


/-- An absorbing context stands for the message `m` absorbed on top of `S0`. -/
structure AbsRep (S0 : Spec.State) (m : List Byte) (ctx : Absorbing) : Prop where
  state : ctx.state.toSpec = Spec.Hash.absorb S0 (parse 8 m).1
  buffered : ctx.buffered = ((parse 8 m).2.length : Int)
  buffer : ∃ buf : List Byte, ctx.buffer = Bytes.ofList buf ∧ buf.length = 8 ∧
    buf.take (parse 8 m).2.length = (parse 8 m).2

theorem keepRemainder_ok (x : List Byte) (off : Nat) (hoff : off ≤ x.length) (buf : List Byte)
    (hbuf : buf.length = 8) (hrem : x.length - off < 8) (bd : Int) :
    keepRemainder (Bytes.ofList x) off (Bytes.ofList buf) bd =
      .ok (if x.length - off ≠ 0 then
          (Bytes.ofList (x.drop off ++ buf.drop (x.length - off)), ((x.length - off : Nat) : Int))
        else (Bytes.ofList buf, bd)) := by
  unfold keepRemainder
  by_cases h0 : x.length - off = 0
  · have : ¬ (Bytes.length (Bytes.ofList x) - (off : Int) ≠ 0) := by simp; omega
    simp only [this, ↓reduceIte, h0, ne_eq, not_true_eq_false]; rfl
  · have : Bytes.length (Bytes.ofList x) - (off : Int) ≠ 0 := by simp; omega
    rw [ite_eq_left this, ite_eq_left h0]
    rw [show Bytes.length (Bytes.ofList x) - (off : Int) = ((x.length - off : Nat) : Int) by
      simp; omega]
    rw [show ((0 : Int)) = ((0 : Nat) : Int) from rfl,
      Bytes.blit_ok x buf off 0 (x.length - off) (by omega) (by omega)]
    simp only [List.take_zero, List.nil_append, Nat.zero_add, bind, Except.bind, pure,
      Except.pure]
    rw [List.take_of_length_le (by simp)]

theorem natCast_zero_int : ((0 : Nat) : Int) = 0 := rfl

/-- `fillPending` when the input completes the pending block. -/
theorem fillPending_full (st : State) (buf r x : List Byte) (hbuf : buf.length = 8)
    (hr : buf.take r.length = r) (hr0 : 0 < r.length) (hr8 : r.length < 8)
    (hfull : 8 ≤ r.length + x.length) :
    fillPending st (Bytes.ofList buf) (r.length : Int) (Bytes.ofList x) =
      .ok (State.ofSpec (Spec.Hash.absorbBlock st.toSpec (r ++ x.take (8 - r.length))),
        Bytes.ofList (r ++ x.take (8 - r.length)), 0, ((8 - r.length : Nat) : Int)) := by
  have hB : (r ++ x.take (8 - r.length)).length = 8 := by simp; omega
  have hblit := Bytes.blit_ok x buf 0 r.length (8 - r.length) (by omega) (by omega)
  rw [natCast_zero_int] at hblit
  have hbuf' : buf.take r.length ++ (x.drop 0).take (8 - r.length) ++
      buf.drop (r.length + (8 - r.length)) = r ++ x.take (8 - r.length) := by
    rw [hr, List.drop_zero, show r.length + (8 - r.length) = 8 by omega,
      List.drop_of_length_le (by omega), List.append_nil]
  have hab := absorbBlock_ok st [] [] (r ++ x.take (8 - r.length)) hB
  simp only [List.nil_append, List.append_nil, List.length_nil] at hab
  rw [natCast_zero_int] at hab
  unfold fillPending
  rw [ite_eq_left (by omega : (r.length : Int) ≠ 0),
    show min (8 - (r.length : Int)) (Bytes.length (Bytes.ofList x)) =
      ((8 - r.length : Nat) : Int) by simp; omega]
  simp only [hblit, bind, Except.bind, hbuf']
  rw [ite_eq_left (by omega : (r.length : Int) + ((8 - r.length : Nat) : Int) = 8), hab]
  rfl

/-- `fillPending` when the input fits in the pending block. -/
theorem fillPending_partial (st : State) (buf r x : List Byte) (hbuf : buf.length = 8)
    (hr : buf.take r.length = r) (hr0 : 0 < r.length) (hfit : r.length + x.length < 8) :
    fillPending st (Bytes.ofList buf) (r.length : Int) (Bytes.ofList x) =
      .ok (st, Bytes.ofList (r ++ x ++ buf.drop (r.length + x.length)),
        ((r.length + x.length : Nat) : Int), (x.length : Int)) := by
  have hblit := Bytes.blit_ok x buf 0 r.length x.length (by omega) (by omega)
  rw [natCast_zero_int] at hblit
  unfold fillPending
  rw [ite_eq_left (by omega : (r.length : Int) ≠ 0),
    show min (8 - (r.length : Int)) (Bytes.length (Bytes.ofList x)) = (x.length : Int) by
      simp; omega]
  simp only [hblit, bind, Except.bind, hr, List.drop_zero, List.take_length]
  rw [ite_eq_right (by omega : ¬ ((r.length : Int) + (x.length : Int) = 8))]
  rfl

/-- `absorb` extends the represented message by the input, for any chunking. -/
theorem absorb_correct (S0 : Spec.State) (m x : List Byte) (ctx : Absorbing)
    (h : AbsRep S0 m ctx) :
    ∃ ctx', absorb ctx (Bytes.ofList x) = .ok ctx' ∧ AbsRep S0 (m ++ x) ctx' := by
  obtain ⟨hst, hbd, buf, hbuf, hlen, htake⟩ := h
  have hr8 : (parse 8 m).2.length < 8 := Spec.parse_rem_length m (by decide)
  have happ := Spec.parse_append (r := 8) m x (by decide)
  generalize (parse 8 m).1 = F at hst happ
  generalize (parse 8 m).2 = r at hbd htake hr8 happ
  obtain ⟨st, buffer, bd⟩ := ctx
  simp only at hst hbd hbuf
  subst hbd hbuf
  by_cases hr0 : r.length = 0
  · -- No pending bytes.
    obtain rfl : r = [] := List.eq_nil_of_length_eq_zero hr0
    have hfill : fillPending st (Bytes.ofList buf) (([] : List Byte).length : Int)
        (Bytes.ofList x) = .ok (st, Bytes.ofList buf, 0, 0) := by
      simp [fillPending]; rfl
    have hloop := absorbLoop_ok x st 0 (Nat.zero_le _)
    have hn := Spec.parse_rem_eq_drop (r := 8) x (by decide)
    have hj := Spec.parse_join (r := 8) x (by decide)
    have hfl := Spec.parse_flatten_length (r := 8) x (by decide)
    have hrl := Spec.parse_rem_length (r := 8) x (by decide)
    have hxlen : x.length = 8 * (parse 8 x).1.length + (parse 8 x).2.length := by
      rw [← hfl, ← List.length_append, hj]
    simp only [List.drop_zero, Nat.zero_add] at hloop
    rw [show ((0 : Nat) : Int) = 0 from rfl] at hloop
    have hkeep := keepRemainder_ok x (8 * (parse 8 x).1.length) (by omega) buf hlen
      (by omega) (0 : Int)
    simp only [absorb, State.copy_eq, Bytes.copy, hfill, hloop, bind, Except.bind]
    rw [hkeep]
    refine ⟨_, rfl, ?_⟩
    simp only [List.nil_append] at happ
    by_cases hz : x.length - 8 * (parse 8 x).1.length ≠ 0
    · rw [ite_eq_left hz]
      refine ⟨?_, ?_, ?_⟩ <;> simp only [happ]
      · rw [State.toSpec_ofSpec, hst, Spec.Hash.absorb_append]
      · rw [hn]; simp
      · refine ⟨_, rfl, by simp [hlen] <;> omega, ?_⟩
        rw [hn, List.take_append_of_le_length (by simp <;> omega)]
        simp only [List.length_drop]
        exact List.take_of_length_le (by simp)
    · rw [ite_eq_right hz]
      have hz' : (parse 8 x).2.length = 0 := by omega
      refine ⟨?_, ?_, ?_⟩ <;> simp only [happ]
      · rw [State.toSpec_ofSpec, hst, Spec.Hash.absorb_append]
      · simp [hz']
      · exact ⟨buf, rfl, hlen, by simp [List.eq_nil_of_length_eq_zero hz']⟩
  · have hrpos : 0 < r.length := Nat.pos_of_ne_zero hr0
    by_cases hfull : 8 ≤ r.length + x.length
    · -- The input completes the pending block.
      have hfill := fillPending_full st buf r x hlen htake hrpos hr8 hfull
      have hB : (r ++ x.take (8 - r.length)).length = 8 := by simp; omega
      have hloop := absorbLoop_ok x
        (State.ofSpec (Spec.Hash.absorbBlock st.toSpec (r ++ x.take (8 - r.length))))
        (8 - r.length) (by omega)
      have hsplit : r ++ x = (r ++ x.take (8 - r.length)) ++ x.drop (8 - r.length) := by
        rw [List.append_assoc, List.take_append_drop]
      rw [hsplit, Spec.parse_block_append _ _ (by decide) hB] at happ
      generalize hy : x.drop (8 - r.length) = y at hloop happ
      have hn := Spec.parse_rem_eq_drop (r := 8) y (by decide)
      have hj := Spec.parse_join (r := 8) y (by decide)
      have hfl := Spec.parse_flatten_length (r := 8) y (by decide)
      have hrl := Spec.parse_rem_length (r := 8) y (by decide)
      have hylen : y.length = x.length - (8 - r.length) := by rw [← hy]; simp
      have hyl : y.length = 8 * (parse 8 y).1.length + (parse 8 y).2.length := by
        rw [← hfl, ← List.length_append, hj]
      have hkeep := keepRemainder_ok x ((8 - r.length) + 8 * (parse 8 y).1.length) (by omega)
        (r ++ x.take (8 - r.length)) hB (by omega) (0 : Int)
      simp only [absorb, State.copy_eq, Bytes.copy, hfill, hloop, bind, Except.bind]
      rw [hkeep]
      refine ⟨_, rfl, ?_⟩
      have hrem : (parse 8 y).2 = x.drop (8 - r.length + 8 * (parse 8 y).1.length) := by
        rw [hn, ← hy, List.drop_drop]
      by_cases hz : x.length - (8 - r.length + 8 * (parse 8 y).1.length) ≠ 0
      · rw [ite_eq_left hz]
        refine ⟨?_, ?_, ?_⟩ <;> simp only [happ]
        · simp only [State.toSpec_ofSpec, hst, Spec.Hash.absorb, List.foldl_append,
            List.foldl_cons]
        · rw [hrem]; simp
        · refine ⟨_, rfl, by simp <;> omega, ?_⟩
          rw [hrem, List.take_append_of_le_length (by simp <;> omega)]
          simp only [List.length_drop]
          exact List.take_of_length_le (by simp)
      · rw [ite_eq_right hz]
        have hz' : (parse 8 y).2.length = 0 := by omega
        refine ⟨?_, ?_, ?_⟩ <;> simp only [happ]
        · simp only [State.toSpec_ofSpec, hst, Spec.Hash.absorb, List.foldl_append,
            List.foldl_cons]
        · simp [hz']
        · exact ⟨_, rfl, hB, by simp [List.eq_nil_of_length_eq_zero hz']⟩
    · -- The input fits in the pending block.
      have hfit : r.length + x.length < 8 := by omega
      have hfill := fillPending_partial st buf r x hlen htake hrpos hfit
      have hloop := absorbLoop_ok x st x.length (Nat.le_refl _)
      simp only [List.drop_length, Spec.parse_nil, List.length_nil, Nat.mul_zero,
        Nat.add_zero] at hloop
      have hbl : (r ++ x ++ buf.drop (r.length + x.length)).length = 8 := by simp; omega
      have hkeep := keepRemainder_ok x x.length (Nat.le_refl _) _ hbl (by omega)
        ((r.length + x.length : Nat) : Int)
      simp only [Nat.sub_self, ne_eq, not_true_eq_false, ↓reduceIte] at hkeep
      simp only [absorb, State.copy_eq, Bytes.copy, hfill, hloop, bind, Except.bind]
      rw [hkeep]
      refine ⟨_, rfl, ?_⟩
      rw [Spec.parse_short (r ++ x) (by simp; omega)] at happ
      refine ⟨?_, ?_, ?_⟩ <;> simp only [happ]
      · simp only [State.toSpec_ofSpec, hst, Spec.Hash.absorb,
          List.foldl_nil, List.append_nil]
      · simp
      · refine ⟨_, rfl, hbl, ?_⟩
        rw [List.take_append_of_le_length (by simp)]
        exact List.take_of_length_le (by simp)

theorem ofState_correct (st : State) :
    ∃ ctx, ofState st = .ok ctx ∧ AbsRep st.toSpec [] ctx := by
  have hmk : Bytes.make 8 0 = .ok (Bytes.ofList (List.replicate 8 0)) :=
    Bytes.make_ok 8 (by decide) 0
  refine ⟨⟨st, Bytes.ofList (List.replicate 8 0), 0⟩, ?_, ?_⟩
  · simp only [ofState, bind, Except.bind, State.copy_eq, hmk]; rfl
  · refine ⟨?_, ?_, ?_⟩ <;> simp only [Spec.parse_nil]
    · rfl
    · rfl
    · exact ⟨List.replicate 8 0, rfl, by simp, by simp⟩

theorem init_correct (iv : Word) :
    ∃ ctx, init iv = .ok ctx ∧ AbsRep (Spec.Hash.initial iv) [] ctx := by
  obtain ⟨ctx, hctx, hrep⟩ := ofState_correct (State.ofSpec (Spec.Hash.initial iv))
  refine ⟨ctx, ?_, ?_⟩
  · simp only [init, p12_correct, bind, Except.bind]
    exact hctx
  · simpa using hrep

/-- Finalization absorbs `pad(final block)`: the state after all padded blocks. -/
theorem finishState_correct (S0 : Spec.State) (m : List Byte) (ctx : Absorbing)
    (h : AbsRep S0 m ctx) :
    finishState ctx = .ok (State.ofSpec (Spec.Hash.absorb S0 (paddedBlocks 8 m))) := by
  obtain ⟨hst, hbd, buf, hbuf, hlen, htake⟩ := h
  have hr8 : (parse 8 m).2.length < 8 := Spec.parse_rem_length m (by decide)
  unfold paddedBlocks
  generalize (parse 8 m).1 = F at hst ⊢
  generalize (parse 8 m).2 = r at hbd htake hr8 ⊢
  obtain ⟨st, buffer, bd⟩ := ctx
  simp only at hst hbd hbuf
  subst hbd hbuf
  have hsplit : Bytes.ofList buf = [] ++ Bytes.ofList r ++ Bytes.ofList (buf.drop r.length) := by
    have e : buf = buf.take r.length ++ buf.drop r.length := (List.take_append_drop _ _).symm
    rw [htake] at e
    rw [List.nil_append, ← Bytes.ofList_append, ← e]
  have hload := Endian.loadPartialLe_ok [] (Bytes.ofList (buf.drop r.length)) r (by omega)
  rw [← hsplit] at hload
  simp only [List.length_nil, natCast_zero_int] at hload
  simp only [finishState, State.copy_eq, hload, Endian.padding_ok r.length hr8, bind,
    Except.bind, p12_correct]
  simp only [Spec.Hash.absorb] at hst
  simp only [Spec.Hash.absorb, List.foldl_append, List.foldl_cons, List.foldl_nil, ← hst,
    Spec.Hash.absorbBlock, Spec.wordLE_pad8 r hr8]
  simp only [State.toSpec, BitVec.xor_assoc]

theorem finish_correct (S0 : Spec.State) (m : List Byte) (ctx : Absorbing)
    (h : AbsRep S0 m ctx) :
    finish ctx = .ok (Squeezing.mk (State.ofSpec (Spec.Hash.absorb S0 (paddedBlocks 8 m))) 0) := by
  simp only [finish, finishState_correct S0 m ctx h, bind, Except.bind, squeezingOfState,
    State.copy_eq]; rfl

end Sponge
end Ascon.Model

namespace Ascon.Spec.Hash

/-- The state from which output block `k` is read: `k` further permutations. -/
def blockState (S : State) : Nat → State
  | 0 => S
  | k + 1 => blockState (asconP 12 S) k

theorem blockState_succ (S : State) (k : Nat) :
    blockState S (k + 1) = asconP 12 (blockState S k) := by
  induction k generalizing S with
  | zero => rfl
  | succ k ih => rw [blockState, ih (asconP 12 S), blockState]

/-- Byte `q` of the output stream that starts in state `S`. -/
def streamByte (S : State) (q : Nat) : Byte := (bytesLE (blockState S (q / 8)).s0).getD (q % 8) 0

theorem streamByte_shift (S : State) (q : Nat) :
    streamByte (asconP 12 S) q = streamByte S (q + 8) := by
  simp only [streamByte, show (q + 8) / 8 = q / 8 + 1 by omega, Nat.add_mod_right, blockState]

theorem bytesLE_getD (w : Word) (i : Nat) (h : i < 8) :
    (bytesLE w).getD i 0 = (bytesLE w)[i]'(by simp [bytesLE_length]; omega) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem]; rfl

/-- `squeeze S L` is the first `L` bytes of the output stream. -/
theorem squeeze_eq_stream (S : State) (L : Nat) :
    squeeze S L = (List.range L).map (streamByte S) := by
  induction L using Nat.strongRecOn generalizing S with
  | ind L ih =>
    rw [squeeze]
    by_cases h : L ≤ 8
    · rw [ite_eq_left h]
      apply List.ext_getElem (by simp [bytesLE_length]; omega)
      intro i h1 h2
      have hi : i < 8 := by simp at h2; omega
      simp only [List.getElem_take, List.getElem_map, List.getElem_range, streamByte,
        show i / 8 = 0 by omega, show i % 8 = i by omega, blockState, bytesLE_getD _ i hi]
    · rw [ite_eq_right h, ih (L - 8) (by omega) (asconP 12 S)]
      have hL : L = 8 + (L - 8) := by omega
      conv => rhs; rw [hL]
      rw [List.range_add, List.map_append, List.map_map]
      refine congr (congrArg HAppend.hAppend ?_) ?_
      · apply List.ext_getElem (by simp [bytesLE_length])
        intro i h1 h2
        have hi : i < 8 := by simp at h2; omega
        simp only [List.getElem_map, List.getElem_range, streamByte,
          show i / 8 = 0 by omega, show i % 8 = i by omega, blockState, bytesLE_getD _ i hi]
      · apply List.map_congr_left
        intro q _
        simp only [Function.comp, streamByte_shift, Nat.add_comm q 8]

/-- Stream bytes `p … p+n-1`. -/
def outBytes (S : State) (p n : Nat) : List Byte := (List.range n).map fun k => streamByte S (p + k)

theorem outBytes_succ (S : State) (p n : Nat) :
    outBytes S p (n + 1) = outBytes S p n ++ [streamByte S (p + n)] := by
  simp [outBytes, List.range_succ]

theorem outBytes_length (S : State) (p n : Nat) : (outBytes S p n).length = n := by
  simp [outBytes]

end Ascon.Spec.Hash

namespace Ascon.Model
open Spec (wordLE bytesLE parse pad paddedBlocks)
open Spec.Hash (blockState streamByte outBytes)
open Permutation
namespace Sponge

/-- A squeezing context stands for position `p` of the output stream from `S`. -/
structure SqRep (S : Spec.State) (p : Nat) (ctx : Squeezing) : Prop where
  state : ctx.state.toSpec = blockState S (p / 8)
  offset : ctx.offset = ((p % 8 : Nat) : Int)

theorem Bytes.create_ok (n : Nat) (h : (n : Int) ≤ maxStringLength) :
    Bytes.create n = .ok (List.replicate n none) := by
  simp only [Bytes.create, show ¬ ((n : Int) < 0 ∨ (n : Int) > maxStringLength) by omega,
    ↓reduceIte, Int.toNat_natCast]; rfl

theorem set_first_none (A : List Byte) (n : Nat) (b : Byte) :
    (Bytes.ofList A ++ List.replicate (n + 1) none).set A.length (some b) =
      Bytes.ofList (A ++ [b]) ++ List.replicate n none := by
  rw [List.set_append_right _ _ (by simp)]
  simp [Bytes.ofList, List.replicate_succ]

/-- One pass of the `for` loop in `squeeze` emits `take` consecutive stream bytes. -/
theorem squeezeInner_ok (S : Spec.State) (p w L t : Nat) (st : State)
    (hst : st.toSpec = blockState S ((p + w) / 8)) (ht : (p + w) % 8 + t ≤ 8)
    (hw : w + t ≤ L) :
    forUp 0 ((t : Int) - 1) (Bytes.ofList (outBytes S p w) ++ List.replicate (L - w) none)
        (squeezeByte st.x0 (((p + w) % 8 : Nat) : Int) w) =
      .ok (Bytes.ofList (outBytes S p (w + t)) ++ List.replicate (L - (w + t)) none) := by
  obtain ⟨out, hout, i, hP⟩ : ∃ out, forUp 0 ((t : Int) - 1)
      (Bytes.ofList (outBytes S p w) ++ List.replicate (L - w) none)
      (squeezeByte st.x0 (((p + w) % 8 : Nat) : Int) w) = .ok out ∧
      ∃ i : Nat, (i : Int) = (t : Int) - 1 + 1 ∧
        out = Bytes.ofList (outBytes S p (w + i)) ++ List.replicate (L - (w + i)) none := by
    obtain ⟨out, hout, hp⟩ := forUp_invariant 0 ((t : Int) - 1) (by omega)
      (Bytes.ofList (outBytes S p w) ++ List.replicate (L - w) none)
      (squeezeByte st.x0 (((p + w) % 8 : Nat) : Int) w)
      (fun i out => ∃ k : Nat, (k : Int) = i ∧ k ≤ t ∧
        out = Bytes.ofList (outBytes S p (w + k)) ++ List.replicate (L - (w + k)) none)
      ⟨0, rfl, by omega, by simp⟩ (by
        intro i out hlo hhi ⟨k, hk, hkt, hout⟩
        subst hk
        have hk8 : (p + w) % 8 + k < 8 := by omega
        refine ⟨_, ?_, ⟨k + 1, by push_cast; rfl, by omega, rfl⟩⟩
        simp only [squeezeByte]
        rw [show 8 * ((((p + w) % 8 : Nat) : Int) + (k : Int)) =
          ((8 * ((p + w) % 8 + k) : Nat) : Int) by omega,
          Int64.shiftRightLogical_ok _ _ (by omega)]
        simp only [bind, Except.bind, chr_low_byte]
        rw [byte_of_word st.x0 ((p + w) % 8 + k) hk8, hout,
          show (w : Int) + (k : Int) = (((outBytes S p (w + k)).length : Nat) : Int) by
            rw [Spec.Hash.outBytes_length]; push_cast; rfl,
          Bytes.unsafeSet_ok _ _ (by simp [Bytes.ofList, Spec.Hash.outBytes_length]; omega),
          show L - (w + k) = (L - (w + (k + 1))) + 1 by omega, set_first_none,
          show w + (k + 1) = (w + k) + 1 by omega, Spec.Hash.outBytes_succ]
        congr 4
        simp only [streamByte, show (p + (w + k)) / 8 = (p + w) / 8 by omega,
          show (p + (w + k)) % 8 = (p + w) % 8 + k by omega, ← hst,
          Spec.Hash.bytesLE_getD _ _ hk8]
        rfl)
    exact ⟨out, hout, t, by omega, by
      obtain ⟨k, hk, _, ho⟩ := hp
      rw [ho, show k = t by omega]⟩
  rw [hout, hP.2, show i = t by omega]

/-- The `while` loop of `squeeze`: it terminates within its budget and emits
stream bytes `p + w … p + L - 1`. -/
theorem squeezeLoop_ok (S : Spec.State) (p L : Nat) :
    ∀ (fuel w : Nat) (st : State), w ≤ L → L - w < fuel →
      st.toSpec = blockState S ((p + w) / 8) →
      squeezeLoop fuel st (((p + w) % 8 : Nat) : Int)
          (Bytes.ofList (outBytes S p w) ++ List.replicate (L - w) none) w L =
        .ok (State.ofSpec (blockState S ((p + L) / 8)), (((p + L) % 8 : Nat) : Int),
          Bytes.ofList (outBytes S p L), (L : Int)) := by
  intro fuel
  induction fuel with
  | zero => intro w st _ h; omega
  | succ fuel ih =>
    intro w st hw hf hst
    rw [squeezeLoop]
    by_cases hlt : w < L
    · rw [ite_eq_left (by omega : (w : Int) < L)]
      have ht : min (8 - (((p + w) % 8 : Nat) : Int)) ((L : Int) - (w : Int)) =
          ((min (8 - (p + w) % 8) (L - w) : Nat) : Int) := by omega
      generalize htk : min (8 - (p + w) % 8) (L - w) = t at ht
      have htpos : 0 < t := by omega
      simp only [ht, squeezeInner_ok S p w L t st hst (by omega) (by omega), bind,
        Except.bind]
      by_cases h8 : (p + w) % 8 + t = 8
      · rw [ite_eq_left (by omega : (((p + w) % 8 : Nat) : Int) + (t : Int) = 8)]
        simp only [p12_correct, pure, Except.pure]
        have := ih (w + t) (State.ofSpec (Spec.asconP 12 st.toSpec)) (by omega) (by omega)
          (by rw [State.toSpec_ofSpec, hst, show (p + (w + t)) / 8 = (p + w) / 8 + 1 by omega,
                Spec.Hash.blockState_succ])
        rw [show (((p + (w + t)) % 8 : Nat) : Int) = 0 by omega,
          show ((w + t : Nat) : Int) = (w : Int) + (t : Int) by push_cast; rfl] at this
        exact this
      · rw [ite_eq_right (by omega : ¬ ((((p + w) % 8 : Nat) : Int) + (t : Int) = 8))]
        simp only [pure, Except.pure]
        have := ih (w + t) st (by omega) (by omega)
          (by rw [hst, show (p + (w + t)) / 8 = (p + w) / 8 by omega])
        rw [show (((p + (w + t)) % 8 : Nat) : Int) = (((p + w) % 8 : Nat) : Int) + (t : Int) by
            omega,
          show ((w + t : Nat) : Int) = (w : Int) + (t : Int) by push_cast; rfl] at this
        exact this
    · have hwL : w = L := by omega
      subst hwL
      rw [ite_eq_right (by omega)]
      simp only [Nat.sub_self, List.replicate_zero, List.append_nil, ← hst,
        State.ofSpec_toSpec]
      rfl

/-- `squeeze` returns the next `L` stream bytes and advances the position by `L`. -/
theorem squeeze_correct (S : Spec.State) (p : Nat) (ctx : Squeezing) (h : SqRep S p ctx)
    (L : Nat) (hL : (L : Int) ≤ maxStringLength) :
    squeeze ctx L =
      .ok (⟨State.ofSpec (blockState S ((p + L) / 8)), (((p + L) % 8 : Nat) : Int)⟩,
        Bytes.ofList (outBytes S p L)) ∧
    SqRep S (p + L) ⟨State.ofSpec (blockState S ((p + L) / 8)), (((p + L) % 8 : Nat) : Int)⟩ := by
  obtain ⟨hst, hoff⟩ := h
  refine ⟨?_, ⟨by simp, rfl⟩⟩
  have hloop := squeezeLoop_ok S p L (L + 1) 0 ctx.state (Nat.zero_le _) (by omega)
    (by rw [hst, Nat.add_zero])
  simp only [Nat.add_zero, Nat.sub_zero, show outBytes S p 0 = [] from rfl,
    Bytes.ofList, List.map_nil, List.nil_append, natCast_zero_int] at hloop
  unfold squeeze
  rw [ite_eq_right (by omega)]
  simp only [State.copy_eq, hoff, Bytes.create_ok L hL, bind, Except.bind,
    Int.toNat_natCast]
  rw [hloop]
  rfl

end Sponge
end Ascon.Model
