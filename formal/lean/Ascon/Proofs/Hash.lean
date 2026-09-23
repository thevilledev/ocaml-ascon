import Ascon.Model.Hash
import Ascon.Proofs.Sponge

/-!
# `Hash256`, `Xof128` and `Cxof128` implement SP 800-232 Algorithms 5–7

For every input and every way of splitting it into `feed` / `absorb` calls,
the modelled OCaml code returns exactly the SP 800-232 output, raises no
exception, and returns every output byte initialized. Successive incremental
squeezes return consecutive segments of the specified output stream. Length
and customization errors are returned exactly in the documented cases.
-/

namespace Ascon.Model

open Spec.Hash (blockState streamByte outBytes)
open Sponge (AbsRep SqRep)

/-- Absorbing a list of chunks one call at a time. -/
def absorbAll (ctx : Sponge.Absorbing) : List (List Byte) → M Sponge.Absorbing
  | [] => pure ctx
  | c :: cs => do absorbAll (← Sponge.absorb ctx (Bytes.ofList c)) cs

theorem absorbAll_correct (S0 : Spec.State) (m : List Byte) (ctx : Sponge.Absorbing)
    (h : AbsRep S0 m ctx) (cs : List (List Byte)) :
    ∃ ctx', absorbAll ctx cs = .ok ctx' ∧ AbsRep S0 (m ++ cs.flatten) ctx' := by
  induction cs generalizing m ctx with
  | nil => exact ⟨ctx, rfl, by simpa using h⟩
  | cons c cs ih =>
    obtain ⟨ctx1, h1, hr1⟩ := Sponge.absorb_correct S0 m c ctx h
    obtain ⟨ctx2, h2, hr2⟩ := ih (m ++ c) ctx1 hr1
    refine ⟨ctx2, ?_, by simpa [List.append_assoc] using hr2⟩
    simp only [absorbAll, h1, bind, Except.bind]
    exact h2

theorem outBytes_zero_eq_squeeze (S : Spec.State) (L : Nat) :
    outBytes S 0 L = Spec.Hash.squeeze S L := by
  rw [Spec.Hash.squeeze_eq_stream]; simp [outBytes]

/-- Consecutive squeezes concatenate. -/
theorem outBytes_add (S : Spec.State) (p a b : Nat) :
    outBytes S p (a + b) = outBytes S p a ++ outBytes S (p + a) b := by
  simp only [outBytes, List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro k _
  simp [Function.comp, Nat.add_assoc]

/-- Finishing an absorbing context gives a squeezing context at stream position 0. -/
theorem finish_rep (S0 : Spec.State) (m : List Byte) (ctx : Sponge.Absorbing)
    (h : AbsRep S0 m ctx) :
    ∃ sq, Sponge.finish ctx = .ok sq ∧ SqRep (Spec.Hash.absorb S0 (Spec.paddedBlocks 8 m)) 0 sq :=
  ⟨_, Sponge.finish_correct S0 m ctx h, ⟨by simp [blockState], rfl⟩⟩

namespace Hash256

/-- The digest of an incremental context is the Ascon-Hash256 digest of
everything fed into it, for every chunking. -/
theorem get_correct (m : List Byte) (ctx : Sponge.Absorbing)
    (h : AbsRep (Spec.Hash.initial Spec.Hash.hashIV) m ctx) :
    get ctx = .ok (Bytes.ofList (Spec.Hash.hash256 m)) := by
  obtain ⟨sq, hsq, hrep⟩ := finish_rep _ m ctx h
  have := (Sponge.squeeze_correct _ 0 sq hrep 32 (by decide)).1
  simp only [get, hsq, bind, Except.bind, digestSize]
  rw [show (32 : Int) = ((32 : Nat) : Int) from rfl, this]
  simp only [pure, Except.pure, outBytes_zero_eq_squeeze, Spec.Hash.hash256]

theorem init_rep : ∃ ctx, init = .ok ctx ∧ AbsRep (Spec.Hash.initial Spec.Hash.hashIV) [] ctx :=
  Sponge.init_correct _

/-- Incremental hashing with any chunking equals one-shot SP 800-232 hashing. -/
theorem incremental_correct (chunks : List (List Byte)) :
    (do let ctx ← init; let ctx ← absorbAll ctx chunks; get ctx) =
      .ok (Bytes.ofList (Spec.Hash.hash256 chunks.flatten)) := by
  obtain ⟨ctx0, h0, hr0⟩ := init_rep
  obtain ⟨ctx1, h1, hr1⟩ := absorbAll_correct _ [] ctx0 hr0 chunks
  simp only [h0, h1, bind, Except.bind]
  exact get_correct _ ctx1 (by simpa using hr1)

/-- `Hash256.digest` is Ascon-Hash256. -/
theorem digest_correct (M : List Byte) :
    digest (Bytes.ofList M) = .ok (Bytes.ofList (Spec.Hash.hash256 M)) := by
  obtain ⟨ctx0, h0, hr0⟩ := init_rep
  obtain ⟨ctx1, h1, hr1⟩ := Sponge.absorb_correct _ [] M ctx0 hr0
  simp only [digest, feed, h0, h1, bind, Except.bind]
  exact get_correct M ctx1 (by simpa using hr1)

end Hash256

namespace Xof128

theorem init_rep : ∃ ctx, init = .ok ctx ∧ AbsRep (Spec.Hash.initial Spec.Hash.xofIV) [] ctx :=
  Sponge.init_correct _

/-- `Xof128.digest` is Ascon-XOF128 for every valid length, and returns
`Invalid_length` otherwise. -/
theorem digest_correct (M : List Byte) (L : Int) :
    digest (Bytes.ofList M) L =
      .ok (if 0 < L ∧ L ≤ maxStringLength then .ok (Bytes.ofList (Spec.Hash.xof128 M L.toNat))
        else .error .invalidLength) := by
  by_cases hL : 0 < L ∧ L ≤ maxStringLength
  · obtain ⟨ctx0, h0, hr0⟩ := init_rep
    obtain ⟨ctx1, h1, hr1⟩ := Sponge.absorb_correct _ [] M ctx0 hr0
    obtain ⟨sq, hsq, hrep⟩ := finish_rep _ _ ctx1 hr1
    have hsqz := (Sponge.squeeze_correct _ 0 sq hrep L.toNat (by omega)).1
    rw [show ((L.toNat : Nat) : Int) = L by omega] at hsqz
    have hv : validDigestLength L = true := by simp [validDigestLength]; omega
    simp only [digest, hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte, absorb,
      startSqueezing, h0, h1, hsq, hsqz, bind, Except.bind, pure, Except.pure, ite_eq_left hL]
    simp only [outBytes_zero_eq_squeeze, Spec.Hash.xof128, List.nil_append]
  · have hv : validDigestLength L = false := by simp [validDigestLength]; omega
    simp [digest, hv, hL]; rfl

/-- One incremental squeeze returns the next `L` bytes of the XOF output. -/
theorem squeeze_correct (S : Spec.State) (p : Nat) (sq : Sponge.Squeezing) (h : SqRep S p sq)
    (L : Nat) (hL : (L : Int) ≤ maxStringLength) :
    ∃ sq', squeeze sq L = .ok (.ok (sq', Bytes.ofList (outBytes S p L))) ∧ SqRep S (p + L) sq' := by
  obtain ⟨hs, hr⟩ := Sponge.squeeze_correct S p sq h L hL
  refine ⟨_, ?_, hr⟩
  have hv : validLength L = true := by simp [validLength]; omega
  simp only [squeeze, hv, ↓reduceIte, hs, bind, Except.bind, pure, Except.pure]

/-- Squeezing a list of lengths one call at a time. -/
def squeezeAll (sq : Sponge.Squeezing) : List Nat → M (Except InvalidLength (List Bytes))
  | [] => pure (.ok [])
  | L :: Ls => do
    match ← squeeze sq L with
    | .error e => pure (.error e)
    | .ok (sq, out) =>
      match ← squeezeAll sq Ls with
      | .error e => pure (.error e)
      | .ok outs => pure (.ok (out :: outs))

theorem squeezeAll_correct (S : Spec.State) (p : Nat) (sq : Sponge.Squeezing) (h : SqRep S p sq)
    (Ls : List Nat) (hLs : ∀ L ∈ Ls, (L : Int) ≤ maxStringLength) :
    ∃ outs, squeezeAll sq Ls = .ok (.ok outs) ∧ outs.flatten = Bytes.ofList (outBytes S p Ls.sum) := by
  induction Ls generalizing p sq with
  | nil => exact ⟨[], rfl, by simp [outBytes, Bytes.ofList]⟩
  | cons L Ls ih =>
    obtain ⟨sq1, h1, hr1⟩ := squeeze_correct S p sq h L (hLs L (by simp))
    obtain ⟨outs, h2, hflat⟩ := ih (p + L) sq1 hr1 (fun L' hL' => hLs L' (by simp [hL']))
    refine ⟨Bytes.ofList (outBytes S p L) :: outs, ?_, ?_⟩
    · simp only [squeezeAll, h1, h2, bind, Except.bind, pure, Except.pure]
    · simp only [List.flatten_cons, hflat, List.sum_cons, outBytes_add, Bytes.ofList_append]

/-- Incremental XOF: any absorb chunking followed by any sequence of squeeze
lengths produces the one-shot Ascon-XOF128 output of the total length. -/
theorem streaming_correct (chunks : List (List Byte)) (Ls : List Nat)
    (hLs : ∀ L ∈ Ls, (L : Int) ≤ maxStringLength) :
    ∃ outs, (do
        let ctx ← init
        let ctx ← absorbAll ctx chunks
        let sq ← startSqueezing ctx
        squeezeAll sq Ls) = .ok (.ok outs) ∧
      outs.flatten = Bytes.ofList (Spec.Hash.xof128 chunks.flatten Ls.sum) := by
  obtain ⟨ctx0, h0, hr0⟩ := init_rep
  obtain ⟨ctx1, h1, hr1⟩ := absorbAll_correct _ [] ctx0 hr0 chunks
  obtain ⟨sq, hsq, hrep⟩ := finish_rep _ _ ctx1 hr1
  obtain ⟨outs, hall, hflat⟩ := squeezeAll_correct _ 0 sq hrep Ls hLs
  refine ⟨outs, ?_, ?_⟩
  · simp only [h0, h1, startSqueezing, hsq, bind, Except.bind]
    exact hall
  · rw [hflat, outBytes_zero_eq_squeeze]
    simp [Spec.Hash.xof128]

/-- A negative or unrepresentable incremental squeeze length is rejected. -/
theorem squeeze_invalid (sq : Sponge.Squeezing) (L : Int)
    (hL : L < 0 ∨ L > maxStringLength) : squeeze sq L = .ok (.error .invalidLength) := by
  have hv : validLength L = false := by simp [validLength]; omega
  simp [squeeze, hv]; rfl

end Xof128

namespace Cxof128

theorem ofInt_bitLength (n : Nat) :
    Int64.ofInt ((n : Int) * 8) = Spec.wordLE (Spec.bytesLE (BitVec.ofNat 64 (8 * n))) := by
  rw [Spec.wordLE_bytesLE, show (n : Int) * 8 = ((8 * n : Nat) : Int) by push_cast; omega]
  simp only [Int64.ofInt, BitVec.ofInt_natCast]

theorem customizedState_correct (n : Nat) :
    customizedState n = .ok (State.ofSpec (Spec.Hash.absorbBlock
      (Spec.Hash.initial Spec.Hash.cxofIV) (Spec.bytesLE (BitVec.ofNat 64 (8 * n))))) := by
  unfold customizedState
  rw [bind_of_ok (Permutation.p12_correct _)]
  simp only []
  rw [Permutation.p12_correct, ofInt_bitLength]
  have hA : (State.create iv 0 0 0 0).toSpec = ⟨Spec.Hash.cxofIV, 0, 0, 0, 0⟩ := rfl
  rw [hA]
  unfold Spec.Hash.absorbBlock Spec.Hash.initial
  -- Generalizing the permuted state keeps the kernel from evaluating it.
  generalize Spec.asconP 12 ⟨Spec.Hash.cxofIV, 0, 0, 0, 0⟩ = T
  rfl

/-- For customization strings of at most 256 bytes, `init` absorbs `Z₀` and
`pad(Z)` and returns an empty absorbing context on top of that state. -/
theorem init_correct (Z : List Byte) (hZ : Z.length ≤ 256) :
    ∃ ctx, init (Bytes.ofList Z) = .ok (.ok ctx) ∧
      AbsRep (Spec.Hash.absorb (Spec.Hash.initial Spec.Hash.cxofIV)
        ([Spec.bytesLE (BitVec.ofNat 64 (8 * Z.length))] ++ Spec.paddedBlocks 8 Z)) [] ctx := by
  let S1 : Spec.State := Spec.Hash.absorbBlock (Spec.Hash.initial Spec.Hash.cxofIV)
    (Spec.bytesLE (BitVec.ofNat 64 (8 * Z.length)))
  obtain ⟨c0, hc0, hr0⟩ := Sponge.ofState_correct (State.ofSpec S1)
  obtain ⟨c1, hc1, hr1⟩ := Sponge.absorb_correct _ [] Z c0 hr0
  have hfs := Sponge.finishState_correct _ _ c1 hr1
  obtain ⟨c2, hc2, hr2⟩ := Sponge.ofState_correct
    (State.ofSpec (Spec.Hash.absorb (State.ofSpec S1).toSpec (Spec.paddedBlocks 8 ([] ++ Z))))
  refine ⟨c2, ?_, ?_⟩
  · have hlen : ¬ (Bytes.length (Bytes.ofList Z) > 256) := by simp; omega
    have hcs := customizedState_correct Z.length
    rw [show ((Z.length : Nat) : Int) = Bytes.length (Bytes.ofList Z) by simp] at hcs
    simp only [init, hlen, ↓reduceIte, hcs, bind, Except.bind]
    rw [hc0]
    simp only [hc1, hfs, hc2, pure, Except.pure]
  · simpa [S1, Spec.Hash.absorb_append, Spec.Hash.absorb, List.foldl_cons] using hr2

/-- Customization strings longer than 256 bytes are rejected. -/
theorem init_too_long (Z : Bytes) (hZ : Bytes.length Z > 256) :
    init Z = .ok (.error .customizationTooLong) := by
  simp only [init, hZ, ↓reduceIte]; rfl

/-- `Cxof128.digest` is Ascon-CXOF128 for every valid length and customization. -/
theorem digest_correct (Z M : List Byte) (L : Int) :
    digest (Bytes.ofList Z) (Bytes.ofList M) L =
      .ok (if 0 < L ∧ L ≤ maxStringLength then
          (if Z.length ≤ 256 then .ok (Bytes.ofList (Spec.Hash.cxof128 M L.toNat Z))
           else .error .customizationTooLong)
        else .error .invalidLength) := by
  by_cases hL : 0 < L ∧ L ≤ maxStringLength
  · have hv : validDigestLength L = true := by simp [validDigestLength]; omega
    by_cases hZ : Z.length ≤ 256
    · obtain ⟨c, hc, hr⟩ := init_correct Z hZ
      obtain ⟨c1, h1, hr1⟩ := Sponge.absorb_correct _ [] M c hr
      obtain ⟨sq, hsq, hrep⟩ := finish_rep _ _ c1 hr1
      have hsqz := (Sponge.squeeze_correct _ 0 sq hrep L.toNat (by omega)).1
      rw [show ((L.toNat : Nat) : Int) = L by omega] at hsqz
      simp only [digest, hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hc, absorb,
        startSqueezing, h1, hsq, hsqz, bind, Except.bind, pure, Except.pure, ite_eq_left hL,
        ite_eq_left hZ]
      simp only [outBytes_zero_eq_squeeze, Spec.Hash.cxof128, List.nil_append]
    · have hlong : Bytes.length (Bytes.ofList Z) > 256 := by simp; omega
      simp only [digest, hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
        init_too_long _ hlong, bind, Except.bind, pure, Except.pure, ite_eq_left hL, ite_eq_right hZ]
  · have hv : validDigestLength L = false := by simp [validDigestLength]; omega
    simp [digest, hv, hL]; rfl

end Cxof128
end Ascon.Model
