import Ascon.Spec.Basic

/-!
# The Ascon permutation (SP 800-232, Sec. 3)

`Ascon-p[rnd]` applies `rnd` rounds of `p = p_L ∘ p_S ∘ p_C`. Round `i` of
`Ascon-p[rnd]` uses the constant `c_{16-rnd+i}` from Table 5.

The substitution layer is written *column-wise* with the 5-bit S-box lookup
table (Table 6), not with the bitsliced formula. The column
`S₀[j] ‖ S₁[j] ‖ S₂[j] ‖ S₃[j] ‖ S₄[j]` is the S-box input, with `S₀[j]` as its
most significant bit. The bitsliced formula used by the implementation is
proved equal to this table in `Ascon.Proofs.Permutation`.
-/

namespace Ascon.Spec

/-- Round constants `c₀ … c₁₅` (SP 800-232, Table 5). -/
def roundConstant (i : Nat) : Word :=
  match i with
  | 0 => 0x3c | 1 => 0x2d | 2 => 0x1e | 3 => 0x0f
  | 4 => 0xf0 | 5 => 0xe1 | 6 => 0xd2 | 7 => 0xc3
  | 8 => 0xb4 | 9 => 0xa5 | 10 => 0x96 | 11 => 0x87
  | 12 => 0x78 | 13 => 0x69 | 14 => 0x5a | 15 => 0x4b
  | _ => 0

/-- The 5-bit S-box (SP 800-232, Table 6), indexed by the input value. -/
def sboxTable : List (BitVec 5) :=
  [0x04, 0x0b, 0x1f, 0x14, 0x1a, 0x15, 0x09, 0x02,
   0x1b, 0x05, 0x08, 0x12, 0x1d, 0x03, 0x06, 0x1c,
   0x1e, 0x13, 0x07, 0x0e, 0x00, 0x0d, 0x11, 0x18,
   0x10, 0x0c, 0x01, 0x19, 0x16, 0x0a, 0x0f, 0x17]

def sbox (x : BitVec 5) : BitVec 5 := sboxTable.getD x.toNat 0

/-- The word whose bit `j` is `f j`. -/
def ofBits : (n : Nat) → (Nat → Bool) → BitVec n
  | 0, _ => 0#0
  | n + 1, f => BitVec.concat (ofBits n fun j => f (j + 1)) (f 0)

/-- Column `j` of the state, read with `S₀[j]` as the most significant bit. -/
def column (S : State) (j : Nat) : BitVec 5 :=
  BitVec.ofNat 5 (16 * (S.s0.getLsbD j).toNat + 8 * (S.s1.getLsbD j).toNat +
    4 * (S.s2.getLsbD j).toNat + 2 * (S.s3.getLsbD j).toNat + (S.s4.getLsbD j).toNat)

/-- Constant-addition layer `p_C`: `S₂ ← S₂ ⊕ cᵢ`. -/
def pC (c : Word) (S : State) : State := { S with s2 := S.s2 ^^^ c }

/-- Substitution layer `p_S`: the S-box applied to each of the 64 columns. -/
def pS (S : State) : State where
  s0 := ofBits 64 fun j => (sbox (column S j)).getLsbD 4
  s1 := ofBits 64 fun j => (sbox (column S j)).getLsbD 3
  s2 := ofBits 64 fun j => (sbox (column S j)).getLsbD 2
  s3 := ofBits 64 fun j => (sbox (column S j)).getLsbD 1
  s4 := ofBits 64 fun j => (sbox (column S j)).getLsbD 0

/-! ### Fast evaluation of `p_S`

Compiled code, for example the KAT runner, evaluates `pS` through the
bitsliced formula `pSBitsliced`. The replacement is a `@[csimp]` lemma, so it
is justified by the proof `pS_eq_pSBitsliced` below and is not trusted. All
definitions and proofs still refer to the table-based `pS`. -/

/-- The bitsliced form of `p_S` (the formula in SP 800-232, Fig. 3). -/
def pSBitsliced (S : State) : State :=
  let x0 := S.s0 ^^^ S.s4
  let x4 := S.s4 ^^^ S.s3
  let x2 := S.s2 ^^^ S.s1
  let x1 := S.s1
  let x3 := S.s3
  let t0 := x0 ^^^ (~~~x1 &&& x2)
  let t1 := x1 ^^^ (~~~x2 &&& x3)
  let t2 := x2 ^^^ (~~~x3 &&& x4)
  let t3 := x3 ^^^ (~~~x4 &&& x0)
  let t4 := x4 ^^^ (~~~x0 &&& x1)
  ⟨t0 ^^^ t4, t1 ^^^ t0, ~~~t2, t3 ^^^ t2, t4⟩

theorem getLsbD_ofBits (n : Nat) (f : Nat → Bool) (i : Nat) :
    (ofBits n f).getLsbD i = (decide (i < n) && f i) := by
  induction n generalizing f i with
  | zero => simp [ofBits]
  | succ n ih =>
    cases i with
    | zero => simp [ofBits]
    | succ i => simp [ofBits, BitVec.getLsbD_concat_succ, ih]

/-- The S-box table agrees with the bitsliced formula on all 32 inputs. -/
theorem sbox_column (b0 b1 b2 b3 b4 : Bool) :
    let x := sbox (BitVec.ofNat 5 (16 * b0.toNat + 8 * b1.toNat + 4 * b2.toNat +
      2 * b3.toNat + b4.toNat))
    x.getLsbD 4 = ((b0 ^^ b4) ^^ (!b1 && (b2 ^^ b1)) ^^ ((b4 ^^ b3) ^^ (!(b0 ^^ b4) && b1))) ∧
    x.getLsbD 3 = ((b1 ^^ (!(b2 ^^ b1) && b3)) ^^ ((b0 ^^ b4) ^^ (!b1 && (b2 ^^ b1)))) ∧
    x.getLsbD 2 = !((b2 ^^ b1) ^^ (!b3 && (b4 ^^ b3))) ∧
    x.getLsbD 1 = ((b3 ^^ (!(b4 ^^ b3) && (b0 ^^ b4))) ^^ ((b2 ^^ b1) ^^ (!b3 && (b4 ^^ b3)))) ∧
    x.getLsbD 0 = ((b4 ^^ b3) ^^ (!(b0 ^^ b4) && b1)) := by
  revert b0 b1 b2 b3 b4; decide

@[csimp] theorem pS_eq_pSBitsliced : @pS = @pSBitsliced := by
  funext S
  obtain ⟨s0, s1, s2, s3, s4⟩ := S
  simp only [pS, pSBitsliced, State.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have h := sbox_column (s0.getLsbD i) (s1.getLsbD i) (s2.getLsbD i) (s3.getLsbD i)
      (s4.getLsbD i)
    simp only [column, getLsbD_ofBits, hi, decide_true, Bool.true_and] at h ⊢
    simp only [h, BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_not, hi,
      decide_true, Bool.true_and]

/-- Linear diffusion layer `p_L` (SP 800-232, Eq. 3.4 – 3.8). -/
def pL (S : State) : State where
  s0 := S.s0 ^^^ S.s0.rotateRight 19 ^^^ S.s0.rotateRight 28
  s1 := S.s1 ^^^ S.s1.rotateRight 61 ^^^ S.s1.rotateRight 39
  s2 := S.s2 ^^^ S.s2.rotateRight 1 ^^^ S.s2.rotateRight 6
  s3 := S.s3 ^^^ S.s3.rotateRight 10 ^^^ S.s3.rotateRight 17
  s4 := S.s4 ^^^ S.s4.rotateRight 7 ^^^ S.s4.rotateRight 41

/-- One round `p = p_L ∘ p_S ∘ p_C` with constant `c`. -/
def round (c : Word) (S : State) : State := pL (pS (pC c S))

/-- `Ascon-p[rnd]` for `1 ≤ rnd ≤ 16`: round `i` uses `c_{16-rnd+i}`. -/
def asconP (rnd : Nat) (S : State) : State :=
  (List.range rnd).foldl (fun S i => round (roundConstant (16 - rnd + i)) S) S

end Ascon.Spec
