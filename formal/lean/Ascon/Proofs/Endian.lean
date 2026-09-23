import Ascon.Model.Endian
import Ascon.Proofs.Loops
import Ascon.Proofs.Words

/-!
# `endian.ml` and `constant_time.ml`

The loads and stores used by the library read and write the intended bytes in
little-endian order. None of their guards fire, and no access goes out of
bounds or reads an uninitialized byte. `Constant_time.equal` decides byte-string
equality.
-/

namespace Ascon.Model

open Spec (wordLE bytesLE wordLE_append_single)

@[simp] theorem Bytes.length_eq (b : Bytes) : Bytes.length b = (List.length b : Int) := rfl

@[simp] theorem Bytes.length_ofList (l : List Byte) : List.length (Bytes.ofList l) = l.length := by
  simp [Bytes.ofList]

@[simp] theorem Bytes.ofList_append (a b : List Byte) :
    Bytes.ofList (a ++ b) = Bytes.ofList a ++ Bytes.ofList b := by
  simp [Bytes.ofList]

theorem Bytes.ofList_take (l : List Byte) (n : Nat) :
    Bytes.ofList (l.take n) = (Bytes.ofList l).take n := by simp [Bytes.ofList, List.map_take]

theorem Bytes.ofList_drop (l : List Byte) (n : Nat) :
    Bytes.ofList (l.drop n) = (Bytes.ofList l).drop n := by simp [Bytes.ofList, List.map_drop]

theorem Bytes.unsafeGet_append (pre post : List (Option Byte)) (xs : List Byte) (i : Nat)
    (hi : i < xs.length) :
    Bytes.unsafeGet (pre ++ Bytes.ofList xs ++ post) ((pre.length + i : Nat) : Int) =
      .ok xs[i] := by
  have hb : 0 ≤ ((pre.length + i : Nat) : Int) ∧
      ((pre.length + i : Nat) : Int) < Bytes.length (pre ++ Bytes.ofList xs ++ post) := by
    simp only [Bytes.length_eq, List.length_append, Bytes.length_ofList]; omega
  unfold Bytes.unsafeGet
  simp only [hb, and_self, ↓reduceDIte, Int.toNat_natCast]
  rw [List.getElem_append_left (by simp; omega), List.getElem_append_right (by omega)]
  simp [Bytes.ofList, pure, Except.pure]

theorem Int64.ofInt_code (c : Byte) : Int64.ofInt (Char.code c) = c.setWidth 64 := by
  apply BitVec.eq_of_toNat_eq
  simp only [Int64.ofInt, Char.code, BitVec.ofInt_natCast, BitVec.toNat_ofNat,
    BitVec.toNat_setWidth]

theorem Int64.shiftLeft_ok (x : Word) (n : Nat) (h : n < 64) :
    Int64.shiftLeft x n = .ok (x <<< n) := by
  simp only [Int64.shiftLeft, show (0 : Int) ≤ n ∧ (n : Int) < 64 by omega, and_self,
    ↓reduceIte, Int.toNat_natCast]; rfl

theorem Int64.shiftRightLogical_ok (x : Word) (n : Nat) (h : n < 64) :
    Int64.shiftRightLogical x n = .ok (x >>> n) := by
  simp only [Int64.shiftRightLogical, show (0 : Int) ≤ n ∧ (n : Int) < 64 by omega, and_self,
    ↓reduceIte, Int.toNat_natCast]; rfl

/-- `Char.chr (Int64.to_int (v land 0xff))` is the low byte of `v`. -/
theorem chr_low_byte (v : Word) :
    Char.chr (Int64.toInt (v &&& 0xff)) = .ok (v.setWidth 8) := by
  have hlt : (v &&& 0xff).toNat < 256 := by
    rw [BitVec.toNat_and]; exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
  have h63 : ((v &&& 0xff).setWidth 63).toNat = (v &&& 0xff).toNat := by
    rw [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by omega)
  have hint : Int64.toInt (v &&& 0xff) = ((v &&& 0xff).toNat : Int) := by
    unfold Int64.toInt
    rw [BitVec.toInt_eq_toNat_of_lt (by rw [h63]; omega), h63]
  rw [hint]
  simp only [Char.chr, show (0 : Int) ≤ ((v &&& 0xff).toNat : Int) ∧
    ((v &&& 0xff).toNat : Int) < 256 by omega, and_self, ↓reduceIte, Int.toNat_natCast, pure,
    Except.pure]
  congr 1
  rw [BitVec.ofNat_toNat]
  bv_decide

theorem byte_of_word (x : Word) (i : Nat) (hi : i < 8) :
    ((x >>> (8 * i)).setWidth 8 : Byte) = (bytesLE x)[i]'(by simp [Spec.bytesLE]; omega) := by
  have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp only [Spec.bytesLE, List.getElem_cons_zero, List.getElem_cons_succ] <;> bv_decide

theorem Bytes.unsafeSet_ok (b : List (Option Byte)) (i : Nat) (h : i < b.length) (c : Byte) :
    Bytes.unsafeSet b i c = .ok (b.set i (some c)) := by
  simp only [Bytes.unsafeSet, Bytes.length_eq, show (0 : Int) ≤ (i : Int) ∧ (i : Int) < b.length
    by omega, and_self, ↓reduceIte, Int.toNat_natCast]; rfl

/-- One step of a byte-by-byte store: overwrite position `k` of the block. -/
theorem set_block (pre post mid : List (Option Byte)) (xs : List Byte) (k : Nat)
    (hk : k < xs.length) (hkm : k < mid.length) :
    (pre ++ (Bytes.ofList (xs.take k) ++ mid.drop k) ++ post).set (pre.length + k)
        (some xs[k]) =
      pre ++ (Bytes.ofList (xs.take (k + 1)) ++ mid.drop (k + 1)) ++ post := by
  have hA : List.length (Bytes.ofList (xs.take k)) = k := by simp; omega
  rw [List.append_assoc pre, List.set_append_right _ _ (by omega), Nat.add_sub_cancel_left,
    List.append_assoc, List.set_append_right _ _ (by omega), hA, Nat.sub_self,
    List.drop_eq_getElem_cons hkm, List.cons_append, List.set_cons_zero,
    ← List.take_append_getElem hk]
  simp only [Bytes.ofList, List.map_append, List.map_cons, List.map_nil, List.append_assoc,
    List.cons_append, List.nil_append]

namespace Endian

/-- Loading `|xs| ≤ 8` initialized bytes at their offset gives their little-endian word. -/
theorem loadPartialLe_ok (pre post : List (Option Byte)) (xs : List Byte) (h : xs.length ≤ 8) :
    loadPartialLe (pre ++ Bytes.ofList xs ++ post) pre.length xs.length = .ok (wordLE xs) := by
  unfold loadPartialLe
  have hguard : ¬ ((pre.length : Int) < 0 ∨ (xs.length : Int) < 0 ∨ (xs.length : Int) > 8 ∨
      (pre.length : Int) > Bytes.length (pre ++ Bytes.ofList xs ++ post) - xs.length) := by
    simp only [Bytes.length, List.length_append, Bytes.length_ofList]; omega
  simp only [hguard, ↓reduceIte]
  obtain ⟨x, hx, hp⟩ := forUp_invariant 0 ((xs.length : Int) - 1) (by omega) (0 : Word)
    (fun i x => do
      pure (x ||| (← Int64.shiftLeft (← byte (pre ++ Bytes.ofList xs ++ post)
        (pre.length + i)) (8 * i))))
    (fun i x => 0 ≤ i ∧ x = wordLE (xs.take i.toNat)) ⟨Int.le_refl _, by simp []⟩ (by
      intro i x hlo hhi ⟨_, hx⟩
      obtain ⟨k, rfl⟩ : ∃ k : Nat, i = k := ⟨i.toNat, by omega⟩
      have hk : k < xs.length := by omega
      refine ⟨_, ?_, ⟨by omega, rfl⟩⟩
      simp only [byte, show ((pre.length : Int) + (k : Int)) = ((pre.length + k : Nat) : Int)
        by push_cast; rfl, Bytes.unsafeGet_append pre post xs k hk, bind, Except.bind, pure,
        Except.pure, Int64.ofInt_code, show (8 * (k : Int)) = ((8 * k : Nat) : Int) by push_cast; rfl,
        Int64.shiftLeft_ok _ (8 * k) (by omega), Int.toNat_natCast, hx]
      congr 1
      rw [show (k : Int) + 1 = ((k + 1 : Nat) : Int) by push_cast; rfl, Int.toNat_natCast,
        ← List.take_append_getElem hk, wordLE_append_single _ _ (by simp; omega)]
      simp only [List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)])
  rw [hx]
  simp only [hp.2]
  congr 1
  rw [show ((xs.length : Int) - 1 + 1).toNat = xs.length by omega, List.take_length]

theorem load64Le_ok (pre post : List (Option Byte)) (xs : List Byte) (h : xs.length = 8) :
    load64Le (pre ++ Bytes.ofList xs ++ post) pre.length = .ok (wordLE xs) := by
  have := loadPartialLe_ok pre post xs (by omega)
  rw [h] at this
  exact this

/-- Storing `len ≤ 8` bytes over `mid` (of length `len`) writes the low bytes of `x`. -/
theorem storePartialLe_ok (pre mid post : List (Option Byte)) (x : Word) (len : Nat) (h : len ≤ 8)
    (hm : mid.length = len) :
    storePartialLe (pre ++ mid ++ post) pre.length x len =
      .ok (pre ++ Bytes.ofList ((bytesLE x).take len) ++ post) := by
  unfold storePartialLe
  have hguard : ¬ ((pre.length : Int) < 0 ∨ (len : Int) < 0 ∨ (len : Int) > 8 ∨
      (pre.length : Int) > Bytes.length (pre ++ mid ++ post) - len) := by
    simp only [Bytes.length, List.length_append]; omega
  simp only [hguard, ↓reduceIte]
  obtain ⟨b, hb, hp⟩ := forUp_invariant 0 ((len : Int) - 1) (by omega) (pre ++ mid ++ post)
    (fun i b => do
      Bytes.unsafeSet b (pre.length + i)
        (← Char.chr (Int64.toInt ((← Int64.shiftRightLogical x (8 * i)) &&& 0xff))))
    (fun i b => 0 ≤ i ∧ i ≤ len ∧
      b = pre ++ (Bytes.ofList ((bytesLE x).take i.toNat) ++ mid.drop i.toNat) ++ post)
    ⟨Int.le_refl _, by omega, by simp [Bytes.ofList]⟩ (by
      intro i b hlo hhi ⟨_, _, hbv⟩
      obtain ⟨k, rfl⟩ : ∃ k : Nat, i = k := ⟨i.toNat, by omega⟩
      have hk : k < len := by omega
      have hk8 : k < 8 := by omega
      refine ⟨_, ?_, ⟨by omega, by omega, rfl⟩⟩
      simp only [show (8 * (k : Int)) = ((8 * k : Nat) : Int) by push_cast; rfl,
        Int64.shiftRightLogical_ok _ (8 * k) (by omega), chr_low_byte, bind, Except.bind,
        ]
      rw [byte_of_word x k hk8, hbv]
      simp only [Int.toNat_natCast]
      rw [show (pre.length : Int) + (k : Int) = ((pre.length + k : Nat) : Int) by push_cast; rfl,
        Bytes.unsafeSet_ok _ _ (by simp [Bytes.length_ofList, Spec.bytesLE_length]; omega)]
      rw [show (k : Int) + 1 = ((k + 1 : Nat) : Int) by push_cast; rfl, Int.toNat_natCast]
      exact congrArg Except.ok (set_block pre post mid (bytesLE x) k
        (by simp [Spec.bytesLE_length]; omega) (by omega)))
  rw [hb]
  obtain ⟨_, _, hbv⟩ := hp
  rw [hbv]
  simp only [show ((len : Int) - 1 + 1).toNat = len by omega]
  congr 1
  simp [hm]

theorem store64Le_ok (pre mid post : List (Option Byte)) (x : Word) (hm : mid.length = 8) :
    store64Le (pre ++ mid ++ post) pre.length x = .ok (pre ++ Bytes.ofList (bytesLE x) ++ post) := by
  have := storePartialLe_ok pre mid post x 8 (Nat.le_refl _) hm
  rw [List.take_of_length_le (by simp [Spec.bytesLE])] at this
  exact this

theorem padding_ok (i : Nat) (h : i < 8) : padding i = .ok (1#64 <<< (8 * i)) := by
  simp only [padding, show ¬ ((i : Int) < 0 ∨ (i : Int) > 7) by omega, ↓reduceIte, 
    show (8 * (i : Int)) = ((8 * i : Nat) : Int) by push_cast; rfl]
  exact Int64.shiftLeft_ok _ _ (by omega)

/-- The low-byte mask for `len < 8` bytes. -/
def lowMask (len : Nat) : Word := (1#64 <<< (8 * len)) - 1

theorem replaceLowBytes_ok (old replacement : Word) (len : Nat) (h : len < 8) :
    replaceLowBytes old replacement len =
      .ok ((old &&& ~~~(lowMask len)) ||| (replacement &&& lowMask len)) := by
  simp only [replaceLowBytes, show ¬ ((len : Int) < 0 ∨ (len : Int) > 8) by omega,
    show ¬ ((len : Int) = 8) by omega, ↓reduceIte, bind, Except.bind,
    show (8 * (len : Int)) = ((8 * len : Nat) : Int) by push_cast; rfl,
    Int64.shiftLeft_ok _ _ (show 8 * len < 64 by omega), pure, Except.pure, lowMask]
  rfl

theorem replaceLowBytes_eight (old replacement : Word) :
    replaceLowBytes old replacement 8 = .ok replacement := by
  simp [replaceLowBytes]; rfl

end Endian

namespace ConstantTime

theorem nat_xor_eq_zero {a b : Nat} : a ^^^ b = 0 ↔ a = b := by
  constructor
  · intro h
    have := congrArg (· ^^^ b) h
    simp only [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero, Nat.zero_xor] at this
    exact this
  · rintro rfl; exact Nat.xor_self a

/-- `Constant_time.equal` on initialized byte strings decides equality, with no fault. -/
theorem equal_ok (a b : List Byte) :
    equal (Bytes.ofList a) (Bytes.ofList b) = .ok (decide (a = b)) := by
  unfold equal
  by_cases hl : a.length = b.length
  · have hne : ¬ (Bytes.length (Bytes.ofList a) ≠ Bytes.length (Bytes.ofList b)) := by
      simp [hl]
    simp only [hne, ↓reduceIte]
    obtain ⟨d, hd, hp⟩ := forUp_invariant 0 (Bytes.length (Bytes.ofList a) - 1)
      (by simp) (0 : Nat)
      (fun i difference => do
        let x ← Bytes.unsafeGet (Bytes.ofList a) i
        let y ← Bytes.unsafeGet (Bytes.ofList b) i
        pure (difference ||| (x.toNat ^^^ y.toNat)))
      (fun i d => 0 ≤ i ∧ (d = 0 ↔ a.take i.toNat = b.take i.toNat))
      ⟨Int.le_refl _, by simp⟩ (by
        intro i d hlo hhi ⟨_, hd⟩
        obtain ⟨k, rfl⟩ : ∃ k : Nat, i = k := ⟨i.toNat, by omega⟩
        have hk : k < a.length := by simp at hhi; omega
        have hkb : k < b.length := by omega
        have ga := Bytes.unsafeGet_append [] [] a k hk
        have gb := Bytes.unsafeGet_append [] [] b k hkb
        simp only [List.nil_append, List.append_nil, List.length_nil, Nat.zero_add] at ga gb
        refine ⟨d ||| (a[k].toNat ^^^ b[k].toNat), ?_, ⟨by omega, ?_⟩⟩
        · simp only [ga, gb, bind, Except.bind, pure, Except.pure]
        · simp only [Int.toNat_natCast, show ((k : Int) + 1).toNat = k + 1 by omega,
            Nat.or_eq_zero_iff, nat_xor_eq_zero, BitVec.toNat_inj, hd]
          rw [← List.take_append_getElem hk, ← List.take_append_getElem hkb]
          constructor
          · rintro ⟨h1, h2⟩; rw [h1, h2]
          · intro h
            have h' := List.append_inj h (by simp; omega)
            simp only [List.cons.injEq, and_true] at h'
            exact h')
    rw [hd]
    simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq, decide_eq_decide]
    have hlen : ((Bytes.length (Bytes.ofList a)) - 1 + 1).toNat = a.length := by simp
    rw [hlen, List.take_length, hl, List.take_length] at hp
    exact hp.2
  · have hne : Bytes.length (Bytes.ofList a) ≠ Bytes.length (Bytes.ofList b) := by
      simp; omega
    have hab : a ≠ b := fun h => hl (h ▸ rfl)
    rw [ite_eq_left hne]
    simp only [hab, decide_false]
    rfl

end ConstantTime
end Ascon.Model
