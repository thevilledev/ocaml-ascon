import Ascon.Model.Aead
import Ascon.Spec.Aead
import Ascon.Proofs.Sponge

/-!
# `Aead128` implements SP 800-232 Algorithms 3 and 4

* `encrypt_correct`: for every key, nonce, associated data and plaintext, the
  modelled `encrypt` runs without a fault and returns exactly
  `Ascon-AEAD128.enc(K, N, A, P)`, with every ciphertext and tag byte
  initialized.
* `decrypt_correct`: `decrypt` returns exactly `Ascon-AEAD128.dec(K, N, A, C, T)`,
  including `Invalid_tag_length` for tags that are not 16 bytes long.
* `encryptCombined_correct` / `decryptCombined_correct`: the combined format
  is `C ‖ T`. `encrypt_combined` succeeds if and only if the plaintext is at
  most `Sys.max_string_length - 16` bytes long.
-/

namespace Ascon.Spec

theorem pad16_long (rem : List Byte) (h8 : 8 ≤ rem.length) (h16 : rem.length < 16) :
    words128 (pad 16 rem) =
      (wordLE (rem.take 8), wordLE (rem.drop 8) ^^^ (1#64 <<< (8 * (rem.length - 8)))) := by
  have hd : (pad 16 rem).drop 8 = pad 8 (rem.drop 8) := by
    simp only [pad, List.append_assoc, List.drop_append_of_le_length h8, List.length_drop]
    congr 3; omega
  have ht : (pad 16 rem).take 8 = rem.take 8 := by
    simp only [pad, List.append_assoc, List.take_append_of_le_length h8]
  have hp := wordLE_pad8 (rem.drop 8) (by simp; omega)
  simp only [List.length_drop] at hp
  simp only [words128, ht, hd, hp]

theorem pad16_short (rem : List Byte) (h : rem.length < 8) :
    words128 (pad 16 rem) = (wordLE rem ^^^ (1#64 <<< (8 * rem.length)), 0) := by
  have ht : (pad 16 rem).take 8 = pad 8 rem ∧ (pad 16 rem).drop 8 = List.replicate 8 0#8 := by
    have h8 : rem.length ≤ 8 := by omega
    revert h
    refine List.cases_le8 rem h8 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> intros <;>
      simp_all [pad, List.replicate]
  simp only [words128, ht.1, ht.2, wordLE_pad8 rem h, wordLE_replicate_zero]

end Ascon.Spec

namespace Ascon.Model

open Spec (wordLE bytesLE parse pad paddedBlocks words128 xorBytes)
open Permutation

theorem loadPartialLe_at (X : List Byte) (off len : Nat) (h : off + len ≤ X.length)
    (hlen : len ≤ 8) :
    Endian.loadPartialLe (Bytes.ofList X) off len = .ok (wordLE ((X.drop off).take len)) := by
  have := Endian.loadPartialLe_ok (Bytes.ofList (X.take off)) (Bytes.ofList (X.drop (off + len)))
    ((X.drop off).take len) (by simp; omega)
  rw [← Bytes.ofList_split3 X off len, Bytes.length_ofList,
    show ((X.drop off).take len).length = len by simp; omega,
    show (X.take off).length = off by simp; omega] at this
  exact this

theorem load64Le_at (X : List Byte) (off : Nat) (h : off + 8 ≤ X.length) :
    Endian.load64Le (Bytes.ofList X) off = .ok (wordLE ((X.drop off).take 8)) :=
  loadPartialLe_at X off 8 h (Nat.le_refl _)

theorem storePartialLe_at (C : List Byte) (n : Nat) (x : Word) (len : Nat) (hlen : len ≤ 8)
    (hn : len ≤ n) :
    Endian.storePartialLe (Bytes.ofList C ++ List.replicate n none) C.length x len =
      .ok (Bytes.ofList (C ++ (bytesLE x).take len) ++ List.replicate (n - len) none) := by
  have := Endian.storePartialLe_ok (Bytes.ofList C) (List.replicate len none)
    (List.replicate (n - len) none) x len hlen (by simp)
  rw [List.append_assoc, List.replicate_append_replicate, Nat.add_sub_cancel' hn,
    Bytes.length_ofList, ← Bytes.ofList_append] at this
  exact this

theorem store64Le_at (C : List Byte) (n : Nat) (x : Word) (hn : 8 ≤ n) :
    Endian.store64Le (Bytes.ofList C ++ List.replicate n none) C.length x =
      .ok (Bytes.ofList (C ++ bytesLE x) ++ List.replicate (n - 8) none) := by
  have := storePartialLe_at C n x 8 (Nat.le_refl _) hn
  rw [List.take_of_length_le (by simp [Spec.bytesLE_length])] at this
  exact this

namespace Aead128

theorem initialize_ok (K N : List Byte) (hK : K.length = 16) (hN : N.length = 16) :
    «initialize» (Bytes.ofList K) (Bytes.ofList N) =
      .ok (State.ofSpec (Spec.Aead.init K N), wordLE (K.take 8), wordLE (K.drop 8)) := by
  have l0 : ∀ X : List Byte, X.length = 16 →
      Endian.load64Le (Bytes.ofList X) 0 = .ok (wordLE (X.take 8)) := fun X hX => by
    simpa using load64Le_at X 0 (by omega)
  have l8 : ∀ X : List Byte, X.length = 16 →
      Endian.load64Le (Bytes.ofList X) 8 = .ok (wordLE (X.drop 8)) := fun X hX => by
    have := load64Le_at X 8 (by omega)
    rwa [List.take_of_length_le (by simp; omega)] at this
  simp only [«initialize», l0 K hK, l8 K hK, l0 N hN, l8 N hN, bind, Except.bind, p12_correct]
  have hS : (State.create iv (wordLE (K.take 8)) (wordLE (K.drop 8)) (wordLE (N.take 8))
      (wordLE (N.drop 8))).toSpec = ⟨Spec.Aead.IV, wordLE (K.take 8), wordLE (K.drop 8),
        wordLE (N.take 8), wordLE (N.drop 8)⟩ := rfl
  rw [hS]
  simp only [Spec.Aead.init]
  generalize Spec.asconP 12 _ = T
  rfl

/-- One associated-data block: `S ← Ascon-p[8](S ⊕ Aᵢ)`. -/
def adStep (S : Spec.State) (B : List Byte) : Spec.State := Spec.asconP 8 (Spec.Aead.xorRate S B)

theorem drop_take_8 (X : List Byte) (off : Nat) :
    ((X.drop off).take 16).take 8 = (X.drop off).take 8 ∧
    ((X.drop off).take 16).drop 8 = (X.drop (off + 8)).take 8 := by
  constructor
  · simp [List.take_take]
  · simp [List.drop_take, List.drop_drop]

theorem adLoop_ok (A : List Byte) (st : State) (off : Nat) (hoff : off ≤ A.length) :
    adLoop st (Bytes.ofList A) off =
      .ok (State.ofSpec ((parse 16 (A.drop off)).1.foldl adStep st.toSpec),
        ((off + 16 * (parse 16 (A.drop off)).1.length : Nat) : Int)) := by
  induction h : A.length - off using Nat.strongRecOn generalizing st off with
  | ind n ih =>
    rw [adLoop]
    by_cases hlong : 16 ≤ A.length - off
    · rw [ite_eq_left (by simp; omega)]
      have hl0 := load64Le_at A off (by omega)
      have hl8 := load64Le_at A (off + 8) (by omega)
      rw [show ((off + 8 : Nat) : Int) = (off : Int) + 8 by push_cast; rfl] at hl8
      simp only [hl0, hl8, bind, Except.bind, p8_correct]
      have hstep : Spec.asconP 8 (State.mk (st.x0 ^^^ wordLE ((A.drop off).take 8))
          (st.x1 ^^^ wordLE ((A.drop (off + 8)).take 8)) st.x2 st.x3 st.x4).toSpec =
          adStep st.toSpec ((A.drop off).take 16) := by
        simp only [adStep, Spec.Aead.xorRate, words128, (drop_take_8 A off).1,
          (drop_take_8 A off).2]
        rfl
      rw [hstep]
      have := ih (A.length - (off + 16)) (by omega)
        (State.ofSpec (adStep st.toSpec ((A.drop off).take 16))) (off + 16) (by omega) rfl
      rw [State.toSpec_ofSpec,
        show off + 16 + 16 * (parse 16 (A.drop (off + 16))).1.length =
          off + 16 * ((parse 16 (A.drop (off + 16))).1.length + 1) by omega] at this
      rw [Spec.parse_long (A.drop off) (by decide) (by simp; omega)]
      simp only [List.drop_drop, List.foldl_cons, List.length_cons]
      rw [show (off : Int) + 16 = ((off + 16 : Nat) : Int) by push_cast; rfl]
      exact this
    · rw [ite_eq_right (by simp; omega), Spec.parse_short (A.drop off) (by simp; omega)]
      rfl

theorem pad_bit_low (k : Nat) (hk : k < 8) :
    (1#64 <<< (8 * k)) &&& ((1#64 <<< (8 * k)) - 1) = 0 := by
  have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- The final associated-data block is `pad(A_{m-1})`, followed by `p[8]`. -/
theorem adTail_ok (A : List Byte) (st : State) (off : Nat) (hoff : off ≤ A.length)
    (hrem : A.length - off < 16) :
    adTail st (Bytes.ofList A) off = .ok (State.ofSpec (adStep st.toSpec (pad 16 (A.drop off)))) := by
  unfold adTail
  have hr : Bytes.length (Bytes.ofList A) - (off : Int) = ((A.length - off : Nat) : Int) := by
    simp; omega
  by_cases h8 : 8 ≤ A.length - off
  · have hl0 := load64Le_at A off (by omega)
    have hlp := loadPartialLe_at A (off + 8) (A.length - off - 8) (by omega) (by omega)
    rw [show ((off + 8 : Nat) : Int) = (off : Int) + 8 by push_cast; rfl,
      show ((A.length - off - 8 : Nat) : Int) = ((A.length - off : Nat) : Int) - 8 by omega] at hlp
    have hpd := Endian.padding_ok (A.length - off - 8) (by omega)
    rw [show ((A.length - off - 8 : Nat) : Int) = ((A.length - off : Nat) : Int) - 8 by omega] at hpd
    rw [hr]
    simp only [show ((A.length - off : Nat) : Int) ≥ 8 by omega, ↓reduceIte, hl0, hlp, hpd,
      ok_bind, pure_bind, p8_correct]
    have hp := Spec.pad16_long (A.drop off) (by simp; omega) (by simp; omega)
    simp only [adStep, Spec.Aead.xorRate, hp, List.length_drop, List.drop_drop,
      List.take_of_length_le (show (A.drop (off + 8)).length ≤ A.length - off - 8 by simp; omega)]
    apply congrArg (fun S => (Except.ok (State.ofSpec (Spec.asconP 8 S)) : M State))
    simp only [State.toSpec, BitVec.xor_assoc]
  · have hlp := loadPartialLe_at A off (A.length - off) (by omega) (by omega)
    rw [hr]
    simp only [show ¬ (((A.length - off : Nat) : Int) ≥ 8) by omega, ↓reduceIte, hlp,
      Endian.padding_ok _ (show A.length - off < 8 by omega), ok_bind, pure_bind, p8_correct]
    have hp := Spec.pad16_short (A.drop off) (by simp; omega)
    simp only [adStep, Spec.Aead.xorRate, hp, List.length_drop,
      List.take_of_length_le (show (A.drop off).length ≤ A.length - off by simp)]
    apply congrArg (fun S => (Except.ok (State.ofSpec (Spec.asconP 8 S)) : M State))
    simp only [State.toSpec, BitVec.xor_assoc, Spec.State.mk.injEq, true_and, and_true]
    bv_decide

theorem absorbAssociatedData_ok (A : List Byte) (st : State) :
    absorbAssociatedData st (Bytes.ofList A) =
      .ok (State.ofSpec (Spec.Aead.processAD st.toSpec A)) := by
  unfold absorbAssociatedData Spec.Aead.processAD
  by_cases h0 : A.length = 0
  · obtain rfl : A = [] := List.eq_nil_of_length_eq_zero h0
    rfl
  · have hz : Bytes.length (Bytes.ofList A) ≠ 0 := by
      simp only [Bytes.length_eq, Bytes.length_ofList]; omega
    have hloop := adLoop_ok A st 0 (Nat.zero_le _)
    simp only [List.drop_zero, Nat.zero_add, Sponge.natCast_zero_int] at hloop
    have hn := Spec.parse_rem_eq_drop (r := 16) A (by decide)
    have hj := Spec.parse_join (r := 16) A (by decide)
    have hfl := Spec.parse_flatten_length (r := 16) A (by decide)
    have hrl := Spec.parse_rem_length (r := 16) A (by decide)
    have hlen : A.length = 16 * (parse 16 A).1.length + (parse 16 A).2.length := by
      rw [← hfl, ← List.length_append, hj]
    have htail := adTail_ok A (State.ofSpec ((parse 16 A).1.foldl adStep st.toSpec))
      (16 * (parse 16 A).1.length) (by omega) (by omega)
    rw [ite_eq_left hz, ite_eq_left (by omega)]
    simp only [hloop, ok_bind, htail]
    simp only [State.toSpec_ofSpec, ← hn, paddedBlocks, List.foldl_append, List.foldl_cons,
      List.foldl_nil]
    rfl

theorem finalize_ok (st : State) (K : List Byte) :
    finalize st (wordLE (K.take 8)) (wordLE (K.drop 8)) =
      .ok (Bytes.ofList (Spec.Aead.finalize st.toSpec K)) := by
  have hc : Bytes.create tagSize = .ok (Bytes.ofList [] ++ List.replicate 16 none) := by
    have := Sponge.Bytes.create_ok 16 (by decide)
    simpa [Bytes.ofList, tagSize] using this
  have s0 : ∀ x, Endian.store64Le (Bytes.ofList [] ++ List.replicate 16 none) 0 x =
      .ok (Bytes.ofList (bytesLE x) ++ List.replicate 8 none) := by
    intro x; simpa using store64Le_at [] 16 x (by decide)
  have s8 : ∀ x y, Endian.store64Le (Bytes.ofList (bytesLE x) ++ List.replicate 8 none) 8 y =
      .ok (Bytes.ofList (bytesLE x ++ bytesLE y)) := by
    intro x y
    have := store64Le_at (bytesLE x) 8 y (by decide)
    simpa [Spec.bytesLE_length] using this
  simp only [finalize, p12_correct, ok_bind, hc, s0, s8]
  simp only [Spec.Aead.finalize]
  rfl

theorem encryptBlocks_cons (S : Spec.State) (B : List Byte) (Bs : List (List Byte)) :
    Spec.Aead.encryptBlocks S (B :: Bs) =
      ((Spec.Aead.encryptBlocks (Spec.asconP 8 (Spec.Aead.xorRate S B)) Bs).1,
        Spec.Aead.rateBytes (Spec.Aead.xorRate S B) ++
          (Spec.Aead.encryptBlocks (Spec.asconP 8 (Spec.Aead.xorRate S B)) Bs).2) := rfl

theorem encryptLoop_ok (P : List Byte) (st : State) (C : List Byte) (off : Nat)
    (hoff : off ≤ P.length) (hC : C.length = off) :
    encryptLoop st (Bytes.ofList P) (Bytes.ofList C ++ List.replicate (P.length - off) none) off =
      .ok (State.ofSpec (Spec.Aead.encryptBlocks st.toSpec (parse 16 (P.drop off)).1).1,
        Bytes.ofList (C ++ (Spec.Aead.encryptBlocks st.toSpec (parse 16 (P.drop off)).1).2) ++
          List.replicate (P.length - (off + 16 * (parse 16 (P.drop off)).1.length)) none,
        ((off + 16 * (parse 16 (P.drop off)).1.length : Nat) : Int)) := by
  induction h : P.length - off using Nat.strongRecOn generalizing st C off with
  | ind n ih =>
    subst h
    rw [encryptLoop]
    by_cases hlong : 16 ≤ P.length - off
    · rw [ite_eq_left (by simp; omega)]
      have hl0 := load64Le_at P off (by omega)
      have hl8 := load64Le_at P (off + 8) (by omega)
      rw [show ((off + 8 : Nat) : Int) = (off : Int) + 8 by push_cast; rfl] at hl8
      have hs0 := store64Le_at C (P.length - off)
        (st.x0 ^^^ wordLE ((P.drop off).take 8)) (by omega)
      rw [hC] at hs0
      have hs8 := store64Le_at (C ++ bytesLE (st.x0 ^^^ wordLE ((P.drop off).take 8)))
        (P.length - off - 8) (st.x1 ^^^ wordLE ((P.drop (off + 8)).take 8)) (by omega)
      rw [List.length_append, hC, Spec.bytesLE_length,
        show ((off + 8 : Nat) : Int) = (off : Int) + 8 by push_cast; rfl] at hs8
      simp only [hl0, hl8, ok_bind, hs0, hs8, p8_correct]
      have hB := drop_take_8 P off
      have hstep : Spec.asconP 8 (State.mk (st.x0 ^^^ wordLE ((P.drop off).take 8))
          (st.x1 ^^^ wordLE ((P.drop (off + 8)).take 8)) st.x2 st.x3 st.x4).toSpec =
          Spec.asconP 8 (Spec.Aead.xorRate st.toSpec ((P.drop off).take 16)) := by
        simp only [Spec.Aead.xorRate, words128, hB.1, hB.2]
        rfl
      have hrate : bytesLE (st.x0 ^^^ wordLE ((P.drop off).take 8)) ++
          bytesLE (st.x1 ^^^ wordLE ((P.drop (off + 8)).take 8)) =
          Spec.Aead.rateBytes (Spec.Aead.xorRate st.toSpec ((P.drop off).take 16)) := by
        simp only [Spec.Aead.rateBytes, Spec.Aead.xorRate, words128, hB.1, hB.2]
        rfl
      rw [hstep, List.append_assoc, hrate]
      have := ih (P.length - (off + 16)) (by omega)
        (State.ofSpec (Spec.asconP 8 (Spec.Aead.xorRate st.toSpec ((P.drop off).take 16))))
        (C ++ Spec.Aead.rateBytes (Spec.Aead.xorRate st.toSpec ((P.drop off).take 16)))
        (off + 16) (by omega) (by simp [Spec.Aead.rateBytes, Spec.bytesLE_length]; omega) rfl
      rw [State.toSpec_ofSpec,
        show P.length - (off + 16) = P.length - off - 8 - 8 by omega] at this
      rw [Spec.parse_long (P.drop off) (by decide) (by simp; omega)]
      simp only [List.drop_drop, encryptBlocks_cons, List.length_cons]
      rw [show (off : Int) + 16 = ((off + 16 : Nat) : Int) by push_cast; rfl,
        show off + 16 * ((parse 16 (List.drop (off + 16) P)).1.length + 1) =
          off + 16 + 16 * (parse 16 (List.drop (off + 16) P)).1.length by omega]
      rw [this]
      simp only [List.append_assoc]
    · rw [ite_eq_right (by simp; omega), Spec.parse_short (P.drop off) (by simp; omega)]
      simp only [Spec.Aead.encryptBlocks, List.append_nil, List.length_nil, Nat.mul_zero,
        Nat.add_zero, State.ofSpec_toSpec]
      rfl

theorem take_rateBytes_long (S : Spec.State) (r : Nat) (h8 : 8 ≤ r) :
    (Spec.Aead.rateBytes S).take r = bytesLE S.s0 ++ (bytesLE S.s1).take (r - 8) := by
  simp only [Spec.Aead.rateBytes, List.take_append, Spec.bytesLE_length,
    List.take_of_length_le (show (bytesLE S.s0).length ≤ r by simp [Spec.bytesLE_length]; omega)]

theorem take_rateBytes_short (S : Spec.State) (r : Nat) (h8 : r ≤ 8) :
    (Spec.Aead.rateBytes S).take r = (bytesLE S.s0).take r := by
  simp only [Spec.Aead.rateBytes, List.take_append, Spec.bytesLE_length,
    show r - 8 = 0 by omega, List.take_zero, List.append_nil]

theorem encryptTail_ok (P : List Byte) (st : State) (C : List Byte) (off : Nat)
    (hoff : off ≤ P.length) (hrem : P.length - off < 16) (hC : C.length = off) :
    encryptTail st (Bytes.ofList P) (Bytes.ofList C ++ List.replicate (P.length - off) none) off =
      .ok (State.ofSpec (Spec.Aead.xorRate st.toSpec (pad 16 (P.drop off))),
        Bytes.ofList (C ++ (Spec.Aead.rateBytes
          (Spec.Aead.xorRate st.toSpec (pad 16 (P.drop off)))).take (P.length - off))) := by
  unfold encryptTail
  have hr : Bytes.length (Bytes.ofList P) - (off : Int) = ((P.length - off : Nat) : Int) := by
    simp; omega
  rw [hr]
  by_cases h8 : 8 ≤ P.length - off
  · have hl0 := load64Le_at P off (by omega)
    have hlp := loadPartialLe_at P (off + 8) (P.length - off - 8) (by omega) (by omega)
    rw [show ((off + 8 : Nat) : Int) = (off : Int) + 8 by push_cast; rfl,
      show ((P.length - off - 8 : Nat) : Int) = ((P.length - off : Nat) : Int) - 8 by omega,
      List.take_of_length_le (show (P.drop (off + 8)).length ≤ P.length - off - 8 by
        simp; omega)] at hlp
    have hs0 := store64Le_at C (P.length - off)
      (st.x0 ^^^ wordLE ((P.drop off).take 8)) (by omega)
    rw [hC] at hs0
    have hsp := storePartialLe_at (C ++ bytesLE (st.x0 ^^^ wordLE ((P.drop off).take 8)))
      (P.length - off - 8) (st.x1 ^^^ wordLE (P.drop (off + 8))) (P.length - off - 8)
      (by omega) (Nat.le_refl _)
    rw [List.length_append, hC, Spec.bytesLE_length,
      show ((off + 8 : Nat) : Int) = (off : Int) + 8 by push_cast; rfl,
      show ((P.length - off - 8 : Nat) : Int) = ((P.length - off : Nat) : Int) - 8 by omega,
      Nat.sub_self, List.replicate_zero, List.append_nil] at hsp
    rw [show P.length - off - 8 = (P.length - off) - 8 from rfl] at hs0
    have hpd := Endian.padding_ok (P.length - off - 8) (by omega)
    rw [show ((P.length - off - 8 : Nat) : Int) = ((P.length - off : Nat) : Int) - 8 by omega] at hpd
    simp only [show ((P.length - off : Nat) : Int) ≥ 8 by omega, ↓reduceIte, hl0, hlp, ok_bind,
      hs0, hsp, hpd]
    have hp := Spec.pad16_long (P.drop off) (by simp; omega) (by simp; omega)
    simp only [List.length_drop, List.drop_drop] at hp
    rw [take_rateBytes_long _ _ h8]
    simp only [Spec.Aead.xorRate, hp, List.append_assoc]
    rw [← BitVec.xor_assoc, Spec.bytesLE_xor_high_take _ (1#64 <<< (8 * (P.length - off - 8)))
      (P.length - off - 8) (by omega) (pad_bit_low _ (by omega))]
    rfl
  · have hlp := loadPartialLe_at P off (P.length - off) (by omega) (by omega)
    rw [List.take_of_length_le (show (P.drop off).length ≤ P.length - off by simp)] at hlp
    have hsp := storePartialLe_at C (P.length - off) (st.x0 ^^^ wordLE (P.drop off))
      (P.length - off) (by omega) (Nat.le_refl _)
    rw [hC, Nat.sub_self, List.replicate_zero, List.append_nil] at hsp
    simp only [show ¬ (((P.length - off : Nat) : Int) ≥ 8) by omega, ↓reduceIte, hlp, ok_bind,
      hsp, Endian.padding_ok _ (show P.length - off < 8 by omega)]
    have hp := Spec.pad16_short (P.drop off) (by simp; omega)
    simp only [List.length_drop] at hp
    rw [take_rateBytes_short _ _ (by omega)]
    simp only [Spec.Aead.xorRate, hp]
    rw [← BitVec.xor_assoc, Spec.bytesLE_xor_high_take _ (1#64 <<< (8 * (P.length - off)))
      (P.length - off) (by omega) (pad_bit_low _ (by omega))]
    rw [show st.toSpec.s1 ^^^ (0 : Spec.Word) = st.x1 by simp [State.toSpec]]
    rfl

theorem encryptBlocks_length (S : Spec.State) (Bs : List (List Byte)) :
    (Spec.Aead.encryptBlocks S Bs).2.length = 16 * Bs.length := by
  induction Bs generalizing S with
  | nil => rfl
  | cons B Bs ih =>
    rw [encryptBlocks_cons]
    simp only [List.length_append, ih, Spec.Aead.rateBytes, Spec.bytesLE_length, List.length_cons]
    omega

/-- Algorithm 3 with its pattern-matching `let`s replaced by projections. -/
theorem _root_.Ascon.Spec.Aead.encrypt_eq (K N A P : List Byte) :
    Spec.Aead.encrypt K N A P =
      let S0 := Spec.Aead.processAD (Spec.Aead.init K N) A
      let R := Spec.Aead.encryptBlocks S0 (parse 16 P).1
      let S := Spec.Aead.xorRate R.1 (pad 16 (parse 16 P).2)
      (R.2 ++ (Spec.Aead.rateBytes S).take (parse 16 P).2.length, Spec.Aead.finalize S K) := rfl

/-- `Aead128.encrypt` is Ascon-AEAD128 encryption (SP 800-232, Algorithm 3). -/
theorem encrypt_correct (K N A P : List Byte) (hK : K.length = 16) (hN : N.length = 16)
    (hP : (P.length : Int) ≤ maxStringLength) :
    encrypt (Bytes.ofList K) (Bytes.ofList N) (Bytes.ofList A) (Bytes.ofList P) =
      .ok (Bytes.ofList (Spec.Aead.encrypt K N A P).1,
        Bytes.ofList (Spec.Aead.encrypt K N A P).2) := by
  let S0 := Spec.Aead.processAD (Spec.Aead.init K N) A
  have hn := Spec.parse_rem_eq_drop (r := 16) P (by decide)
  have hj := Spec.parse_join (r := 16) P (by decide)
  have hfl := Spec.parse_flatten_length (r := 16) P (by decide)
  have hrl := Spec.parse_rem_length (r := 16) P (by decide)
  have hlen : P.length = 16 * (parse 16 P).1.length + (parse 16 P).2.length := by
    rw [← hfl, ← List.length_append, hj]
  have hc : Bytes.create (Bytes.length (Bytes.ofList P)) =
      .ok (Bytes.ofList [] ++ List.replicate (P.length - 0) none) := by
    simpa [Bytes.ofList] using Sponge.Bytes.create_ok P.length hP
  have hloop := encryptLoop_ok P (State.ofSpec S0) [] 0 (Nat.zero_le _) rfl
  simp only [List.drop_zero, Nat.zero_add, Sponge.natCast_zero_int, List.nil_append,
    State.toSpec_ofSpec] at hloop
  have htail := encryptTail_ok P (State.ofSpec (Spec.Aead.encryptBlocks S0 (parse 16 P).1).1)
    (Spec.Aead.encryptBlocks S0 (parse 16 P).1).2 (16 * (parse 16 P).1.length) (by omega)
    (by omega) (encryptBlocks_length _ _)
  rw [← hn, State.toSpec_ofSpec] at htail
  have hfin := finalize_ok (State.ofSpec (Spec.Aead.xorRate
    (Spec.Aead.encryptBlocks S0 (parse 16 P).1).1 (pad 16 (parse 16 P).2))) K
  rw [State.toSpec_ofSpec] at hfin
  simp only [encrypt, initialize_ok K N hK hN, ok_bind, absorbAssociatedData_ok,
    State.toSpec_ofSpec, hc]
  simp only [Nat.sub_zero] at hloop ⊢
  rw [bind_of_ok hloop]
  simp only []
  rw [bind_of_ok htail]
  simp only []
  rw [bind_of_ok hfin, Spec.Aead.encrypt_eq]
  simp only [show P.length - 16 * (parse 16 P).1.length = (parse 16 P).2.length by omega,
    Bytes.ofList_append]
  rfl

theorem decryptBlocks_cons (S : Spec.State) (B : List Byte) (Bs : List (List Byte)) :
    Spec.Aead.decryptBlocks S (B :: Bs) =
      ((Spec.Aead.decryptBlocks (Spec.asconP 8 (Spec.Aead.setRate S B)) Bs).1,
        xorBytes (Spec.Aead.rateBytes S) B ++
          (Spec.Aead.decryptBlocks (Spec.asconP 8 (Spec.Aead.setRate S B)) Bs).2) := rfl

theorem decryptBlocks_length (S : Spec.State) (Bs : List (List Byte))
    (h : ∀ B ∈ Bs, B.length = 16) :
    (Spec.Aead.decryptBlocks S Bs).2.length = 16 * Bs.length := by
  induction Bs generalizing S with
  | nil => rfl
  | cons B Bs ih =>
    rw [decryptBlocks_cons]
    simp only [List.length_append, ih _ (fun B' hB' => h B' (by simp [hB'])), xorBytes,
      List.length_zipWith, Spec.Aead.rateBytes, Spec.bytesLE_length, List.length_cons,
      h B (by simp)]
    omega

theorem xorBytes_append (a b c d : List Byte) (h : a.length = c.length) :
    xorBytes (a ++ b) (c ++ d) = xorBytes a c ++ xorBytes b d := by
  simp only [xorBytes]; exact List.zipWith_append h

theorem xorBytes_append_left (a b X : List Byte) (h : a.length ≤ X.length) :
    xorBytes (a ++ b) X = xorBytes a (X.take a.length) ++ xorBytes b (X.drop a.length) := by
  calc xorBytes (a ++ b) X = xorBytes (a ++ b) (X.take a.length ++ X.drop a.length) := by
        rw [List.take_append_drop]
    _ = _ := xorBytes_append _ _ _ _ (by simp; omega)

/-- The eight bytes of `x ⊕ wordLE b` are `bytesLE x ⊕ b`. -/
theorem bytesLE_xor_eight (x : Word) (b : List Byte) (h : b.length = 8) :
    bytesLE (x ^^^ wordLE b) = xorBytes (bytesLE x) b := by
  have := Spec.bytesLE_xor_wordLE_take x b (by omega)
  rwa [h, List.take_of_length_le (by simp [Spec.bytesLE_length]),
    List.take_of_length_le (by simp [Spec.bytesLE_length])] at this

theorem decryptLoop_ok (Cx : List Byte) (st : State) (Pp : List Byte) (off : Nat)
    (hoff : off ≤ Cx.length) (hP : Pp.length = off) :
    decryptLoop st (Bytes.ofList Cx) (Bytes.ofList Pp ++ List.replicate (Cx.length - off) none)
        off =
      .ok (State.ofSpec (Spec.Aead.decryptBlocks st.toSpec (parse 16 (Cx.drop off)).1).1,
        Bytes.ofList (Pp ++ (Spec.Aead.decryptBlocks st.toSpec (parse 16 (Cx.drop off)).1).2) ++
          List.replicate (Cx.length - (off + 16 * (parse 16 (Cx.drop off)).1.length)) none,
        ((off + 16 * (parse 16 (Cx.drop off)).1.length : Nat) : Int)) := by
  induction h : Cx.length - off using Nat.strongRecOn generalizing st Pp off with
  | ind n ih =>
    subst h
    rw [decryptLoop]
    by_cases hlong : 16 ≤ Cx.length - off
    · rw [ite_eq_left (by simp; omega)]
      have hl0 := load64Le_at Cx off (by omega)
      have hl8 := load64Le_at Cx (off + 8) (by omega)
      rw [show ((off + 8 : Nat) : Int) = (off : Int) + 8 by push_cast; rfl] at hl8
      have hs0 := store64Le_at Pp (Cx.length - off)
        (st.x0 ^^^ wordLE ((Cx.drop off).take 8)) (by omega)
      rw [hP] at hs0
      have hs8 := store64Le_at (Pp ++ bytesLE (st.x0 ^^^ wordLE ((Cx.drop off).take 8)))
        (Cx.length - off - 8) (st.x1 ^^^ wordLE ((Cx.drop (off + 8)).take 8)) (by omega)
      rw [List.length_append, hP, Spec.bytesLE_length,
        show ((off + 8 : Nat) : Int) = (off : Int) + 8 by push_cast; rfl] at hs8
      simp only [hl0, hl8, ok_bind, hs0, hs8, p8_correct]
      have hB := drop_take_8 Cx off
      have hstep : Spec.asconP 8 (State.mk (wordLE ((Cx.drop off).take 8))
          (wordLE ((Cx.drop (off + 8)).take 8)) st.x2 st.x3 st.x4).toSpec =
          Spec.asconP 8 (Spec.Aead.setRate st.toSpec ((Cx.drop off).take 16)) := by
        simp only [Spec.Aead.setRate, words128, hB.1, hB.2]
        rfl
      have hplain : bytesLE (st.x0 ^^^ wordLE ((Cx.drop off).take 8)) ++
          bytesLE (st.x1 ^^^ wordLE ((Cx.drop (off + 8)).take 8)) =
          xorBytes (Spec.Aead.rateBytes st.toSpec) ((Cx.drop off).take 16) := by
        rw [bytesLE_xor_eight _ _ (by simp; omega), bytesLE_xor_eight _ _ (by simp; omega),
          ← xorBytes_append _ _ _ _ (by simp [Spec.bytesLE_length]; omega),
          ← hB.1, ← hB.2, List.take_append_drop]
        rfl
      rw [hstep, List.append_assoc, hplain]
      have := ih (Cx.length - (off + 16)) (by omega)
        (State.ofSpec (Spec.asconP 8 (Spec.Aead.setRate st.toSpec ((Cx.drop off).take 16))))
        (Pp ++ xorBytes (Spec.Aead.rateBytes st.toSpec) ((Cx.drop off).take 16))
        (off + 16) (by omega)
        (by simp [xorBytes, Spec.Aead.rateBytes, Spec.bytesLE_length]; omega) rfl
      rw [State.toSpec_ofSpec,
        show Cx.length - (off + 16) = Cx.length - off - 8 - 8 by omega] at this
      rw [Spec.parse_long (Cx.drop off) (by decide) (by simp; omega)]
      simp only [List.drop_drop, decryptBlocks_cons, List.length_cons]
      rw [show (off : Int) + 16 = ((off + 16 : Nat) : Int) by push_cast; rfl,
        show off + 16 * ((parse 16 (List.drop (off + 16) Cx)).1.length + 1) =
          off + 16 + 16 * (parse 16 (List.drop (off + 16) Cx)).1.length by omega]
      rw [this]
      simp only [List.append_assoc]
    · rw [ite_eq_right (by simp; omega), Spec.parse_short (Cx.drop off) (by simp; omega)]
      simp only [Spec.Aead.decryptBlocks, List.append_nil, List.length_nil, Nat.mul_zero,
        Nat.add_zero, State.ofSpec_toSpec]
      rfl

/-- Replacing the low `t` bytes of `x` by those of `c` equals XORing in the
low `t` bytes of `x ⊕ c`. This is the identity behind `replace_low_bytes`. -/
theorem replace_low_eq (x c m : Word) :
    (x &&& ~~~m) ||| (c &&& m) = x ^^^ ((x ^^^ c) &&& m) := by bv_decide

theorem decryptTail_ok (Cx : List Byte) (st : State) (Pp : List Byte) (off : Nat)
    (hoff : off ≤ Cx.length) (hrem : Cx.length - off < 16) (hP : Pp.length = off) :
    let Plast := xorBytes ((Spec.Aead.rateBytes st.toSpec).take (Cx.length - off)) (Cx.drop off)
    decryptTail st (Bytes.ofList Cx) (Bytes.ofList Pp ++ List.replicate (Cx.length - off) none)
        off =
      .ok (State.ofSpec (Spec.Aead.xorRate st.toSpec (pad 16 Plast)), Bytes.ofList (Pp ++ Plast)) := by
  intro Plast
  unfold decryptTail
  have hr : Bytes.length (Bytes.ofList Cx) - (off : Int) = ((Cx.length - off : Nat) : Int) := by
    simp; omega
  rw [hr]
  have hPl : Plast.length = Cx.length - off := by
    simp [Plast, xorBytes, Spec.Aead.rateBytes, Spec.bytesLE_length]; omega
  by_cases h8 : 8 ≤ Cx.length - off
  · have hl0 := load64Le_at Cx off (by omega)
    have hlp := loadPartialLe_at Cx (off + 8) (Cx.length - off - 8) (by omega) (by omega)
    rw [show ((off + 8 : Nat) : Int) = (off : Int) + 8 by push_cast; rfl,
      show ((Cx.length - off - 8 : Nat) : Int) = ((Cx.length - off : Nat) : Int) - 8 by omega,
      List.take_of_length_le (show (Cx.drop (off + 8)).length ≤ Cx.length - off - 8 by
        simp; omega)] at hlp
    have hs0 := store64Le_at Pp (Cx.length - off)
      (st.x0 ^^^ wordLE ((Cx.drop off).take 8)) (by omega)
    rw [hP] at hs0
    have hsp := storePartialLe_at (Pp ++ bytesLE (st.x0 ^^^ wordLE ((Cx.drop off).take 8)))
      (Cx.length - off - 8) (st.x1 ^^^ wordLE (Cx.drop (off + 8))) (Cx.length - off - 8)
      (by omega) (Nat.le_refl _)
    rw [List.length_append, hP, Spec.bytesLE_length,
      show ((off + 8 : Nat) : Int) = (off : Int) + 8 by push_cast; rfl,
      show ((Cx.length - off - 8 : Nat) : Int) = ((Cx.length - off : Nat) : Int) - 8 by omega,
      Nat.sub_self, List.replicate_zero, List.append_nil] at hsp
    have hrl := Endian.replaceLowBytes_ok st.x1 (wordLE (Cx.drop (off + 8)))
      (Cx.length - off - 8) (by omega)
    rw [show ((Cx.length - off - 8 : Nat) : Int) = ((Cx.length - off : Nat) : Int) - 8 by
      omega] at hrl
    have hpd := Endian.padding_ok (Cx.length - off - 8) (by omega)
    rw [show ((Cx.length - off - 8 : Nat) : Int) = ((Cx.length - off : Nat) : Int) - 8 by
      omega] at hpd
    simp only [show ((Cx.length - off : Nat) : Int) ≥ 8 by omega, ↓reduceIte, hl0, hlp, ok_bind,
      hs0, hsp, hrl, hpd]
    -- The released plaintext block.
    have hPlast : Plast = bytesLE (st.x0 ^^^ wordLE ((Cx.drop off).take 8)) ++
        (bytesLE (st.x1 ^^^ wordLE (Cx.drop (off + 8)))).take (Cx.length - off - 8) := by
      simp only [Plast, take_rateBytes_long _ _ h8]
      rw [xorBytes_append_left _ _ _ (by simp [Spec.bytesLE_length]; omega), Spec.bytesLE_length,
        List.drop_drop, bytesLE_xor_eight _ _ (by simp; omega)]
      have := Spec.bytesLE_xor_wordLE_take st.x1 (Cx.drop (off + 8)) (by simp; omega)
      rw [show (Cx.drop (off + 8)).length = Cx.length - off - 8 by simp; omega] at this
      rw [this]
      rfl
    have hp := Spec.pad16_long Plast (by omega) (by omega)
    have ht8 : Plast.take 8 = xorBytes (bytesLE st.x0) ((Cx.drop off).take 8) := by
      rw [hPlast, List.take_append_of_le_length (by simp [Spec.bytesLE_length]),
        List.take_of_length_le (by simp [Spec.bytesLE_length]),
        bytesLE_xor_eight _ _ (by simp; omega)]
    have hd8 : Plast.drop 8 = xorBytes ((bytesLE st.x1).take (Cx.length - off - 8))
        (Cx.drop (off + 8)) := by
      rw [hPlast, List.drop_append_of_le_length (by simp [Spec.bytesLE_length]),
        List.drop_of_length_le (by simp [Spec.bytesLE_length]), List.nil_append]
      have := Spec.bytesLE_xor_wordLE_take st.x1 (Cx.drop (off + 8)) (by simp; omega)
      rwa [show (Cx.drop (off + 8)).length = Cx.length - off - 8 by simp; omega] at this
    have hw0 : wordLE (Plast.take 8) = st.x0 ^^^ wordLE ((Cx.drop off).take 8) := by
      rw [ht8, Spec.wordLE_xorBytes_eight _ _ (by simp; omega)]
    have hw1 : wordLE (Plast.drop 8) =
        (st.x1 ^^^ wordLE (Cx.drop (off + 8))) &&& Endian.lowMask (Cx.length - off - 8) := by
      rw [hd8]
      have := Spec.wordLE_xorBytes_take st.x1 (Cx.drop (off + 8)) (by simp; omega)
      rw [show (Cx.drop (off + 8)).length = Cx.length - off - 8 by simp; omega] at this
      rw [this]; rfl
    rw [List.append_assoc, ← hPlast]
    simp only [Spec.Aead.xorRate, hp, hw0, hw1, hPl]
    apply congrArg (fun x => (Except.ok x : M (State × Bytes)))
    simp only [State.ofSpec, State.toSpec, Prod.mk.injEq, State.mk.injEq, and_true]
    exact ⟨by bv_decide, by rw [replace_low_eq, BitVec.xor_assoc]⟩
  · have hlp := loadPartialLe_at Cx off (Cx.length - off) (by omega) (by omega)
    rw [List.take_of_length_le (show (Cx.drop off).length ≤ Cx.length - off by simp)] at hlp
    have hsp := storePartialLe_at Pp (Cx.length - off) (st.x0 ^^^ wordLE (Cx.drop off))
      (Cx.length - off) (by omega) (Nat.le_refl _)
    rw [hP, Nat.sub_self, List.replicate_zero, List.append_nil] at hsp
    have hrl := Endian.replaceLowBytes_ok st.x0 (wordLE (Cx.drop off)) (Cx.length - off)
      (by omega)
    simp only [show ¬ (((Cx.length - off : Nat) : Int) ≥ 8) by omega, ↓reduceIte, hlp, ok_bind,
      hsp, hrl, Endian.padding_ok _ (show Cx.length - off < 8 by omega)]
    have hPlast : Plast = (bytesLE (st.x0 ^^^ wordLE (Cx.drop off))).take (Cx.length - off) := by
      simp only [Plast, take_rateBytes_short _ _ (by omega : Cx.length - off ≤ 8)]
      have := Spec.bytesLE_xor_wordLE_take st.x0 (Cx.drop off) (by simp; omega)
      rw [show (Cx.drop off).length = Cx.length - off by simp] at this
      rw [this]; rfl
    have hp := Spec.pad16_short Plast (by omega)
    have hw : wordLE Plast = (st.x0 ^^^ wordLE (Cx.drop off)) &&& Endian.lowMask (Cx.length - off) := by
      simp only [Plast, take_rateBytes_short _ _ (by omega : Cx.length - off ≤ 8)]
      change wordLE (xorBytes (List.take (Cx.length - off) (bytesLE st.x0)) (List.drop off Cx)) = _
      have := Spec.wordLE_xorBytes_take st.x0 (Cx.drop off) (by simp; omega)
      rw [show (Cx.drop off).length = Cx.length - off by simp] at this
      rw [this]; rfl
    rw [← hPlast]
    simp only [Spec.Aead.xorRate, hp, hw, hPl]
    apply congrArg (fun x => (Except.ok x : M (State × Bytes)))
    simp only [State.ofSpec, State.toSpec, Prod.mk.injEq, State.mk.injEq, and_true]
    exact ⟨by rw [replace_low_eq, BitVec.xor_assoc], by bv_decide⟩

/-- The error of the specification, as the OCaml variant. -/
def DecryptError.ofSpec : Spec.Aead.DecryptError → DecryptError
  | .invalidTagLength => .invalidTagLength
  | .authenticationFailure => .authenticationFailure

/-- The OCaml result denoted by a specification result. -/
def decryptResult : Except Spec.Aead.DecryptError (List Byte) → Except DecryptError Bytes
  | .ok P => .ok (Bytes.ofList P)
  | .error e => .error (DecryptError.ofSpec e)

/-- Algorithm 4 with its pattern-matching `let`s replaced by projections. -/
theorem _root_.Ascon.Spec.Aead.decrypt_eq (K N A C T : List Byte) :
    Spec.Aead.decrypt K N A C T =
      if T.length ≠ 16 then .error .invalidTagLength
      else
        let S0 := Spec.Aead.processAD (Spec.Aead.init K N) A
        let R := Spec.Aead.decryptBlocks S0 (parse 16 C).1
        let Plast := xorBytes ((Spec.Aead.rateBytes R.1).take (parse 16 C).2.length) (parse 16 C).2
        let S := Spec.Aead.xorRate R.1 (pad 16 Plast)
        if Spec.Aead.finalize S K = T then .ok (R.2 ++ Plast)
        else .error .authenticationFailure := rfl

theorem Bytes.fill_ok (b : List (Option Byte)) (c : Byte) :
    ∃ r, Bytes.fill b 0 (Bytes.length b) c = .ok r := by
  unfold Bytes.fill
  rw [ite_eq_left (by simp [Bytes.validRange])]
  exact ⟨_, rfl⟩

/-- `Aead128.decrypt` is Ascon-AEAD128 decryption (SP 800-232, Algorithm 4):
plaintext is returned exactly when the full 128-bit tag matches, and tags of
any other length are rejected with `Invalid_tag_length`. -/
theorem decrypt_correct (K N A Cx T : List Byte) (hK : K.length = 16) (hN : N.length = 16)
    (hC : (Cx.length : Int) ≤ maxStringLength) :
    decrypt (Bytes.ofList K) (Bytes.ofList N) (Bytes.ofList A) (Bytes.ofList Cx)
        (Bytes.ofList T) =
      .ok (decryptResult (Spec.Aead.decrypt K N A Cx T)) := by
  rw [Spec.Aead.decrypt_eq]
  unfold decrypt
  by_cases hT : T.length = 16
  · have hTl : ¬ (Bytes.length (Bytes.ofList T) ≠ tagSize) := by simp [tagSize, hT]
    rw [ite_eq_right hTl, ite_eq_right (by simp [hT])]
    have hn := Spec.parse_rem_eq_drop (r := 16) Cx (by decide)
    have hj := Spec.parse_join (r := 16) Cx (by decide)
    have hfl := Spec.parse_flatten_length (r := 16) Cx (by decide)
    have hrl := Spec.parse_rem_length (r := 16) Cx (by decide)
    have hbl := Spec.parse_blocks_length (r := 16) Cx (by decide)
    have hlen : Cx.length = 16 * (parse 16 Cx).1.length + (parse 16 Cx).2.length := by
      rw [← hfl, ← List.length_append, hj]
    have hc : Bytes.create (Bytes.length (Bytes.ofList Cx)) =
        .ok (Bytes.ofList [] ++ List.replicate Cx.length none) := by
      simpa [Bytes.ofList] using Sponge.Bytes.create_ok Cx.length hC
    simp only [initialize_ok K N hK hN, ok_bind, absorbAssociatedData_ok, State.toSpec_ofSpec,
      hc]
    generalize Spec.Aead.processAD (Spec.Aead.init K N) A = S0
    have hloop := decryptLoop_ok Cx (State.ofSpec S0) [] 0 (Nat.zero_le _) rfl
    simp only [List.drop_zero, Nat.zero_add, Sponge.natCast_zero_int, List.nil_append,
      State.toSpec_ofSpec, Nat.sub_zero] at hloop
    have htail := decryptTail_ok Cx (State.ofSpec (Spec.Aead.decryptBlocks S0 (parse 16 Cx).1).1)
      (Spec.Aead.decryptBlocks S0 (parse 16 Cx).1).2 (16 * (parse 16 Cx).1.length) (by omega)
      (by omega) (decryptBlocks_length _ _ hbl)
    simp only [State.toSpec_ofSpec, ← hn] at htail
    rw [bind_of_ok hloop]
    simp only []
    rw [bind_of_ok htail]
    simp only [show Cx.length - 16 * (parse 16 Cx).1.length = (parse 16 Cx).2.length by omega]
    generalize hPl : xorBytes ((Spec.Aead.rateBytes (Spec.Aead.decryptBlocks S0 (parse 16 Cx).1).1).take
      (parse 16 Cx).2.length) (parse 16 Cx).2 = Plast
    have hfin := finalize_ok (State.ofSpec (Spec.Aead.xorRate
      (Spec.Aead.decryptBlocks S0 (parse 16 Cx).1).1 (pad 16 Plast))) K
    rw [State.toSpec_ofSpec] at hfin
    rw [bind_of_ok hfin, bind_of_ok (ConstantTime.equal_ok _ T)]
    by_cases heq : Spec.Aead.finalize (Spec.Aead.xorRate
        (Spec.Aead.decryptBlocks S0 (parse 16 Cx).1).1 (pad 16 Plast)) K = T
    · simp only [heq, decide_true, ↓reduceIte]
      rfl
    · simp only [heq, decide_false, Bool.false_eq_true, ↓reduceIte]
      obtain ⟨r, hr⟩ := Bytes.fill_ok (Bytes.ofList ((Spec.Aead.decryptBlocks S0
        (parse 16 Cx).1).2 ++ Plast)) 0
      have hlenP : Bytes.length (Bytes.ofList ((Spec.Aead.decryptBlocks S0
          (parse 16 Cx).1).2 ++ Plast)) = Bytes.length (Bytes.ofList Cx) := by
        simp only [Bytes.length_eq, Bytes.length_ofList, List.length_append,
          decryptBlocks_length _ _ hbl, ← hPl, xorBytes, List.length_zipWith, List.length_take,
          Spec.Aead.rateBytes, Spec.bytesLE_length]
        omega
      rw [← hlenP, bind_of_ok hr]
      rfl
  · have hTl : Bytes.length (Bytes.ofList T) ≠ tagSize := by simp [tagSize]; omega
    rw [ite_eq_left hTl, ite_eq_left (by simpa using hT)]
    rfl

theorem encrypt_lengths (K N A P : List Byte) :
    (Spec.Aead.encrypt K N A P).1.length = P.length ∧ (Spec.Aead.encrypt K N A P).2.length = 16 := by
  have hj := Spec.parse_join (r := 16) P (by decide)
  have hfl := Spec.parse_flatten_length (r := 16) P (by decide)
  have hrl := Spec.parse_rem_length (r := 16) P (by decide)
  have hlen : P.length = 16 * (parse 16 P).1.length + (parse 16 P).2.length := by
    rw [← hfl, ← List.length_append, hj]
  rw [Spec.Aead.encrypt_eq]
  simp only [List.length_append, encryptBlocks_length, List.length_take, Spec.Aead.rateBytes,
    Spec.bytesLE_length, Spec.Aead.finalize]
  exact ⟨by omega, trivial⟩

theorem Bytes.blit_into (src : List Byte) (dst : List (Option Byte)) (so d len : Nat)
    (hs : so + len ≤ src.length) (hd : d + len ≤ dst.length) :
    Bytes.blit (Bytes.ofList src) so dst d len =
      .ok (dst.take d ++ Bytes.ofList ((src.drop so).take len) ++ dst.drop (d + len)) := by
  unfold Bytes.blit
  rw [ite_eq_left (by simp only [Bytes.validRange, Bytes.length_eq, Bytes.length_ofList]; omega)]
  simp only [Int.toNat_natCast, show ((d : Int) + (len : Int)).toNat = d + len by omega,
    Bytes.ofList_take, Bytes.ofList_drop]
  rfl

theorem Bytes.sub_ok (X : List Byte) (off len : Nat) (h : off + len ≤ X.length) :
    Bytes.sub (Bytes.ofList X) off len = .ok (Bytes.ofList ((X.drop off).take len)) := by
  unfold Bytes.sub
  rw [ite_eq_left (by simp only [Bytes.validRange, Bytes.length_eq, Bytes.length_ofList]; omega)]
  simp only [Int.toNat_natCast, Bytes.ofList_take, Bytes.ofList_drop]
  rfl

/-- `encrypt_combined` returns `C ‖ T`. It raises `Invalid_argument` exactly when
`|P| + 16` exceeds `Sys.max_string_length`. -/
theorem encryptCombined_correct (K N A P : List Byte) (hK : K.length = 16) (hN : N.length = 16)
    (hP : (P.length : Int) ≤ maxStringLength) :
    encryptCombined (Bytes.ofList K) (Bytes.ofList N) (Bytes.ofList A) (Bytes.ofList P) =
      if (P.length : Int) > maxStringLength - 16 then
        .error (.invalidArgument "Ascon combined ciphertext is too long")
      else .ok (Bytes.ofList (Spec.Aead.encryptCombined K N A P)) := by
  unfold encryptCombined Spec.Aead.encryptCombined
  rw [bind_of_ok (encrypt_correct K N A P hK hN hP)]
  obtain ⟨hl1, hl2⟩ := encrypt_lengths K N A P
  generalize (Spec.Aead.encrypt K N A P).1 = C at hl1 ⊢
  generalize (Spec.Aead.encrypt K N A P).2 = T at hl2 ⊢
  simp only [Bytes.length_eq, Bytes.length_ofList, hl1, tagSize]
  by_cases hlong : (P.length : Int) > maxStringLength - 16
  · simp only [hlong, ↓reduceIte, invalidArg, throw, throwThe, MonadExceptOf.throw]
    rfl
  · simp only [hlong, ↓reduceIte]
    have hcr := Sponge.Bytes.create_ok (P.length + 16) (by omega)
    rw [show ((P.length + 16 : Nat) : Int) = (P.length : Int) + 16 by push_cast; rfl] at hcr
    rw [bind_of_ok hcr]
    have hb1 := Bytes.blit_into C (List.replicate (P.length + 16) none) 0 0 P.length
      (by omega) (by simp)
    simp only [Sponge.natCast_zero_int, List.take_zero, List.nil_append, List.drop_zero,
      List.take_of_length_le (show C.length ≤ P.length by omega), Nat.zero_add,
      List.drop_replicate, show P.length + 16 - P.length = 16 by omega] at hb1
    rw [bind_of_ok hb1]
    have hb2 := Bytes.blit_into T (Bytes.ofList C ++ List.replicate 16 none) 0 P.length 16
      (by omega) (by simp; omega)
    have hCl : List.length (Bytes.ofList C) = P.length := by simp [hl1]
    have e1 : List.take P.length (Bytes.ofList C ++ List.replicate 16 none) = Bytes.ofList C := by
      rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
    have e2 : List.take 16 (List.drop 0 T) = T := by
      rw [List.drop_zero, List.take_of_length_le (by omega)]
    have e3 : List.drop (P.length + 16) (Bytes.ofList C ++ List.replicate 16 none) = [] :=
      List.drop_of_length_le (by simp; omega)
    rw [e1, e2, e3, List.append_nil, Sponge.natCast_zero_int,
      show ((16 : Nat) : Int) = 16 from rfl] at hb2
    rw [hb2, Bytes.ofList_append]

/-- `decrypt_combined` splits `C ‖ T` and decrypts; inputs shorter than a tag
are rejected with `Invalid_tag_length`. -/
theorem decryptCombined_correct (K N A CT : List Byte) (hK : K.length = 16) (hN : N.length = 16)
    (hCT : (CT.length : Int) ≤ maxStringLength) :
    decryptCombined (Bytes.ofList K) (Bytes.ofList N) (Bytes.ofList A) (Bytes.ofList CT) =
      .ok (decryptResult (Spec.Aead.decryptCombined K N A CT)) := by
  unfold decryptCombined Spec.Aead.decryptCombined
  by_cases hs : CT.length < 16
  · rw [ite_eq_left (by simp [tagSize]; omega), ite_eq_left hs]
    rfl
  · rw [ite_eq_right (by simp [tagSize]; omega), ite_eq_right hs]
    have h1 := Bytes.sub_ok CT 0 (CT.length - 16) (by omega)
    have h2 := Bytes.sub_ok CT (CT.length - 16) 16 (by omega)
    rw [List.drop_zero, Sponge.natCast_zero_int,
      show ((CT.length - 16 : Nat) : Int) = Bytes.length (Bytes.ofList CT) - tagSize by
        simp [tagSize]; omega] at h1
    rw [List.take_of_length_le (show (CT.drop (CT.length - 16)).length ≤ 16 by simp; omega),
      show ((CT.length - 16 : Nat) : Int) = Bytes.length (Bytes.ofList CT) - tagSize by
        simp [tagSize]; omega, show ((16 : Nat) : Int) = tagSize from rfl] at h2
    simp only [bind_of_ok h1, bind_of_ok h2]
    exact decrypt_correct K N A _ _ hK hN (by simp; omega)

end Aead128
end Ascon.Model
