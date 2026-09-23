import Ascon.Spec.Basic

/-! # Properties of `parse` -/

namespace Ascon.Spec

variable {r : Nat}

/-- Strong induction on the length of a list. -/
theorem list_len_induction {α : Type} {P : List α → Prop}
    (h : ∀ X, (∀ Y : List α, Y.length < X.length → P Y) → P X) (X : List α) : P X := by
  suffices H : ∀ n, ∀ X : List α, X.length = n → P X from H _ X rfl
  intro n
  induction n using Nat.strongRecOn with
  | ind n ihn => intro X hX; exact h X (fun Y hY => ihn Y.length (hX ▸ hY) Y rfl)

theorem parse_short (X : List Byte) (h : X.length < r) : parse r X = ([], X) := by
  rw [parse]; simp [h]

theorem parse_long (X : List Byte) (hr : 0 < r) (h : r ≤ X.length) :
    parse r X = (X.take r :: (parse r (X.drop r)).1, (parse r (X.drop r)).2) := by
  rw [parse]; simp [show ¬ (r = 0 ∨ X.length < r) by omega]

theorem parse_block_append (B Y : List Byte) (hr : 0 < r) (hB : B.length = r) :
    parse r (B ++ Y) = (B :: (parse r Y).1, (parse r Y).2) := by
  rw [parse_long _ hr (by simp; omega)]
  simp [List.take_append_of_le_length (by omega : r ≤ B.length),
    List.drop_append_of_le_length (by omega : r ≤ B.length),
    List.take_of_length_le (by omega : B.length ≤ r), List.drop_of_length_le (by omega : B.length ≤ r)]

theorem parse_rem_length (X : List Byte) (hr : 0 < r) : (parse r X).2.length < r := by
  induction X using list_len_induction with
  | h X ih =>
    by_cases h : X.length < r
    · rw [parse_short X h]; exact h
    · rw [parse_long X hr (by omega)]
      exact ih _ (by simp; omega)

theorem parse_blocks_length (X : List Byte) (hr : 0 < r) :
    ∀ B ∈ (parse r X).1, B.length = r := by
  induction X using list_len_induction with
  | h X ih =>
    by_cases h : X.length < r
    · rw [parse_short X h]; simp
    · rw [parse_long X hr (by omega)]
      intro B hB
      simp only [List.mem_cons] at hB
      rcases hB with rfl | hB
      · simp; omega
      · exact ih _ (by simp; omega) B hB

/-- Full blocks followed by the final block give back `X`. -/
theorem parse_join (X : List Byte) (hr : 0 < r) : (parse r X).1.flatten ++ (parse r X).2 = X := by
  induction X using list_len_induction with
  | h X ih =>
    by_cases h : X.length < r
    · rw [parse_short X h]; simp
    · rw [parse_long X hr (by omega)]
      simp only [List.flatten_cons, List.append_assoc]
      rw [ih _ (by simp; omega), List.take_append_drop]

theorem parse_rem_eq_drop (X : List Byte) (hr : 0 < r) :
    (parse r X).2 = X.drop (r * (parse r X).1.length) := by
  induction X using list_len_induction with
  | h X ih =>
    by_cases h : X.length < r
    · rw [parse_short X h]; simp
    · rw [parse_long X hr (by omega)]
      simp only [List.length_cons, Nat.mul_add, Nat.mul_one]
      rw [ih _ (by simp; omega), List.drop_drop]
      congr 1; omega

theorem parse_flatten_length (X : List Byte) (hr : 0 < r) :
    (parse r X).1.flatten.length = r * (parse r X).1.length := by
  have h := parse_blocks_length X hr
  generalize (parse r X).1 = bs at h ⊢
  induction bs with
  | nil => simp
  | cons b bs ih =>
    simp only [List.flatten_cons, List.length_append, List.length_cons, Nat.mul_add, Nat.mul_one]
    rw [h b (by simp), ih (fun B hB => h B (by simp [hB]))]
    omega

/-- Absorbing more data only changes what comes after the old full blocks. -/
theorem parse_append (X Y : List Byte) (hr : 0 < r) :
    parse r (X ++ Y) =
      ((parse r X).1 ++ (parse r ((parse r X).2 ++ Y)).1, (parse r ((parse r X).2 ++ Y)).2) := by
  induction X using list_len_induction with
  | h X ih =>
    by_cases h : X.length < r
    · rw [parse_short X h]; simp
    · have hlong := parse_long X hr (by omega)
      rw [hlong, parse_long (X ++ Y) hr (by simp; omega)]
      simp only [List.take_append_of_le_length (by omega : r ≤ X.length),
        List.drop_append_of_le_length (by omega : r ≤ X.length), List.cons_append]
      rw [ih _ (by simp; omega)]

theorem parse_nil : parse r [] = ([], []) := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · rw [parse]; simp
  · exact parse_short [] (by simpa using hr)

end Ascon.Spec
