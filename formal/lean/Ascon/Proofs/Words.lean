import Ascon.Spec.Basic
import Std.Tactic.BVDecide

/-!
# Facts about little-endian words and byte blocks

Specification-level lemmas. Most statements concern a block of at most eight
bytes. They are proved by splitting on the block length and then applying
`bv_decide` to the resulting fixed-size bit-vector statement.
-/

namespace Ascon.Spec

/-- Case analysis on a list of at most eight elements. -/
@[elab_as_elim] theorem List.cases_le8 {α : Type} {P : List α → Prop} (xs : List α) (h : xs.length ≤ 8)
    (h0 : P []) (h1 : ∀ a, P [a]) (h2 : ∀ a b, P [a, b]) (h3 : ∀ a b c, P [a, b, c])
    (h4 : ∀ a b c d, P [a, b, c, d]) (h5 : ∀ a b c d e, P [a, b, c, d, e])
    (h6 : ∀ a b c d e f, P [a, b, c, d, e, f]) (h7 : ∀ a b c d e f g, P [a, b, c, d, e, f, g])
    (h8 : ∀ a b c d e f g i, P [a, b, c, d, e, f, g, i]) : P xs := by
  match xs, h with
  | [], _ => exact h0
  | [a], _ => exact h1 a
  | [a, b], _ => exact h2 a b
  | [a, b, c], _ => exact h3 a b c
  | [a, b, c, d], _ => exact h4 a b c d
  | [a, b, c, d, e], _ => exact h5 a b c d e
  | [a, b, c, d, e, f], _ => exact h6 a b c d e f
  | [a, b, c, d, e, f, g], _ => exact h7 a b c d e f g
  | [a, b, c, d, e, f, g, i], _ => exact h8 a b c d e f g i
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _, h => simp at h

/-- Split a list of length ≤ 8 into explicit elements, unfold the given
definitions, and finish with `bv_decide`. -/
macro "by_cases_le8" xs:term "," h:term "using" "[" defs:Lean.Parser.Tactic.simpLemma,* "]" :
    tactic =>
  `(tactic| (refine List.cases_le8 $xs $h ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> intros <;>
      simp only [$defs,*] <;> bv_decide))

@[simp] theorem wordLE_nil : wordLE [] = 0 := rfl

theorem wordLE_cons (b : Byte) (bs : List Byte) :
    wordLE (b :: bs) = b.setWidth 64 ||| (wordLE bs <<< 8) := rfl

/-- Accumulating bytes one at a time, as `load_partial_le` does. -/
theorem wordLE_append_single (ys : List Byte) (y : Byte) (h : ys.length < 8) :
    wordLE (ys ++ [y]) = wordLE ys ||| (y.setWidth 64 <<< (8 * ys.length)) := by
  revert y
  by_cases_le8 ys, (by omega : ys.length ≤ 8) using
    [wordLE, List.cons_append, List.nil_append, List.length_cons, List.length_nil]
  all_goals simp at h

theorem wordLE_replicate_zero (n : Nat) : wordLE (List.replicate n 0#8) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ, wordLE_cons, ih]; bv_decide

/-- Appending zero bytes does not change a word. -/
theorem wordLE_append_zeros (xs : List Byte) (n : Nat) :
    wordLE (xs ++ List.replicate n 0#8) = wordLE xs := by
  induction xs with
  | nil => simp [wordLE_replicate_zero]
  | cons x xs ih => simp only [List.cons_append, wordLE_cons, ih]

/-- The padded block of `r < 8` bytes: the `0x01` byte lands at bit `8r`. -/
theorem wordLE_pad8 (xs : List Byte) (h : xs.length < 8) :
    wordLE (pad 8 xs) = wordLE xs ^^^ (1#64 <<< (8 * xs.length)) := by
  unfold pad
  rw [List.append_assoc, show [1#8] ++ List.replicate (8 - 1 - xs.length) 0#8 =
    [1#8] ++ List.replicate (7 - xs.length) 0#8 by rfl]
  rw [← List.append_assoc, wordLE_append_zeros]
  by_cases_le8 xs, (by omega : xs.length ≤ 8) using
    [wordLE, List.cons_append, List.nil_append, List.length_cons, List.length_nil]
  all_goals simp at h

/-- A word read from at most eight bytes has no bits beyond them. -/
theorem wordLE_high_zero (xs : List Byte) (h : xs.length ≤ 8) :
    wordLE xs &&& ~~~((1#64 <<< (8 * xs.length)) - 1) = 0 ∨ xs.length = 8 := by
  by_cases h8 : xs.length = 8
  · exact .inr h8
  · left
    by_cases_le8 xs, h using
      [wordLE, List.length_cons, List.length_nil]
    all_goals simp at h8

theorem bytesLE_length (w : Word) : (bytesLE w).length = 8 := by simp [bytesLE]

/-- Storing a word and loading it back gives the word. -/
theorem wordLE_bytesLE (w : Word) : wordLE (bytesLE w) = w := by
  simp only [bytesLE, wordLE]
  bv_decide

/-- Loading eight bytes and storing them back gives the bytes. -/
theorem bytesLE_wordLE (xs : List Byte) (h : xs.length = 8) : bytesLE (wordLE xs) = xs := by
  match xs, h with
  | [a, b, c, d, e, f, g, i], _ =>
    simp only [bytesLE, wordLE, List.cons.injEq,
      and_true]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> bv_decide

/-- The first `n` bytes of a word read from `n ≤ 8` bytes are those bytes. -/
theorem bytesLE_wordLE_take (xs : List Byte) (h : xs.length ≤ 8) :
    (bytesLE (wordLE xs)).take xs.length = xs := by
  by_cases_le8 xs, h using
    [bytesLE, wordLE, List.take, List.length_cons,
      List.length_nil, List.cons.injEq, and_true]

/-- Bits at or above byte `r` do not affect the first `r` bytes. -/
theorem bytesLE_xor_high_take (w v : Word) (r : Nat) (hr : r ≤ 8)
    (hv : v &&& ((1#64 <<< (8 * r)) - 1) = 0) :
    (bytesLE (w ^^^ v)).take r = (bytesLE w).take r := by
  have : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 ∨ r = 7 ∨ r = 8 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp only [bytesLE, List.take, List.cons.injEq,
    and_true] <;> simp only [Nat.reduceMul] at hv <;>
  (try constructor) <;> (try constructor) <;> (try constructor) <;> (try constructor) <;>
  (try constructor) <;> (try constructor) <;> (try constructor) <;> bv_decide

/-- The first `r` bytes of `w ⊕ wordLE xs` are the byte-wise XOR. -/
theorem bytesLE_xor_wordLE_take (w : Word) (xs : List Byte) (h : xs.length ≤ 8) :
    (bytesLE (w ^^^ wordLE xs)).take xs.length = xorBytes ((bytesLE w).take xs.length) xs := by
  revert w
  by_cases_le8 xs, h using
    [bytesLE, wordLE, List.take, List.length_cons,
      List.length_nil, xorBytes, List.zipWith, List.cons.injEq, and_true]

/-- Loading a byte-wise XOR of the low bytes of `w` with `xs`: the word equals
`(w ⊕ wordLE xs)` restricted to the low `|xs|` bytes. -/
theorem wordLE_xorBytes_take (w : Word) (xs : List Byte) (h : xs.length < 8) :
    wordLE (xorBytes ((bytesLE w).take xs.length) xs) =
      (w ^^^ wordLE xs) &&& ((1#64 <<< (8 * xs.length)) - 1) := by
  revert w
  by_cases_le8 xs, (by omega : xs.length ≤ 8) using
    [bytesLE, wordLE, List.take, List.length_cons,
      List.length_nil, xorBytes, List.zipWith]
  all_goals simp at h

theorem wordLE_xorBytes_eight (w : Word) (xs : List Byte) (h : xs.length = 8) :
    wordLE (xorBytes (bytesLE w) xs) = w ^^^ wordLE xs := by
  match xs, h with
  | [a, b, c, d, e, f, g, i], _ =>
    simp only [bytesLE, wordLE, xorBytes, List.zipWith]
    bv_decide

end Ascon.Spec
