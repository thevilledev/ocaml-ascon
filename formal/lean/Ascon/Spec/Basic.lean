/-!
# SP 800-232 notation for byte-oriented inputs

This file fixes the notation used by the executable specification. It follows
NIST SP 800-232 (August 2025), restricted to inputs whose lengths are whole
bytes, which is the only case the OCaml library accepts.

* The 320-bit state `S` is five 64-bit words `S = S₀ ‖ S₁ ‖ S₂ ‖ S₃ ‖ S₄`.
* Byte strings are mapped to words in little-endian order: byte `i` of a block
  occupies bits `8i … 8i+7` of its word, so the first byte of a message is the
  least significant byte of `S₀`.
* With that bit order, `pad(X, r) = X ‖ 1 ‖ 0ʲ` appends the byte `0x01`
  followed by zero bytes when `X` is byte aligned.
* `parse(X, r)` returns the full `r`-bit blocks of `X` followed by one final,
  possibly empty, block shorter than `r`.

Nothing in this directory refers to the implementation model.
-/

namespace Ascon.Spec

abbrev Byte := BitVec 8
abbrev Word := BitVec 64

/-- The 320-bit Ascon state as five 64-bit words. -/
structure State where
  s0 : Word
  s1 : Word
  s2 : Word
  s3 : Word
  s4 : Word
deriving DecidableEq, Repr, Inhabited

/-- Little-endian word of at most eight bytes: the first byte is least significant. -/
def wordLE : List Byte → Word
  | [] => 0
  | b :: bs => b.setWidth 64 ||| (wordLE bs <<< 8)

/-- The eight little-endian bytes of a word. -/
def bytesLE (w : Word) : List Byte :=
  [w.extractLsb' 0 8, w.extractLsb' 8 8, w.extractLsb' 16 8, w.extractLsb' 24 8,
   w.extractLsb' 32 8, w.extractLsb' 40 8, w.extractLsb' 48 8, w.extractLsb' 56 8]

/-- `pad(X, r)` for a byte string `X` shorter than the rate of `r` bytes. -/
def pad (r : Nat) (X : List Byte) : List Byte :=
  X ++ [1#8] ++ List.replicate (r - 1 - X.length) 0#8

/-- `parse(X, r)`: the full `r`-byte blocks of `X`, and the final block
(`0 ≤ |final| < r`). -/
def parse (r : Nat) (X : List Byte) : List (List Byte) × List Byte :=
  if _h : r = 0 ∨ X.length < r then ([], X)
  else
    let rest := parse r (X.drop r)
    (X.take r :: rest.1, rest.2)
termination_by X.length
decreasing_by simp only [List.length_drop]; omega

/-- The blocks absorbed for `X`: all full blocks followed by `pad` of the final block. -/
def paddedBlocks (r : Nat) (X : List Byte) : List (List Byte) :=
  (parse r X).1 ++ [pad r (parse r X).2]

/-- Split a 16-byte block into its two 64-bit little-endian words. -/
def words128 (B : List Byte) : Word × Word :=
  (wordLE (B.take 8), wordLE (B.drop 8))

/-- Byte-wise exclusive or. -/
def xorBytes (X Y : List Byte) : List Byte :=
  List.zipWith (· ^^^ ·) X Y

end Ascon.Spec
