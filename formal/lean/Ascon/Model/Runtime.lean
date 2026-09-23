/-!
# A model of the OCaml runtime features used by `lib/`

The implementation model in `Ascon.Model.*` transcribes the OCaml sources
statement by statement on top of these definitions.

* OCaml `int` is modelled by `Int`. Every intermediate value in the library is
  bounded by an input length plus a small constant, so none of them comes near
  `max_int` on 63-bit or 31-bit runtimes.
* OCaml `int64` is modelled by `BitVec 64`. `Int64.logand`, `logor`, `logxor`,
  `lognot` and `sub` are exactly the two's-complement bit-vector operations.
* OCaml `bytes` is modelled by `List (Option Byte)`. `none` is a byte with
  unspecified contents, as returned by `Bytes.create`.
* Everything that raises `Invalid_argument` becomes a `Fault`, and so does
  every operation whose behaviour OCaml leaves undefined or unspecified.
  `Bytes.unsafe_get` and `Bytes.unsafe_set` out of bounds, reading a byte
  that was never initialized, and `Int64` shifts by amounts outside `[0, 63]`
  are all faults.

A proof that a model function returns `.ok` therefore also proves that the
OCaml code raises no exception, performs no out-of-bounds unsafe access, and
executes no shift with an unspecified result.
-/

namespace Ascon.Model

abbrev Byte := BitVec 8
abbrev Word := BitVec 64

inductive Fault where
  | invalidArgument (message : String)
  | outOfBounds
  | uninitializedRead
  | unspecifiedShift
  | loopBound
deriving Repr, DecidableEq, Inhabited

abbrev M := Except Fault

/-- OCaml `invalid_arg`. -/
def invalidArg (message : String) : M α := throw (.invalidArgument message)

/-- `Sys.max_string_length` on 64-bit runtimes. -/
def maxStringLength : Int := 144115188075855863

/-- OCaml `bytes`. -/
abbrev Bytes := List (Option Byte)

namespace Bytes

def ofList (l : List Byte) : Bytes := l.map some

def length (b : Bytes) : Int := List.length b

/-- `Bytes.create n`: `n` bytes with unspecified contents. -/
def create (n : Int) : M Bytes :=
  if n < 0 ∨ n > maxStringLength then invalidArg "Bytes.create"
  else pure (List.replicate n.toNat none)

/-- `Bytes.make n c`. -/
def make (n : Int) (c : Byte) : M Bytes :=
  if n < 0 ∨ n > maxStringLength then invalidArg "Bytes.make"
  else pure (List.replicate n.toNat (some c))

/-- `Bytes.copy` (a fresh object with the same contents). -/
def copy (b : Bytes) : Bytes := b

/-- `Bytes.unsafe_get`. -/
def unsafeGet (b : Bytes) (i : Int) : M Byte :=
  if h : 0 ≤ i ∧ i < b.length then
    match b[i.toNat]'(by simp only [length] at h; omega) with
    | some c => pure c
    | none => throw .uninitializedRead
  else throw .outOfBounds

/-- `Bytes.unsafe_set`. -/
def unsafeSet (b : Bytes) (i : Int) (c : Byte) : M Bytes :=
  if 0 ≤ i ∧ i < b.length then pure (b.set i.toNat (some c)) else throw .outOfBounds

/-- `(off, len)` designates a valid range of `b`. -/
def validRange (b : Bytes) (off len : Int) : Prop :=
  0 ≤ off ∧ 0 ≤ len ∧ off ≤ b.length - len

instance : Decidable (validRange b off len) := by unfold validRange; infer_instance

/-- `Bytes.blit src srcoff dst dstoff len`. -/
def blit (src : Bytes) (srcoff : Int) (dst : Bytes) (dstoff len : Int) : M Bytes :=
  if validRange src srcoff len ∧ validRange dst dstoff len then
    pure (dst.take dstoff.toNat ++ (src.drop srcoff.toNat).take len.toNat ++
      dst.drop (dstoff + len).toNat)
  else invalidArg "Bytes.blit"

/-- `Bytes.sub b off len`. -/
def sub (b : Bytes) (off len : Int) : M Bytes :=
  if validRange b off len then pure ((b.drop off.toNat).take len.toNat)
  else invalidArg "Bytes.sub"

/-- `Bytes.fill b off len c`. -/
def fill (b : Bytes) (off len : Int) (c : Byte) : M Bytes :=
  if validRange b off len then
    pure (b.take off.toNat ++ List.replicate len.toNat (some c) ++ b.drop (off + len).toNat)
  else invalidArg "Bytes.fill"

end Bytes

namespace Int64

/-- `Int64.shift_left`: unspecified unless `0 ≤ n < 64`. -/
def shiftLeft (x : Word) (n : Int) : M Word :=
  if 0 ≤ n ∧ n < 64 then pure (x <<< n.toNat) else throw .unspecifiedShift

/-- `Int64.shift_right_logical`: unspecified unless `0 ≤ n < 64`. -/
def shiftRightLogical (x : Word) (n : Int) : M Word :=
  if 0 ≤ n ∧ n < 64 then pure (x >>> n.toNat) else throw .unspecifiedShift

/-- `Int64.of_int` on a 63-bit runtime (sign extension). -/
def ofInt (n : Int) : Word := BitVec.ofInt 64 n

/-- `Int64.to_int` on a 63-bit runtime: keeps the low 63 bits, signed. -/
def toInt (x : Word) : Int := (x.setWidth 63).toInt

/-- `Int64.min_int`. -/
def minInt : Word := 1#64 <<< 63

end Int64

/-- `Char.code`. -/
def Char.code (c : Byte) : Int := c.toNat

/-- `Char.chr`: raises `Invalid_argument` outside `[0, 255]`. -/
def Char.chr (n : Int) : M Byte :=
  if 0 ≤ n ∧ n < 256 then pure (BitVec.ofNat 8 n.toNat) else invalidArg "Char.chr"

/-- `for i = lo to hi do body done`. -/
def forUp (lo hi : Int) (s : σ) (body : Int → σ → M σ) : M σ :=
  if lo ≤ hi then do
    let s ← body lo s
    forUp (lo + 1) hi s body
  else pure s
termination_by (hi + 1 - lo).toNat

end Ascon.Model
