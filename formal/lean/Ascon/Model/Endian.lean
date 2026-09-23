import Ascon.Model.Runtime

/-! # Model of `lib/internal/endian.ml` and `lib/internal/constant_time.ml` -/

namespace Ascon.Model

namespace Endian

/-- `byte b i`. -/
def byte (b : Bytes) (i : Int) : M Word := do
  pure (Int64.ofInt (Char.code (← Bytes.unsafeGet b i)))

/-- `load_partial_le b off len`. -/
def loadPartialLe (b : Bytes) (off len : Int) : M Word := do
  if off < 0 ∨ len < 0 ∨ len > 8 ∨ off > b.length - len then
    invalidArg "Ascon internal little-endian load"
  forUp 0 (len - 1) (0 : Word) fun i x => do
    pure (x ||| (← Int64.shiftLeft (← byte b (off + i)) (8 * i)))

/-- `load64_le b off`. -/
def load64Le (b : Bytes) (off : Int) : M Word := loadPartialLe b off 8

/-- `store_partial_le b off x len`. -/
def storePartialLe (b : Bytes) (off : Int) (x : Word) (len : Int) : M Bytes := do
  if off < 0 ∨ len < 0 ∨ len > 8 ∨ off > b.length - len then
    invalidArg "Ascon internal little-endian store"
  forUp 0 (len - 1) b fun i b => do
    Bytes.unsafeSet b (off + i)
      (← Char.chr (Int64.toInt ((← Int64.shiftRightLogical x (8 * i)) &&& 0xff)))

/-- `store64_le b off x`. -/
def store64Le (b : Bytes) (off : Int) (x : Word) : M Bytes := storePartialLe b off x 8

/-- `padding i`. -/
def padding (i : Int) : M Word := do
  if i < 0 ∨ i > 7 then invalidArg "Ascon internal padding position"
  Int64.shiftLeft 1 (8 * i)

/-- `replace_low_bytes old replacement len`. -/
def replaceLowBytes (old replacement : Word) (len : Int) : M Word := do
  if len < 0 ∨ len > 8 then invalidArg "Ascon internal byte replacement"
  if len = 8 then pure replacement
  else
    let lowMask := (← Int64.shiftLeft 1 (8 * len)) - 1
    pure ((old &&& ~~~lowMask) ||| (replacement &&& lowMask))

end Endian

namespace ConstantTime

/-- `equal a b`. OCaml `int` values here are always in `[0, 255]`, so they are
modelled as natural numbers with `lor` / `lxor`. -/
def equal (a b : Bytes) : M Bool := do
  let len := a.length
  if len ≠ b.length then pure false
  else
    let difference ← forUp 0 (len - 1) (0 : Nat) fun i difference => do
      let x ← Bytes.unsafeGet a i
      let y ← Bytes.unsafeGet b i
      pure (difference ||| (x.toNat ^^^ y.toNat))
    pure (difference = 0)

end ConstantTime
end Ascon.Model
