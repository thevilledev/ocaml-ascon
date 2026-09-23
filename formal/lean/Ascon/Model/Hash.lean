import Ascon.Model.Sponge

/-!
# Model of `Hash256`, `Xof128` and `Cxof128` in `lib/ascon.ml`

OCaml `result` values are modelled with `Except`, nested inside the fault
monad `M`: a successful model run returns `.ok (.ok v)` or `.ok (.error e)`.
-/

namespace Ascon.Model

open Permutation

namespace Hash256

def digestSize : Int := 32
def iv : Word := 0x0000080100cc0002
def init : M Sponge.Absorbing := Sponge.init iv
def feed (context : Sponge.Absorbing) (input : Bytes) : M Sponge.Absorbing :=
  Sponge.absorb context input

def get (context : Sponge.Absorbing) : M Bytes := do
  let squeezing ← Sponge.finish context
  pure (← Sponge.squeeze squeezing digestSize).2

def digest (input : Bytes) : M Bytes := do get (← feed (← init) input)

end Hash256

inductive InvalidLength where
  | invalidLength
deriving DecidableEq, Repr

namespace Xof128

def iv : Word := 0x0000080000cc0003
def init : M Sponge.Absorbing := Sponge.init iv
def absorb := Sponge.absorb
def startSqueezing := Sponge.finish

def validLength (length : Int) : Bool := length ≥ 0 ∧ length ≤ maxStringLength
def validDigestLength (length : Int) : Bool := length > 0 ∧ length ≤ maxStringLength

def squeeze (state : Sponge.Squeezing) (length : Int) :
    M (Except InvalidLength (Sponge.Squeezing × Bytes)) := do
  if validLength length then pure (.ok (← Sponge.squeeze state length))
  else pure (.error .invalidLength)

def digest (input : Bytes) (length : Int) : M (Except InvalidLength Bytes) := do
  if !validDigestLength length then pure (.error .invalidLength)
  else
    let state ← startSqueezing (← absorb (← init) input)
    pure (.ok (← Sponge.squeeze state length).2)

end Xof128

inductive CxofError where
  | customizationTooLong
  | invalidLength
deriving DecidableEq, Repr

namespace Cxof128

def iv : Word := 0x0000080000cc0004

/-- `init`, lines 230–236 of `ascon.ml`: the permuted IV with the
customization bit length `Z₀` absorbed. -/
def customizedState (length : Int) : M State := do
  let initialState := State.create iv 0 0 0 0
  let initialState ← p12 initialState
  let initialState := { initialState with
    x0 := initialState.x0 ^^^ Int64.ofInt (length * 8) }
  p12 initialState

/-- `init ~customization`. -/
def init (customization : Bytes) : M (Except CxofError Sponge.Absorbing) := do
  let length := customization.length
  if length > 256 then pure (.error .customizationTooLong)
  else
    let initialState ← customizedState length
    let customizationContext ← Sponge.ofState initialState
    let customizationState ←
      Sponge.finishState (← Sponge.absorb customizationContext customization)
    pure (.ok (← Sponge.ofState customizationState))

def absorb := Sponge.absorb
def startSqueezing := Sponge.finish
def validLength (length : Int) : Bool := length ≥ 0 ∧ length ≤ maxStringLength
def validDigestLength (length : Int) : Bool := length > 0 ∧ length ≤ maxStringLength

def squeeze (state : Sponge.Squeezing) (length : Int) :
    M (Except InvalidLength (Sponge.Squeezing × Bytes)) := do
  if validLength length then pure (.ok (← Sponge.squeeze state length))
  else pure (.error .invalidLength)

def digest (customization message : Bytes) (length : Int) : M (Except CxofError Bytes) := do
  if !validDigestLength length then pure (.error .invalidLength)
  else
    match ← init customization with
    | .error _ => pure (.error .customizationTooLong)
    | .ok state =>
      let state ← startSqueezing (← absorb state message)
      pure (.ok (← Sponge.squeeze state length).2)

end Cxof128
end Ascon.Model
