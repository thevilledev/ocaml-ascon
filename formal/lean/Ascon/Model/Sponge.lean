import Ascon.Model.Permutation
import Ascon.Model.Endian

/-!
# Model of `lib/internal/sponge.ml`

`absorb` transcribes the OCaml statements in order. Its `while` loop becomes
`absorbLoop`. The `squeeze` loop is `squeezeLoop`, which carries an explicit
iteration budget of `length + 1`: running out of budget is the fault
`loopBound`, so `squeeze_correct` also proves the loop terminates.
-/

namespace Ascon.Model.Sponge

open Permutation

/-- `absorbing`. -/
structure Absorbing where
  state : State
  buffer : Bytes
  buffered : Int

/-- `squeezing`. -/
structure Squeezing where
  state : State
  offset : Int

/-- `of_state state`. -/
def ofState (state : State) : M Absorbing := do
  pure { state := State.copy state, buffer := (← Bytes.make 8 0), buffered := 0 }

/-- `init ~iv`. -/
def init (iv : Word) : M Absorbing := do
  let state := State.create iv 0 0 0 0
  let state ← p12 state
  ofState state

/-- `absorb_block state block off`. -/
def absorbBlock (state : State) (block : Bytes) (off : Int) : M State := do
  let state := { state with x0 := state.x0 ^^^ (← Endian.load64Le block off) }
  p12 state

/-- `while input_length - !input_offset >= 8 do … done`. -/
def absorbLoop (state : State) (input : Bytes) (inputOffset : Int) : M (State × Int) :=
  if input.length - inputOffset ≥ 8 then do
    let state ← absorbBlock state input inputOffset
    absorbLoop state input (inputOffset + 8)
  else pure (state, inputOffset)
termination_by (input.length - inputOffset).toNat

/-- `absorb`, lines 24–31 of `sponge.ml`: complete a pending partial block
from the start of the input. Returns `(state, buffer, buffered, input_offset)`. -/
def fillPending (state : State) (buffer : Bytes) (buffered : Int) (input : Bytes) :
    M (State × Bytes × Int × Int) :=
  if buffered ≠ 0 then do
    let take := min (8 - buffered) input.length
    let buffer ← Bytes.blit input 0 buffer buffered take
    let buffered := buffered + take
    let inputOffset := take
    if buffered = 8 then do
      let state ← absorbBlock state buffer 0
      pure (state, buffer, 0, inputOffset)
    else pure (state, buffer, buffered, inputOffset)
  else pure (state, buffer, buffered, 0)

/-- `absorb`, lines 36–39 of `sponge.ml`: keep the trailing partial block. -/
def keepRemainder (input : Bytes) (inputOffset : Int) (buffer : Bytes) (buffered : Int) :
    M (Bytes × Int) :=
  let remaining := input.length - inputOffset
  if remaining ≠ 0 then do
    let buffer ← Bytes.blit input inputOffset buffer 0 remaining
    pure (buffer, remaining)
  else pure (buffer, buffered)

/-- `absorb context input`. -/
def absorb (context : Absorbing) (input : Bytes) : M Absorbing := do
  let state := State.copy context.state
  let buffer := Bytes.copy context.buffer
  let (state, buffer, buffered, inputOffset) ←
    fillPending state buffer context.buffered input
  let (state, inputOffset) ← absorbLoop state input inputOffset
  let (buffer, buffered) ← keepRemainder input inputOffset buffer buffered
  pure { state, buffer, buffered }

/-- `squeezing_of_state state`. -/
def squeezingOfState (state : State) : Squeezing := { state := State.copy state, offset := 0 }

/-- `finish_state context`. -/
def finishState (context : Absorbing) : M State := do
  let state := State.copy context.state
  let state := { state with
    x0 := state.x0 ^^^ (← Endian.loadPartialLe context.buffer 0 context.buffered) }
  let state := { state with x0 := state.x0 ^^^ (← Endian.padding context.buffered) }
  p12 state

/-- `finish context`. -/
def finish (context : Absorbing) : M Squeezing := do
  pure (squeezingOfState (← finishState context))

/-- The body of the `for i = 0 to take - 1` loop in `squeeze`. -/
def squeezeByte (x0 : Word) (offset written : Int) (i : Int) (output : Bytes) : M Bytes := do
  let shift := 8 * (offset + i)
  Bytes.unsafeSet output (written + i)
    (← Char.chr (Int64.toInt ((← Int64.shiftRightLogical x0 shift) &&& 0xff)))

/-- `while !written < length do … done`, with an iteration budget. -/
def squeezeLoop (fuel : Nat) (state : State) (offset : Int) (output : Bytes) (written length : Int) :
    M (State × Int × Bytes × Int) :=
  match fuel with
  | 0 => if written < length then throw .loopBound else pure (state, offset, output, written)
  | fuel + 1 =>
    if written < length then do
      let take := min (8 - offset) (length - written)
      let output ← forUp 0 (take - 1) output (squeezeByte state.x0 offset written)
      let written := written + take
      let offset := offset + take
      let (state, offset) ← if offset = 8 then do pure ((← p12 state), (0 : Int))
        else pure (state, offset)
      squeezeLoop fuel state offset output written length
    else pure (state, offset, output, written)

/-- `squeeze context length`. -/
def squeeze (context : Squeezing) (length : Int) : M (Squeezing × Bytes) := do
  if length < 0 ∨ length > maxStringLength then invalidArg "Ascon XOF output length"
  let state := State.copy context.state
  let offset := context.offset
  let output ← Bytes.create length
  let written : Int := 0
  let (state, offset, output, _) ←
    squeezeLoop (length.toNat + 1) state offset output written length
  pure ({ state, offset }, output)

end Ascon.Model.Sponge
