import Ascon.Model.Runtime

/-!
# Model of `lib/internal/state.ml` and `lib/internal/permutation.ml`

The mutable OCaml record is modelled as a value. Each field assignment becomes
a record update, and each function returns the updated state. Aliasing between
mutable states is outside this functional model; the TLA+ heap model in
`formal/tla/` covers it.
-/

namespace Ascon.Model

/-- `State.t`. -/
structure State where
  x0 : Word
  x1 : Word
  x2 : Word
  x3 : Word
  x4 : Word
deriving DecidableEq, Repr, Inhabited

/-- `State.create`. -/
def State.create (x0 x1 x2 x3 x4 : Word) : State := ⟨x0, x1, x2, x3, x4⟩

/-- `State.copy`. -/
def State.copy (s : State) : State := ⟨s.x0, s.x1, s.x2, s.x3, s.x4⟩

namespace Permutation

/-- `round_constants`. -/
def roundConstants : Array Word :=
  #[0xf0, 0xe1, 0xd2, 0xc3, 0xb4, 0xa5, 0x96, 0x87, 0x78, 0x69, 0x5a, 0x4b]

/-- `Array.unsafe_get` on the constant table. -/
def constant (i : Int) : M Word :=
  if h : 0 ≤ i ∧ i < roundConstants.size then pure (roundConstants[i.toNat]'(by omega))
  else throw .outOfBounds

/-- `ror x n`. -/
def ror (x : Word) (n : Int) : M Word := do
  let a ← Int64.shiftRightLogical x n
  let b ← Int64.shiftLeft x (64 - n)
  pure (a ||| b)

/-- `round s c`. -/
def round (s : State) (c : Word) : M State := do
  -- Constant addition to the least significant byte of S2.
  let s := { s with x2 := s.x2 ^^^ c }
  -- The bitsliced five-bit substitution layer from SP 800-232, Fig. 3.
  let s := { s with x0 := s.x0 ^^^ s.x4 }
  let s := { s with x4 := s.x4 ^^^ s.x3 }
  let s := { s with x2 := s.x2 ^^^ s.x1 }
  let t0 := s.x0 ^^^ (~~~s.x1 &&& s.x2)
  let t1 := s.x1 ^^^ (~~~s.x2 &&& s.x3)
  let t2 := s.x2 ^^^ (~~~s.x3 &&& s.x4)
  let t3 := s.x3 ^^^ (~~~s.x4 &&& s.x0)
  let t4 := s.x4 ^^^ (~~~s.x0 &&& s.x1)
  let t1 := t1 ^^^ t0
  let t0 := t0 ^^^ t4
  let t3 := t3 ^^^ t2
  let t2 := ~~~t2
  -- Per-word linear diffusion.
  let s := { s with x0 := t0 ^^^ ((← ror t0 19) ^^^ (← ror t0 28)) }
  let s := { s with x1 := t1 ^^^ ((← ror t1 61) ^^^ (← ror t1 39)) }
  let s := { s with x2 := t2 ^^^ ((← ror t2 1) ^^^ (← ror t2 6)) }
  let s := { s with x3 := t3 ^^^ ((← ror t3 10) ^^^ (← ror t3 17)) }
  let s := { s with x4 := t4 ^^^ ((← ror t4 7) ^^^ (← ror t4 41)) }
  pure s

/-- `rounds s n`. -/
def rounds (s : State) (n : Int) : M State := do
  if n < 1 ∨ n > 12 then invalidArg "Ascon permutation round count"
  forUp (12 - n) 11 s fun i s => do round s (← constant i)

def p12 (s : State) : M State := rounds s 12
def p8 (s : State) : M State := rounds s 8

end Permutation
end Ascon.Model
