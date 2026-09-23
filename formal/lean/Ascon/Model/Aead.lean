import Ascon.Model.Permutation
import Ascon.Model.Endian

/-!
# Model of `Aead128` in `lib/ascon.ml`

Each `while` loop is a recursive function (`adLoop`, `encryptLoop`,
`decryptLoop`). The code after each loop, which handles the final block, is a
separate function (`adTail`, `encryptTail`, `decryptTail`). Apart from that,
the functions transcribe the OCaml statements in order.
-/

namespace Ascon.Model.Aead128

open Permutation

def keySize : Int := 16
def nonceSize : Int := 16
def tagSize : Int := 16
def iv : Word := 0x00001000808c0001

inductive InvalidLength where
  | invalidLength
deriving DecidableEq, Repr

inductive DecryptError where
  | authenticationFailure
  | invalidTagLength
deriving DecidableEq, Repr

/-- `Key.of_bytes`. The abstract `Key.t` can only be built here, so every key
passed to `encrypt` / `decrypt` has exactly `key_size` bytes. -/
def Key.ofBytes (key : Bytes) : Except InvalidLength Bytes :=
  if key.length = keySize then .ok (Bytes.copy key) else .error .invalidLength

/-- `Nonce.of_bytes`. -/
def Nonce.ofBytes (nonce : Bytes) : Except InvalidLength Bytes :=
  if nonce.length = nonceSize then .ok (Bytes.copy nonce) else .error .invalidLength

/-- `initialize key nonce` (`initialize` is a Lean keyword, hence the quotes). -/
def «initialize» (key nonce : Bytes) : M (State × Word × Word) := do
  let k0 ← Endian.load64Le key 0
  let k1 ← Endian.load64Le key 8
  let n0 ← Endian.load64Le nonce 0
  let n1 ← Endian.load64Le nonce 8
  let state := State.create iv k0 k1 n0 n1
  let state ← p12 state
  let state := { state with x3 := state.x3 ^^^ k0 }
  let state := { state with x4 := state.x4 ^^^ k1 }
  pure (state, k0, k1)

/-- The `while` loop of `absorb_associated_data`. -/
def adLoop (state : State) (ad : Bytes) (offset : Int) : M (State × Int) :=
  if ad.length - offset ≥ 16 then do
    let state := { state with x0 := state.x0 ^^^ (← Endian.load64Le ad offset) }
    let state := { state with x1 := state.x1 ^^^ (← Endian.load64Le ad (offset + 8)) }
    let state ← p8 state
    adLoop state ad (offset + 16)
  else pure (state, offset)
termination_by (ad.length - offset).toNat

/-- The final, padded associated-data block of `absorb_associated_data`. -/
def adTail (state : State) (ad : Bytes) (offset : Int) : M State := do
  let remaining := ad.length - offset
  let state ←
    if remaining ≥ 8 then do
      let state := { state with x0 := state.x0 ^^^ (← Endian.load64Le ad offset) }
      let state := { state with
        x1 := state.x1 ^^^ (← Endian.loadPartialLe ad (offset + 8) (remaining - 8)) }
      pure { state with x1 := state.x1 ^^^ (← Endian.padding (remaining - 8)) }
    else do
      let state := { state with
        x0 := state.x0 ^^^ (← Endian.loadPartialLe ad offset remaining) }
      pure { state with x0 := state.x0 ^^^ (← Endian.padding remaining) }
  p8 state

/-- `absorb_associated_data state associated_data`. -/
def absorbAssociatedData (state : State) (ad : Bytes) : M State := do
  let length := ad.length
  let state ←
    if length ≠ 0 then do
      let (state, offset) ← adLoop state ad 0
      adTail state ad offset
    else pure state
  -- The domain-separation bit is bit 319: byte 7 of S4.
  pure { state with x4 := state.x4 ^^^ Int64.minInt }

/-- `finalize state k0 k1`. -/
def finalize (state : State) (k0 k1 : Word) : M Bytes := do
  let state := { state with x2 := state.x2 ^^^ k0 }
  let state := { state with x3 := state.x3 ^^^ k1 }
  let state ← p12 state
  let state := { state with x3 := state.x3 ^^^ k0 }
  let state := { state with x4 := state.x4 ^^^ k1 }
  let tag ← Bytes.create tagSize
  let tag ← Endian.store64Le tag 0 state.x3
  Endian.store64Le tag 8 state.x4

/-- The `while` loop of `encrypt`. -/
def encryptLoop (state : State) (plaintext ciphertext : Bytes) (offset : Int) :
    M (State × Bytes × Int) :=
  if plaintext.length - offset ≥ 16 then do
    let state := { state with x0 := state.x0 ^^^ (← Endian.load64Le plaintext offset) }
    let state := { state with x1 := state.x1 ^^^ (← Endian.load64Le plaintext (offset + 8)) }
    let ciphertext ← Endian.store64Le ciphertext offset state.x0
    let ciphertext ← Endian.store64Le ciphertext (offset + 8) state.x1
    let state ← p8 state
    encryptLoop state plaintext ciphertext (offset + 16)
  else pure (state, ciphertext, offset)
termination_by (plaintext.length - offset).toNat

/-- The final plaintext block of `encrypt`. -/
def encryptTail (state : State) (plaintext ciphertext : Bytes) (offset : Int) :
    M (State × Bytes) := do
  let remaining := plaintext.length - offset
  if remaining ≥ 8 then do
    let state := { state with x0 := state.x0 ^^^ (← Endian.load64Le plaintext offset) }
    let state := { state with
      x1 := state.x1 ^^^ (← Endian.loadPartialLe plaintext (offset + 8) (remaining - 8)) }
    let ciphertext ← Endian.store64Le ciphertext offset state.x0
    let ciphertext ← Endian.storePartialLe ciphertext (offset + 8) state.x1 (remaining - 8)
    let state := { state with x1 := state.x1 ^^^ (← Endian.padding (remaining - 8)) }
    pure (state, ciphertext)
  else do
    let state := { state with
      x0 := state.x0 ^^^ (← Endian.loadPartialLe plaintext offset remaining) }
    let ciphertext ← Endian.storePartialLe ciphertext offset state.x0 remaining
    let state := { state with x0 := state.x0 ^^^ (← Endian.padding remaining) }
    pure (state, ciphertext)

/-- `encrypt ~key ~nonce ~associated_data ~plaintext`. -/
def encrypt (key nonce ad plaintext : Bytes) : M (Bytes × Bytes) := do
  let (state, k0, k1) ← «initialize» key nonce
  let state ← absorbAssociatedData state ad
  let length := plaintext.length
  let ciphertext ← Bytes.create length
  let (state, ciphertext, offset) ← encryptLoop state plaintext ciphertext 0
  let (state, ciphertext) ← encryptTail state plaintext ciphertext offset
  let tag ← finalize state k0 k1
  pure (ciphertext, tag)

/-- The `while` loop of `decrypt`. -/
def decryptLoop (state : State) (ciphertext plaintext : Bytes) (offset : Int) :
    M (State × Bytes × Int) :=
  if ciphertext.length - offset ≥ 16 then do
    let c0 ← Endian.load64Le ciphertext offset
    let c1 ← Endian.load64Le ciphertext (offset + 8)
    let plaintext ← Endian.store64Le plaintext offset (state.x0 ^^^ c0)
    let plaintext ← Endian.store64Le plaintext (offset + 8) (state.x1 ^^^ c1)
    let state := { state with x0 := c0 }
    let state := { state with x1 := c1 }
    let state ← p8 state
    decryptLoop state ciphertext plaintext (offset + 16)
  else pure (state, plaintext, offset)
termination_by (ciphertext.length - offset).toNat

/-- The final ciphertext block of `decrypt`. -/
def decryptTail (state : State) (ciphertext plaintext : Bytes) (offset : Int) :
    M (State × Bytes) := do
  let remaining := ciphertext.length - offset
  if remaining ≥ 8 then do
    let c0 ← Endian.load64Le ciphertext offset
    let tail := remaining - 8
    let c1 ← Endian.loadPartialLe ciphertext (offset + 8) tail
    let plaintext ← Endian.store64Le plaintext offset (state.x0 ^^^ c0)
    let plaintext ← Endian.storePartialLe plaintext (offset + 8) (state.x1 ^^^ c1) tail
    let state := { state with x0 := c0 }
    let state := { state with x1 := (← Endian.replaceLowBytes state.x1 c1 tail) }
    let state := { state with x1 := state.x1 ^^^ (← Endian.padding tail) }
    pure (state, plaintext)
  else do
    let c0 ← Endian.loadPartialLe ciphertext offset remaining
    let plaintext ← Endian.storePartialLe plaintext offset (state.x0 ^^^ c0) remaining
    let state := { state with x0 := (← Endian.replaceLowBytes state.x0 c0 remaining) }
    let state := { state with x0 := state.x0 ^^^ (← Endian.padding remaining) }
    pure (state, plaintext)

/-- `decrypt ~key ~nonce ~associated_data ~ciphertext ~tag`. The zero fill of a
rejected candidate is performed and its result discarded, as in OCaml, where
the buffer is simply dropped afterwards. -/
def decrypt (key nonce ad ciphertext tag : Bytes) : M (Except DecryptError Bytes) := do
  if tag.length ≠ tagSize then pure (.error .invalidTagLength)
  else
    let (state, k0, k1) ← «initialize» key nonce
    let state ← absorbAssociatedData state ad
    let length := ciphertext.length
    let plaintext ← Bytes.create length
    let (state, plaintext, offset) ← decryptLoop state ciphertext plaintext 0
    let (state, plaintext) ← decryptTail state ciphertext plaintext offset
    let expectedTag ← finalize state k0 k1
    if ← ConstantTime.equal expectedTag tag then pure (.ok plaintext)
    else do
      let _ ← Bytes.fill plaintext 0 length 0
      pure (.error .authenticationFailure)

/-- `encrypt_combined`. -/
def encryptCombined (key nonce ad plaintext : Bytes) : M Bytes := do
  let (ciphertext, tag) ← encrypt key nonce ad plaintext
  let ciphertextLength := ciphertext.length
  if ciphertextLength > maxStringLength - tagSize then
    invalidArg "Ascon combined ciphertext is too long"
  let combined ← Bytes.create (ciphertextLength + tagSize)
  let combined ← Bytes.blit ciphertext 0 combined 0 ciphertextLength
  Bytes.blit tag 0 combined ciphertextLength tagSize

/-- `decrypt_combined`. -/
def decryptCombined (key nonce ad combined : Bytes) : M (Except DecryptError Bytes) := do
  let length := combined.length
  if length < tagSize then pure (.error .invalidTagLength)
  else
    let ciphertextLength := length - tagSize
    let ciphertext ← Bytes.sub combined 0 ciphertextLength
    let tag ← Bytes.sub combined ciphertextLength tagSize
    decrypt key nonce ad ciphertext tag

end Ascon.Model.Aead128
