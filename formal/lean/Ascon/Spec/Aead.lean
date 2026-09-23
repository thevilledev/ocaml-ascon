import Ascon.Spec.Permutation

/-!
# Ascon-AEAD128 (SP 800-232, Sec. 4, Algorithms 3 and 4)

Byte-oriented transcription. `S[0:127]` is `S₀ ‖ S₁`, `S[192:319]` is `S₃ ‖ S₄`,
and `IV ‖ K ‖ N` puts `K` in `S₁ ‖ S₂` and `N` in `S₃ ‖ S₄`.
-/

namespace Ascon.Spec.Aead

def IV : Word := 0x00001000808c0001

/-- `S[0:127] ← S[0:127] ⊕ B` for a 16-byte block `B`. -/
def xorRate (S : State) (B : List Byte) : State :=
  { S with s0 := S.s0 ^^^ (words128 B).1, s1 := S.s1 ^^^ (words128 B).2 }

/-- `S[0:127] ← B` for a 16-byte block `B`. -/
def setRate (S : State) (B : List Byte) : State :=
  { S with s0 := (words128 B).1, s1 := (words128 B).2 }

/-- The 16 bytes of `S[0:127]`. -/
def rateBytes (S : State) : List Byte := bytesLE S.s0 ++ bytesLE S.s1

/-- Steps 1–3: initialization. -/
def init (K N : List Byte) : State :=
  let S : State := ⟨IV, wordLE (K.take 8), wordLE (K.drop 8), wordLE (N.take 8), wordLE (N.drop 8)⟩
  let S := asconP 12 S
  { S with s3 := S.s3 ^^^ wordLE (K.take 8), s4 := S.s4 ^^^ wordLE (K.drop 8) }

/-- Steps 4–9: associated data, then domain separation `S ← S ⊕ (0³¹⁹ ‖ 1)`. -/
def processAD (S : State) (A : List Byte) : State :=
  let S :=
    if A.length > 0 then
      (paddedBlocks 16 A).foldl (fun S Ai => asconP 8 (xorRate S Ai)) S
    else S
  { S with s4 := S.s4 ^^^ (1#64 <<< 63) }

/-- Finalization: `S ← Ascon-p[12](S ⊕ (0¹²⁸ ‖ K ‖ 0⁶⁴))` and `T ← S[192:319] ⊕ K`. -/
def finalize (S : State) (K : List Byte) : List Byte :=
  let K0 := wordLE (K.take 8)
  let K1 := wordLE (K.drop 8)
  let S := asconP 12 { S with s2 := S.s2 ^^^ K0, s3 := S.s3 ^^^ K1 }
  bytesLE (S.s3 ^^^ K0) ++ bytesLE (S.s4 ^^^ K1)

/-- Full plaintext blocks: `S[0:127] ← S[0:127] ⊕ Pᵢ`, `Cᵢ ← S[0:127]`, `S ← Ascon-p[8](S)`. -/
def encryptBlocks : State → List (List Byte) → State × List Byte
  | S, [] => (S, [])
  | S, Pi :: Ps =>
    let S := xorRate S Pi
    let Ci := rateBytes S
    let (S, C) := encryptBlocks (asconP 8 S) Ps
    (S, Ci ++ C)

/-- Algorithm 3, `Ascon-AEAD128.enc(K, N, A, P)`, returning `(C, T)`. -/
def encrypt (K N A P : List Byte) : List Byte × List Byte :=
  let S := processAD (init K N) A
  let (full, last) := parse 16 P
  let ℓ := last.length
  let (S, C) := encryptBlocks S full
  -- The last block: `S[0:127] ← S[0:127] ⊕ pad(P_{n-1})`, `C_{n-1} ← S[0:ℓ-1]`.
  let S := xorRate S (pad 16 last)
  let C := C ++ (rateBytes S).take ℓ
  (C, finalize S K)

/-- Full ciphertext blocks: `Pᵢ ← S[0:127] ⊕ Cᵢ`, `S[0:127] ← Cᵢ`, `S ← Ascon-p[8](S)`. -/
def decryptBlocks : State → List (List Byte) → State × List Byte
  | S, [] => (S, [])
  | S, Ci :: Cs =>
    let Pi := xorBytes (rateBytes S) Ci
    let (S, P) := decryptBlocks (asconP 8 (setRate S Ci)) Cs
    (S, Pi ++ P)

inductive DecryptError where
  | invalidTagLength
  | authenticationFailure
deriving DecidableEq, Repr

/-- Algorithm 4, `Ascon-AEAD128.dec(K, N, A, C, T)`. Only 128-bit tags are accepted. -/
def decrypt (K N A C T : List Byte) : Except DecryptError (List Byte) :=
  if T.length ≠ 16 then .error .invalidTagLength
  else
    let S := processAD (init K N) A
    let (full, last) := parse 16 C
    let ℓ := last.length
    let (S, P) := decryptBlocks S full
    -- The last block: `P_{n-1} ← S[0:ℓ-1] ⊕ C_{n-1}`, `S[0:127] ← S[0:127] ⊕ pad(P_{n-1})`.
    let Plast := xorBytes ((rateBytes S).take ℓ) last
    let S := xorRate S (pad 16 Plast)
    if finalize S K = T then .ok (P ++ Plast) else .error .authenticationFailure

/-- Combined format `C ‖ T`. -/
def encryptCombined (K N A P : List Byte) : List Byte :=
  (encrypt K N A P).1 ++ (encrypt K N A P).2

def decryptCombined (K N A CT : List Byte) : Except DecryptError (List Byte) :=
  if CT.length < 16 then .error .invalidTagLength
  else decrypt K N A (CT.take (CT.length - 16)) (CT.drop (CT.length - 16))

end Ascon.Spec.Aead
