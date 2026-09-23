import Ascon.Spec.Permutation

/-!
# Ascon-Hash256, Ascon-XOF128 and Ascon-CXOF128 (SP 800-232, Sec. 5, Algorithms 5–7)

All three use a 64-bit rate. Each padded input block is XORed into `S₀` and
followed by `Ascon-p[12]`. Output blocks are read from `S₀`, with
`Ascon-p[12]` applied between consecutive output blocks. The output is truncated
to the requested number of bytes.
-/

namespace Ascon.Spec.Hash

def hashIV : Word := 0x0000080100cc0002
def xofIV : Word := 0x0000080000cc0003
def cxofIV : Word := 0x0000080000cc0004

/-- `S ← Ascon-p[12](IV ‖ 0²⁵⁶)`. -/
def initial (iv : Word) : State := asconP 12 ⟨iv, 0, 0, 0, 0⟩

/-- Absorb one 8-byte block: `S ← Ascon-p[12]((S[0:63] ⊕ Mᵢ) ‖ S[64:319])`. -/
def absorbBlock (S : State) (B : List Byte) : State :=
  asconP 12 { S with s0 := S.s0 ^^^ wordLE B }

def absorb (S : State) (blocks : List (List Byte)) : State := blocks.foldl absorbBlock S

/-- Squeezing `L` bytes: `Hᵢ ← S[0:63]`, `S ← Ascon-p[12](S)` between blocks. -/
def squeeze (S : State) (L : Nat) : List Byte :=
  if L ≤ 8 then (bytesLE S.s0).take L
  else bytesLE S.s0 ++ squeeze (asconP 12 S) (L - 8)
termination_by L

/-- Algorithm 5: `Ascon-Hash256(M)`, a 256-bit digest. -/
def hash256 (M : List Byte) : List Byte :=
  squeeze (absorb (initial hashIV) (paddedBlocks 8 M)) 32

/-- Algorithm 6: `Ascon-XOF128(M, L)` with `L` given in bytes. -/
def xof128 (M : List Byte) (L : Nat) : List Byte :=
  squeeze (absorb (initial xofIV) (paddedBlocks 8 M)) L

/-- Algorithm 7: `Ascon-CXOF128(M, L, Z)` with `|Z| ≤ 2048` bits. `Z₀ = int64(|Z|)`
is the bit length of `Z` as a 64-bit little-endian integer. -/
def cxof128 (M : List Byte) (L : Nat) (Z : List Byte) : List Byte :=
  let Z0 : List Byte := bytesLE (BitVec.ofNat 64 (8 * Z.length))
  let S := absorb (initial cxofIV) ([Z0] ++ paddedBlocks 8 Z)
  squeeze (absorb S (paddedBlocks 8 M)) L

end Ascon.Spec.Hash
