import Ascon.Proofs.Aead

/-!
# Ascon-AEAD128 decryption inverts encryption

`Spec.Aead.decrypt_encrypt` shows that the specification is internally
consistent: decrypting `Ascon-AEAD128.enc(K, N, A, P)` with the same key,
nonce and associated data returns `P`. `Aead128.decrypt_encrypt` transfers the
result to the modelled OCaml functions.
-/

namespace Ascon.Spec

open Aead

theorem xorBytes_length (a b : List Byte) : (xorBytes a b).length = min a.length b.length := by
  simp [xorBytes]

/-- Byte-wise XOR with the same key stream twice is the identity. -/
theorem xorBytes_cancel (a b : List Byte) (h : b.length ≤ a.length) :
    xorBytes a (xorBytes a b) = b := by
  induction b generalizing a with
  | nil => simp [xorBytes]
  | cons y ys ih =>
    cases a with
    | nil => simp at h
    | cons x xs =>
      simp only [xorBytes, List.zipWith_cons_cons, List.cons.injEq] at ih ⊢
      exact ⟨by bv_decide, ih xs (by simp at h; omega)⟩

theorem take_xorBytes (n : Nat) (a b : List Byte) :
    (xorBytes a b).take n = xorBytes (a.take n) (b.take n) := by
  simp [xorBytes, List.take_zipWith]

theorem rateBytes_length (S : State) : (rateBytes S).length = 16 := by
  simp [rateBytes, bytesLE_length]

/-- Encrypting one block XORs it into the rate. -/
theorem rateBytes_xorRate (S : State) (B : List Byte) (h : B.length = 16) :
    rateBytes (xorRate S B) = xorBytes (rateBytes S) B := by
  simp only [rateBytes, xorRate, words128]
  rw [Model.Aead128.bytesLE_xor_eight _ _ (by simp; omega),
    Model.Aead128.bytesLE_xor_eight _ _ (by simp; omega),
    ← Model.Aead128.xorBytes_append _ _ _ _ (by simp [bytesLE_length]; omega),
    List.take_append_drop]

/-- Overwriting the rate with the ciphertext block gives the encryption state. -/
theorem setRate_ciphertext (S : State) (B : List Byte) :
    setRate S (rateBytes (xorRate S B)) = xorRate S B := by
  simp only [setRate, rateBytes, words128]
  rw [List.take_append_of_le_length (by simp [bytesLE_length]),
    List.take_of_length_le (by simp [bytesLE_length]),
    List.drop_append_of_le_length (by simp [bytesLE_length]),
    List.drop_of_length_le (by simp [bytesLE_length]), List.nil_append,
    wordLE_bytesLE, wordLE_bytesLE]
  rfl

/-- The ciphertext blocks produced for a list of full plaintext blocks. -/
def encBlocks : State → List (List Byte) → List (List Byte)
  | _, [] => []
  | S, B :: Bs => rateBytes (xorRate S B) :: encBlocks (asconP 8 (xorRate S B)) Bs

theorem encryptBlocks_eq (S : State) (Bs : List (List Byte)) :
    (encryptBlocks S Bs).2 = (encBlocks S Bs).flatten := by
  induction Bs generalizing S with
  | nil => rfl
  | cons B Bs ih =>
    rw [Model.Aead128.encryptBlocks_cons]
    simp [encBlocks, ih]

theorem encBlocks_length (S : State) (Bs : List (List Byte)) :
    ∀ C ∈ encBlocks S Bs, C.length = 16 := by
  induction Bs generalizing S with
  | nil => simp [encBlocks]
  | cons B Bs ih =>
    intro C hC
    simp only [encBlocks, List.mem_cons] at hC
    rcases hC with rfl | hC
    · exact rateBytes_length _
    · exact ih _ C hC

/-- Parsing full 16-byte blocks followed by a short block recovers them. -/
theorem parse_flatten (Cs : List (List Byte)) (L : List Byte) (hC : ∀ C ∈ Cs, C.length = 16)
    (hL : L.length < 16) : parse 16 (Cs.flatten ++ L) = (Cs, L) := by
  induction Cs with
  | nil => simpa using parse_short L hL
  | cons C Cs ih =>
    rw [List.flatten_cons, List.append_assoc,
      parse_block_append _ _ (by decide) (hC C (by simp)),
      ih (fun C' h' => hC C' (by simp [h']))]

/-- Decrypting the ciphertext blocks returns the plaintext blocks and the
same final state. -/
theorem decryptBlocks_encBlocks (S : State) (Bs : List (List Byte))
    (hB : ∀ B ∈ Bs, B.length = 16) :
    decryptBlocks S (encBlocks S Bs) = ((encryptBlocks S Bs).1, Bs.flatten) := by
  induction Bs generalizing S with
  | nil => rfl
  | cons B Bs ih =>
    have hB0 := hB B (by simp)
    rw [encBlocks, Model.Aead128.decryptBlocks_cons, Model.Aead128.encryptBlocks_cons,
      setRate_ciphertext S B, ih _ (fun B' h' => hB B' (by simp [h'])),
      rateBytes_xorRate S B hB0, xorBytes_cancel _ _ (by simp [rateBytes_length]; omega)]
    rfl

theorem take_pad (r : Nat) (X : List Byte) : (pad r X).take X.length = X := by
  simp [pad]

/-- Decryption inverts encryption (SP 800-232, Algorithms 3 and 4). -/
theorem decrypt_encrypt (K N A P : List Byte) :
    decrypt K N A (encrypt K N A P).1 (encrypt K N A P).2 = .ok P := by
  rw [decrypt_eq, encrypt_eq]
  simp only
  have hT : (finalize (xorRate (encryptBlocks (processAD (init K N) A) (parse 16 P).1).1
      (pad 16 (parse 16 P).2)) K).length = 16 := by
    simp [finalize, bytesLE_length]
  rw [ite_eq_right (by omega)]
  generalize processAD (init K N) A = S0
  have hbl := parse_blocks_length (r := 16) P (by decide)
  have hrl := parse_rem_length (r := 16) P (by decide)
  have hj := parse_join (r := 16) P (by decide)
  generalize hF : (parse 16 P).1 = F at hbl hj ⊢
  generalize hL : (parse 16 P).2 = L at hrl hj ⊢
  -- The ciphertext parses back into the ciphertext blocks and the short block.
  generalize hR : (encryptBlocks S0 F).1 = R
  have hCl : ((rateBytes (xorRate R (pad 16 L))).take L.length).length = L.length := by
    simp [rateBytes_length]; omega
  rw [encryptBlocks_eq, parse_flatten _ _ (encBlocks_length S0 F) (by omega),
    decryptBlocks_encBlocks S0 F hbl, hR]
  simp only [hCl]
  have hpad : (pad 16 L).length = 16 := by simp [pad]; omega
  have hPl : xorBytes ((rateBytes R).take L.length)
      ((rateBytes (xorRate R (pad 16 L))).take L.length) = L := by
    simp only [rateBytes_xorRate _ _ hpad, take_xorBytes, take_pad]
    exact xorBytes_cancel _ _ (by simp [rateBytes_length]; omega)
  rw [hPl]
  simp only [↓reduceIte, hj]

end Ascon.Spec

namespace Ascon.Model.Aead128

/-- The modelled `decrypt` accepts every output of the modelled `encrypt` and
returns the original plaintext. -/
theorem decrypt_encrypt (K N A P : List Byte) (hK : K.length = 16) (hN : N.length = 16)
    (hP : (P.length : Int) ≤ maxStringLength) :
    (do
      let (C, T) ← encrypt (Bytes.ofList K) (Bytes.ofList N) (Bytes.ofList A) (Bytes.ofList P)
      decrypt (Bytes.ofList K) (Bytes.ofList N) (Bytes.ofList A) C T) =
      .ok (.ok (Bytes.ofList P)) := by
  rw [bind_of_ok (encrypt_correct K N A P hK hN hP)]
  simp only []
  rw [decrypt_correct K N A _ _ hK hN (by rw [(encrypt_lengths K N A P).1]; exact hP),
    Spec.decrypt_encrypt]
  rfl

end Ascon.Model.Aead128
