let () =
  (* Example-only deterministic material. Production applications must obtain
     keys and unique nonces from an appropriate secure source. *)
  let key_bytes = Bytes.init 16 (fun i -> Char.chr i) in
  let nonce_bytes = Bytes.init 16 (fun i -> Char.chr (0x10 + i)) in
  let key = Common.get_ok "key" (Ascon.Aead128.Key.of_bytes key_bytes) in
  let nonce = Common.get_ok "nonce" (Ascon.Aead128.Nonce.of_bytes nonce_bytes) in
  let associated_data = Bytes.of_string "record header" in
  let plaintext = Bytes.of_string "authenticated payload" in
  let ciphertext, tag =
    Ascon.Aead128.encrypt ~key ~nonce ~associated_data ~plaintext
  in
  let recovered =
    Common.get_ok "decryption"
      (Ascon.Aead128.decrypt ~key ~nonce ~associated_data ~ciphertext ~tag)
  in
  Printf.printf "ciphertext: %s\ntag:        %s\nplaintext:  %s\n"
    (Common.hex ciphertext) (Common.hex tag) (Bytes.to_string recovered)
