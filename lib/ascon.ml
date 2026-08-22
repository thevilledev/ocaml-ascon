open State

module Aead128 = struct
  let key_size = 16
  let nonce_size = 16
  let tag_size = 16
  let iv = 0x00001000808c0001L

  module Key = struct
    type t = bytes

    let of_bytes key =
      if Bytes.length key = key_size then Ok (Bytes.copy key)
      else Error `Invalid_length

    let of_string key = of_bytes (Bytes.of_string key)
  end

  module Nonce = struct
    type t = bytes

    let of_bytes nonce =
      if Bytes.length nonce = nonce_size then Ok (Bytes.copy nonce)
      else Error `Invalid_length

    let of_string nonce = of_bytes (Bytes.of_string nonce)
  end

  let initialize key nonce =
    let k0 = Endian.load64_le key 0 in
    let k1 = Endian.load64_le key 8 in
    let n0 = Endian.load64_le nonce 0 in
    let n1 = Endian.load64_le nonce 8 in
    let state = State.create iv k0 k1 n0 n1 in
    Permutation.p12 state;
    state.x3 <- Int64.logxor state.x3 k0;
    state.x4 <- Int64.logxor state.x4 k1;
    (state, k0, k1)

  let absorb_associated_data state associated_data =
    let length = Bytes.length associated_data in
    if length <> 0 then (
      let offset = ref 0 in
      while length - !offset >= 16 do
        state.State.x0 <-
          Int64.logxor state.x0 (Endian.load64_le associated_data !offset);
        state.x1 <-
          Int64.logxor state.x1
            (Endian.load64_le associated_data (!offset + 8));
        Permutation.p8 state;
        offset := !offset + 16
      done;
      let remaining = length - !offset in
      if remaining >= 8 then (
        state.x0 <-
          Int64.logxor state.x0
            (Endian.load64_le associated_data !offset);
        state.x1 <-
          Int64.logxor state.x1
            (Endian.load_partial_le associated_data (!offset + 8) (remaining - 8));
        state.x1 <- Int64.logxor state.x1 (Endian.padding (remaining - 8)))
      else (
        state.x0 <-
          Int64.logxor state.x0
            (Endian.load_partial_le associated_data !offset remaining);
        state.x0 <- Int64.logxor state.x0 (Endian.padding remaining));
      Permutation.p8 state);
    (* The domain-separation bit is bit 319: byte 7 of S4 in little-endian
       representation. It is applied even when associated data is empty. *)
    state.State.x4 <- Int64.logxor state.x4 Int64.min_int

  let finalize state k0 k1 =
    state.State.x2 <- Int64.logxor state.x2 k0;
    state.x3 <- Int64.logxor state.x3 k1;
    Permutation.p12 state;
    state.x3 <- Int64.logxor state.x3 k0;
    state.x4 <- Int64.logxor state.x4 k1;
    let tag = Bytes.create tag_size in
    Endian.store64_le tag 0 state.x3;
    Endian.store64_le tag 8 state.x4;
    tag

  let encrypt ~key ~nonce ~associated_data ~plaintext =
    let state, k0, k1 = initialize key nonce in
    absorb_associated_data state associated_data;
    let length = Bytes.length plaintext in
    let ciphertext = Bytes.create length in
    let offset = ref 0 in
    while length - !offset >= 16 do
      state.x0 <- Int64.logxor state.x0 (Endian.load64_le plaintext !offset);
      state.x1 <-
        Int64.logxor state.x1 (Endian.load64_le plaintext (!offset + 8));
      Endian.store64_le ciphertext !offset state.x0;
      Endian.store64_le ciphertext (!offset + 8) state.x1;
      Permutation.p8 state;
      offset := !offset + 16
    done;
    let remaining = length - !offset in
    if remaining >= 8 then (
      state.x0 <- Int64.logxor state.x0 (Endian.load64_le plaintext !offset);
      state.x1 <-
        Int64.logxor state.x1
          (Endian.load_partial_le plaintext (!offset + 8) (remaining - 8));
      Endian.store64_le ciphertext !offset state.x0;
      Endian.store_partial_le ciphertext (!offset + 8) state.x1 (remaining - 8);
      state.x1 <- Int64.logxor state.x1 (Endian.padding (remaining - 8)))
    else (
      state.x0 <-
        Int64.logxor state.x0
          (Endian.load_partial_le plaintext !offset remaining);
      Endian.store_partial_le ciphertext !offset state.x0 remaining;
      state.x0 <- Int64.logxor state.x0 (Endian.padding remaining));
    let tag = finalize state k0 k1 in
    (ciphertext, tag)

  let decrypt ~key ~nonce ~associated_data ~ciphertext ~tag =
    if Bytes.length tag <> tag_size then Error `Invalid_tag_length
    else
      let state, k0, k1 = initialize key nonce in
      absorb_associated_data state associated_data;
      let length = Bytes.length ciphertext in
      let plaintext = Bytes.create length in
      let offset = ref 0 in
      while length - !offset >= 16 do
        let c0 = Endian.load64_le ciphertext !offset in
        let c1 = Endian.load64_le ciphertext (!offset + 8) in
        Endian.store64_le plaintext !offset (Int64.logxor state.x0 c0);
        Endian.store64_le plaintext (!offset + 8) (Int64.logxor state.x1 c1);
        state.x0 <- c0;
        state.x1 <- c1;
        Permutation.p8 state;
        offset := !offset + 16
      done;
      let remaining = length - !offset in
      if remaining >= 8 then (
        let c0 = Endian.load64_le ciphertext !offset in
        let tail = remaining - 8 in
        let c1 = Endian.load_partial_le ciphertext (!offset + 8) tail in
        Endian.store64_le plaintext !offset (Int64.logxor state.x0 c0);
        Endian.store_partial_le plaintext (!offset + 8)
          (Int64.logxor state.x1 c1) tail;
        state.x0 <- c0;
        state.x1 <- Endian.replace_low_bytes state.x1 c1 tail;
        state.x1 <- Int64.logxor state.x1 (Endian.padding tail))
      else (
        let c0 = Endian.load_partial_le ciphertext !offset remaining in
        Endian.store_partial_le plaintext !offset (Int64.logxor state.x0 c0)
          remaining;
        state.x0 <- Endian.replace_low_bytes state.x0 c0 remaining;
        state.x0 <- Int64.logxor state.x0 (Endian.padding remaining));
      let expected_tag = finalize state k0 k1 in
      if Constant_time.equal expected_tag tag then Ok plaintext
      else (
        (* Best effort only: OCaml's runtime may retain or copy heap data. *)
        Bytes.fill plaintext 0 length '\000';
        Error `Authentication_failure)

  let encrypt_combined ~key ~nonce ~associated_data ~plaintext =
    let ciphertext, tag = encrypt ~key ~nonce ~associated_data ~plaintext in
    let ciphertext_length = Bytes.length ciphertext in
    if ciphertext_length > Sys.max_string_length - tag_size then
      invalid_arg "Ascon combined ciphertext is too long";
    let combined = Bytes.create (ciphertext_length + tag_size) in
    Bytes.blit ciphertext 0 combined 0 ciphertext_length;
    Bytes.blit tag 0 combined ciphertext_length tag_size;
    combined

  let decrypt_combined ~key ~nonce ~associated_data combined =
    let length = Bytes.length combined in
    if length < tag_size then Error `Invalid_tag_length
    else
      let ciphertext_length = length - tag_size in
      let ciphertext = Bytes.sub combined 0 ciphertext_length in
      let tag = Bytes.sub combined ciphertext_length tag_size in
      decrypt ~key ~nonce ~associated_data ~ciphertext ~tag
end

module Hash256 = struct
  type ctx = Sponge.absorbing

  let digest_size = 32
  let iv = 0x0000080100cc0002L
  let init () = Sponge.init ~iv
  let feed = Sponge.absorb
  let feed_string context input = feed context (Bytes.of_string input)

  let get context =
    let squeezing = Sponge.finish context in
    snd (Sponge.squeeze squeezing digest_size)

  let digest input = get (feed (init ()) input)
  let digest_string input = digest (Bytes.of_string input)
end

module Xof128 = struct
  type absorbing = Sponge.absorbing
  type squeezing = Sponge.squeezing
  type length_error = [ `Invalid_length ]

  let iv = 0x0000080000cc0003L
  let init () = Sponge.init ~iv
  let absorb = Sponge.absorb
  let start_squeezing = Sponge.finish

  let valid_length length = length >= 0 && length <= Sys.max_string_length
  let valid_digest_length length = length > 0 && length <= Sys.max_string_length

  let squeeze state ~length =
    if valid_length length then Ok (Sponge.squeeze state length)
    else Error `Invalid_length

  let digest input ~length =
    if not (valid_digest_length length) then Error `Invalid_length
    else
      let state = start_squeezing (absorb (init ()) input) in
      Ok (snd (Sponge.squeeze state length))
end

module Cxof128 = struct
  type absorbing = Sponge.absorbing
  type squeezing = Sponge.squeezing
  type error = [ `Customization_too_long | `Invalid_length ]

  let iv = 0x0000080000cc0004L

  let init ~customization =
    let length = Bytes.length customization in
    if length > 256 then Error `Customization_too_long
    else
      let initial_state = State.create iv 0L 0L 0L 0L in
      Permutation.p12 initial_state;
      (* Z0 is the customization length in bits, encoded as one little-endian
         64-bit block and immediately followed by a permutation. *)
      initial_state.x0 <-
        Int64.logxor initial_state.x0 (Int64.of_int (length * 8));
      Permutation.p12 initial_state;
      let customization_context = Sponge.of_state initial_state in
      let customization_state =
        Sponge.finish_state (Sponge.absorb customization_context customization)
      in
      (* The message is a separate parse-and-pad operation, so it starts with
         an empty rate buffer after the customized state has been finalized. *)
      Ok (Sponge.of_state customization_state)

  let absorb = Sponge.absorb
  let start_squeezing = Sponge.finish
  let valid_length length = length >= 0 && length <= Sys.max_string_length
  let valid_digest_length length = length > 0 && length <= Sys.max_string_length

  let squeeze state ~length =
    if valid_length length then Ok (Sponge.squeeze state length)
    else Error `Invalid_length

  let digest ~customization ~message ~length =
    if not (valid_digest_length length) then Error `Invalid_length
    else
      match init ~customization with
      | Error `Customization_too_long -> Error `Customization_too_long
      | Ok state ->
          let state = start_squeezing (absorb state message) in
          Ok (snd (Sponge.squeeze state length))
end
