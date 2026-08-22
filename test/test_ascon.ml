exception Test_failure of string

let fail format = Printf.ksprintf (fun message -> raise (Test_failure message)) format

let check condition format =
  Printf.ksprintf
    (fun message -> if not condition then raise (Test_failure message))
    format

let check_bytes label expected actual =
  if not (Bytes.equal expected actual) then fail "%s: byte strings differ" label

let bytes_of_hex hex =
  let length = String.length hex in
  if length mod 2 <> 0 then fail "odd-length hexadecimal input";
  let value c =
    match c with
    | '0' .. '9' -> Char.code c - Char.code '0'
    | 'a' .. 'f' -> Char.code c - Char.code 'a' + 10
    | 'A' .. 'F' -> Char.code c - Char.code 'A' + 10
    | _ -> fail "invalid hexadecimal digit %C" c
  in
  Bytes.init (length / 2) (fun i ->
      Char.chr ((value hex.[2 * i] lsl 4) lor value hex.[(2 * i) + 1]))

let find_equals line =
  try String.index line '=' with Not_found -> fail "malformed vector line: %s" line

let parse_field line =
  let equals = find_equals line in
  let name = String.trim (String.sub line 0 equals) in
  let value =
    String.trim (String.sub line (equals + 1) (String.length line - equals - 1))
  in
  (name, value)

let read_records path =
  let channel = open_in path in
  let finish current records =
    if current = [] then records else List.rev current :: records
  in
  let rec loop current records =
    match input_line channel with
    | line when String.trim line = "" -> loop [] (finish current records)
    | line -> loop (parse_field line :: current) records
    | exception End_of_file ->
        close_in channel;
        List.rev (finish current records)
  in
  loop [] []

let field name record =
  try List.assoc name record
  with Not_found -> fail "missing field %s in vector record" name

let count record = int_of_string (field "Count" record)

let validated_key bytes =
  match Ascon.Aead128.Key.of_bytes bytes with
  | Ok key -> key
  | Error `Invalid_length -> fail "official vector contains an invalid key"

let validated_nonce bytes =
  match Ascon.Aead128.Nonce.of_bytes bytes with
  | Ok nonce -> nonce
  | Error `Invalid_length -> fail "official vector contains an invalid nonce"

let test_aead_kats path =
  let records = read_records path in
  check (List.length records = 1089) "AEAD vector count";
  List.iter
    (fun record ->
      let number = count record in
      let key = validated_key (bytes_of_hex (field "Key" record)) in
      let nonce = validated_nonce (bytes_of_hex (field "Nonce" record)) in
      let plaintext = bytes_of_hex (field "PT" record) in
      let associated_data = bytes_of_hex (field "AD" record) in
      let combined = bytes_of_hex (field "CT" record) in
      let ciphertext_length = Bytes.length plaintext in
      check
        (Bytes.length combined = ciphertext_length + Ascon.Aead128.tag_size)
        "AEAD KAT %d combined length" number;
      let expected_ciphertext = Bytes.sub combined 0 ciphertext_length in
      let expected_tag =
        Bytes.sub combined ciphertext_length Ascon.Aead128.tag_size
      in
      let ciphertext, tag =
        Ascon.Aead128.encrypt ~key ~nonce ~associated_data ~plaintext
      in
      check_bytes (Printf.sprintf "AEAD KAT %d ciphertext" number)
        expected_ciphertext ciphertext;
      check_bytes (Printf.sprintf "AEAD KAT %d tag" number) expected_tag tag;
      match
        Ascon.Aead128.decrypt ~key ~nonce ~associated_data ~ciphertext ~tag
      with
      | Ok decrypted ->
          check_bytes (Printf.sprintf "AEAD KAT %d decryption" number)
            plaintext decrypted
      | Error _ -> fail "AEAD KAT %d decryption rejected" number)
    records;
  Printf.printf "KAT Ascon-AEAD128: %d passed\n%!" (List.length records)

let test_hash_kats path =
  let records = read_records path in
  check (List.length records = 1025) "Hash256 vector count";
  List.iter
    (fun record ->
      let number = count record in
      let message = bytes_of_hex (field "Msg" record) in
      let expected = bytes_of_hex (field "MD" record) in
      check_bytes (Printf.sprintf "Hash256 KAT %d" number) expected
        (Ascon.Hash256.digest message))
    records;
  Printf.printf "KAT Ascon-Hash256: %d passed\n%!" (List.length records)

let get_ok label = function
  | Ok value -> value
  | Error _ -> fail "%s unexpectedly returned an error" label

let test_xof_kats path =
  let records = read_records path in
  check (List.length records = 1025) "XOF128 vector count";
  List.iter
    (fun record ->
      let number = count record in
      let message = bytes_of_hex (field "Msg" record) in
      let expected = bytes_of_hex (field "MD" record) in
      let actual =
        get_ok "XOF KAT"
          (Ascon.Xof128.digest message ~length:(Bytes.length expected))
      in
      check_bytes (Printf.sprintf "XOF128 KAT %d" number) expected actual)
    records;
  Printf.printf "KAT Ascon-XOF128: %d passed\n%!" (List.length records)

let test_cxof_kats path =
  let records = read_records path in
  check (List.length records = 1089) "CXOF128 vector count";
  List.iter
    (fun record ->
      let number = count record in
      let message = bytes_of_hex (field "Msg" record) in
      let customization = bytes_of_hex (field "Z" record) in
      let expected = bytes_of_hex (field "MD" record) in
      let actual =
        get_ok "CXOF KAT"
          (Ascon.Cxof128.digest ~customization ~message
             ~length:(Bytes.length expected))
      in
      check_bytes (Printf.sprintf "CXOF128 KAT %d" number) expected actual)
    records;
  Printf.printf "KAT Ascon-CXOF128: %d passed\n%!" (List.length records)

let check_word label expected actual =
  if expected <> actual then
    fail "%s: expected %016Lx, got %016Lx" label expected actual

let test_endian () =
  let bytes = bytes_of_hex "0123456789abcdef" in
  check_word "load64_le" 0xefcdab8967452301L
    (Ascon__Endian.load64_le bytes 0);
  let stored = Bytes.make 8 '\000' in
  Ascon__Endian.store64_le stored 0 0xefcdab8967452301L;
  check_bytes "store64_le" bytes stored;
  check_word "partial little-endian load" 0x8967452301L
    (Ascon__Endian.load_partial_le bytes 0 5);
  for position = 0 to 7 do
    check_word (Printf.sprintf "padding %d" position)
      (Int64.shift_left 1L (8 * position))
      (Ascon__Endian.padding position)
  done

let check_state label expected state =
  let actual =
    [| state.Ascon__State.x0; state.x1; state.x2; state.x3; state.x4 |]
  in
  Array.iteri
    (fun i word -> check_word (Printf.sprintf "%s S%d" label i) word actual.(i))
    expected

let test_permutation () =
  let zero8 = Ascon__State.create 0L 0L 0L 0L 0L in
  Ascon__Permutation.p8 zero8;
  check_state "p8 zero"
    [| 0x1418f8af721aa830L; 0xa5425f1f8cb31388L; 0xa01ef761bf8e1652L;
       0xf01fdabf8c8a82b4L; 0x0168260badf76a06L |]
    zero8;
  let zero12 = Ascon__State.create 0L 0L 0L 0L 0L in
  Ascon__Permutation.p12 zero12;
  check_state "p12 zero"
    [| 0x78ea7ae5cfebb108L; 0x9b9bfb8513b560f7L; 0x6937f83e03d11a50L;
       0x3fe53f36f2c1178cL; 0x045d648e4def12c9L |]
    zero12;
  let hash = Ascon__State.create 0x0000080100cc0002L 0L 0L 0L 0L in
  Ascon__Permutation.p12 hash;
  check_state "NIST Hash256 precomputed initialization"
    [| 0x9b1e5494e934d681L; 0x4bc3a01e333751d2L; 0xae65396c6b34b81aL;
       0x3c7fd4a4d56a4db3L; 0x1a5c464906c5976dL |]
    hash;
  let xof = Ascon__State.create 0x0000080000cc0003L 0L 0L 0L 0L in
  Ascon__Permutation.p12 xof;
  check_state "NIST XOF128 precomputed initialization"
    [| 0xda82ce768d9447ebL; 0xcc7ce6c75f1ef969L; 0xe7508fd780085631L;
       0x0ee0ea53416b58ccL; 0xe0547524db6f0bdeL |]
    xof;
  let cxof = Ascon__State.create 0x0000080000cc0004L 0L 0L 0L 0L in
  Ascon__Permutation.p12 cxof;
  check_state "NIST CXOF128 precomputed initialization"
    [| 0x675527c2a0e8de03L; 0x43d12d7dc0377bbcL; 0xe9901dec426e81b5L;
       0x2ab14907720780b6L; 0x8f3f1d02d432bc46L |]
    cxof

let patterned length seed =
  Bytes.init length (fun i -> Char.chr ((i + seed) land 0xff))

let feed_in_chunks feed initial message chunks =
  let rec loop state offset = function
    | [] ->
        if offset = Bytes.length message then state
        else feed state (Bytes.sub message offset (Bytes.length message - offset))
    | size :: rest ->
        let take = min size (Bytes.length message - offset) in
        let state = feed state (Bytes.sub message offset take) in
        loop state (offset + take) rest
  in
  loop initial 0 chunks

let boundary_lengths = [ 0; 1; 7; 8; 9; 15; 16; 17; 31; 32; 33; 63; 64; 65 ]

let test_hash_incremental () =
  List.iter
    (fun length ->
      let message = patterned length 19 in
      let expected = Ascon.Hash256.digest message in
      let context =
        feed_in_chunks Ascon.Hash256.feed (Ascon.Hash256.init ()) message
          [ 0; 1; 2; 7; 3; 8; 1; 16 ]
      in
      check_bytes (Printf.sprintf "Hash chunking length %d" length) expected
        (Ascon.Hash256.get context))
    boundary_lengths;
  let empty = Ascon.Hash256.init () in
  ignore (Ascon.Hash256.feed empty (Bytes.of_string "not empty"));
  check_bytes "Hash contexts are persistent" (Ascon.Hash256.digest Bytes.empty)
    (Ascon.Hash256.get empty)

let squeeze_ok state length =
  get_ok "XOF squeeze" (Ascon.Xof128.squeeze state ~length)

let test_xof_streaming () =
  List.iter
    (fun input_length ->
      let message = patterned input_length 37 in
      let absorbed =
        feed_in_chunks Ascon.Xof128.absorb (Ascon.Xof128.init ()) message
          [ 1; 7; 2; 8; 3; 16 ]
      in
      List.iter
        (fun output_length ->
          let expected =
            get_ok "one-shot XOF"
              (Ascon.Xof128.digest message ~length:output_length)
          in
          let state = Ascon.Xof128.start_squeezing absorbed in
          let first_length = output_length / 3 in
          let second_length = (output_length - first_length) / 2 in
          let third_length = output_length - first_length - second_length in
          let state, first = squeeze_ok state first_length in
          let state, second = squeeze_ok state second_length in
          let _, third = squeeze_ok state third_length in
          check_bytes
            (Printf.sprintf "XOF streaming input %d output %d" input_length
               output_length)
            expected (Bytes.concat Bytes.empty [ first; second; third ]))
        (List.filter (fun length -> length > 0) boundary_lengths))
    boundary_lengths;
  check
    (Ascon.Xof128.digest Bytes.empty ~length:(-1) = Error `Invalid_length)
    "XOF rejects negative output length";
  check
    (Ascon.Xof128.digest Bytes.empty ~length:0 = Error `Invalid_length)
    "XOF one-shot API rejects zero output length";
  let state = Ascon.Xof128.start_squeezing (Ascon.Xof128.init ()) in
  let state_after, empty = squeeze_ok state 0 in
  let _, first = squeeze_ok state 8 in
  let _, after_empty = squeeze_ok state_after 8 in
  check (Bytes.length empty = 0) "XOF permits a zero-byte incremental squeeze";
  check_bytes "zero-byte XOF squeeze preserves state" first after_empty

let cxof_squeeze_ok state length =
  get_ok "CXOF squeeze" (Ascon.Cxof128.squeeze state ~length)

let test_cxof_edges () =
  let message = patterned 65 73 in
  List.iter
    (fun customization_length ->
      let customization = patterned customization_length 101 in
      let expected =
        get_ok "one-shot CXOF"
          (Ascon.Cxof128.digest ~customization ~message ~length:65)
      in
      let absorbing =
        get_ok "CXOF init" (Ascon.Cxof128.init ~customization)
      in
      let absorbing =
        feed_in_chunks Ascon.Cxof128.absorb absorbing message [ 1; 7; 8; 9 ]
      in
      let state = Ascon.Cxof128.start_squeezing absorbing in
      let state, first = cxof_squeeze_ok state 7 in
      let _, rest = cxof_squeeze_ok state 58 in
      check_bytes (Printf.sprintf "CXOF customization %d" customization_length)
        expected (Bytes.cat first rest))
    [ 0; 1; 256 ];
  check
    (Ascon.Cxof128.init ~customization:(Bytes.make 257 '\000')
    = Error `Customization_too_long)
    "CXOF rejects a 257-byte customization";
  let one =
    get_ok "CXOF customization one"
      (Ascon.Cxof128.digest ~customization:(Bytes.of_string "one") ~message
         ~length:32)
  in
  let two =
    get_ok "CXOF customization two"
      (Ascon.Cxof128.digest ~customization:(Bytes.of_string "two") ~message
         ~length:32)
  in
  check (not (Bytes.equal one two)) "CXOF customizations must domain-separate";
  check
    (Ascon.Cxof128.digest ~customization:Bytes.empty ~message:Bytes.empty
       ~length:0
    = Error `Invalid_length)
    "CXOF one-shot API rejects zero output length"

let flip_first bytes =
  let changed = Bytes.copy bytes in
  let value = Char.code (Bytes.get changed 0) lxor 1 in
  Bytes.set changed 0 (Char.chr value);
  changed

let flip_bit bytes bit =
  let changed = Bytes.copy bytes in
  let byte = bit / 8 in
  let mask = 1 lsl (bit mod 8) in
  Bytes.set changed byte (Char.chr (Char.code (Bytes.get changed byte) lxor mask));
  changed

let expect_authentication_failure label result =
  match result with
  | Error `Authentication_failure -> ()
  | Error `Invalid_tag_length -> fail "%s returned invalid tag length" label
  | Ok _ -> fail "%s accepted tampered input" label

let test_aead_edges () =
  let key = validated_key (patterned 16 3) in
  let nonce_bytes = patterned 16 41 in
  let nonce = validated_nonce nonce_bytes in
  List.iter
    (fun plaintext_length ->
      List.iter
        (fun associated_data_length ->
          let plaintext = patterned plaintext_length 83 in
          let associated_data = patterned associated_data_length 117 in
          let ciphertext, tag =
            Ascon.Aead128.encrypt ~key ~nonce ~associated_data ~plaintext
          in
          (match
             Ascon.Aead128.decrypt ~key ~nonce ~associated_data ~ciphertext
               ~tag
           with
          | Ok actual ->
              check_bytes
                (Printf.sprintf "AEAD round trip %d/%d" plaintext_length
                   associated_data_length)
                plaintext actual
          | Error _ -> fail "AEAD rejected its own output");
          expect_authentication_failure "modified tag"
            (Ascon.Aead128.decrypt ~key ~nonce ~associated_data ~ciphertext
               ~tag:(flip_first tag));
          if Bytes.length ciphertext <> 0 then
            expect_authentication_failure "modified ciphertext"
              (Ascon.Aead128.decrypt ~key ~nonce ~associated_data
                 ~ciphertext:(flip_first ciphertext) ~tag);
          if Bytes.length associated_data <> 0 then
            expect_authentication_failure "modified associated data"
              (Ascon.Aead128.decrypt ~key ~nonce
                 ~associated_data:(flip_first associated_data) ~ciphertext ~tag);
          let wrong_nonce = validated_nonce (flip_first nonce_bytes) in
          expect_authentication_failure "modified nonce"
            (Ascon.Aead128.decrypt ~key ~nonce:wrong_nonce ~associated_data
               ~ciphertext ~tag))
        boundary_lengths)
    boundary_lengths;
  check
    (Ascon.Aead128.Key.of_bytes (Bytes.make 15 '\000') = Error `Invalid_length)
    "AEAD rejects a short key";
  check
    (Ascon.Aead128.Nonce.of_bytes (Bytes.make 17 '\000') = Error `Invalid_length)
    "AEAD rejects a long nonce";
  check
    (Ascon.Aead128.decrypt ~key ~nonce ~associated_data:Bytes.empty
       ~ciphertext:Bytes.empty ~tag:(Bytes.make 15 '\000')
    = Error `Invalid_tag_length)
    "AEAD rejects an invalid tag length"

let test_aead_all_bit_tampering () =
  let key = validated_key (patterned 16 7) in
  let nonce_bytes = patterned 16 29 in
  let nonce = validated_nonce nonce_bytes in
  let associated_data = patterned 17 61 in
  let plaintext = patterned 17 97 in
  let ciphertext, tag =
    Ascon.Aead128.encrypt ~key ~nonce ~associated_data ~plaintext
  in
  for bit = 0 to (Bytes.length ciphertext * 8) - 1 do
    expect_authentication_failure "each ciphertext bit"
      (Ascon.Aead128.decrypt ~key ~nonce ~associated_data
         ~ciphertext:(flip_bit ciphertext bit) ~tag)
  done;
  for bit = 0 to (Bytes.length tag * 8) - 1 do
    expect_authentication_failure "each tag bit"
      (Ascon.Aead128.decrypt ~key ~nonce ~associated_data ~ciphertext
         ~tag:(flip_bit tag bit))
  done;
  for bit = 0 to (Bytes.length associated_data * 8) - 1 do
    expect_authentication_failure "each associated-data bit"
      (Ascon.Aead128.decrypt ~key ~nonce
         ~associated_data:(flip_bit associated_data bit) ~ciphertext ~tag)
  done;
  for bit = 0 to (Bytes.length nonce_bytes * 8) - 1 do
    let changed_nonce = validated_nonce (flip_bit nonce_bytes bit) in
    expect_authentication_failure "each nonce bit"
      (Ascon.Aead128.decrypt ~key ~nonce:changed_nonce ~associated_data
         ~ciphertext ~tag)
  done;
  let combined =
    Ascon.Aead128.encrypt_combined ~key ~nonce ~associated_data ~plaintext
  in
  (match Ascon.Aead128.decrypt_combined ~key ~nonce ~associated_data combined with
  | Ok actual -> check_bytes "combined AEAD round trip" plaintext actual
  | Error _ -> fail "combined AEAD rejected its own output");
  check
    (Ascon.Aead128.decrypt_combined ~key ~nonce ~associated_data
       (Bytes.make 15 '\000')
    = Error `Invalid_tag_length)
    "combined AEAD rejects input shorter than a tag"

let test_tag_comparison () =
  let zero = Bytes.make 16 '\000' in
  let first = flip_bit zero 0 in
  let last = flip_bit zero 127 in
  check (Ascon__Constant_time.equal zero (Bytes.copy zero))
    "tag comparison accepts equal values";
  check (not (Ascon__Constant_time.equal zero first))
    "tag comparison detects first-byte differences";
  check (not (Ascon__Constant_time.equal zero last))
    "tag comparison detects last-byte differences";
  check (not (Ascon__Constant_time.equal zero (Bytes.make 15 '\000')))
    "tag comparison detects length differences"

let random_bytes state length =
  Bytes.init length (fun _ -> Char.chr (Random.State.int state 256))

let test_properties () =
  let random = Random.State.make [| 0x4153434f; 0x4e |] in
  for case = 1 to 250 do
    let key = validated_key (random_bytes random 16) in
    let nonce = validated_nonce (random_bytes random 16) in
    let associated_data = random_bytes random (Random.State.int random 130) in
    let plaintext = random_bytes random (Random.State.int random 130) in
    let ciphertext, tag =
      Ascon.Aead128.encrypt ~key ~nonce ~associated_data ~plaintext
    in
    (match
       Ascon.Aead128.decrypt ~key ~nonce ~associated_data ~ciphertext ~tag
     with
    | Ok actual ->
        check_bytes (Printf.sprintf "property AEAD round trip %d" case)
          plaintext actual
    | Error _ -> fail "property AEAD round trip %d rejected" case);
    let message = random_bytes random (Random.State.int random 260) in
    let split = Random.State.int random (Bytes.length message + 1) in
    let hash_context =
      Ascon.Hash256.feed
        (Ascon.Hash256.feed (Ascon.Hash256.init ())
           (Bytes.sub message 0 split))
        (Bytes.sub message split (Bytes.length message - split))
    in
    check_bytes (Printf.sprintf "property Hash chunking %d" case)
      (Ascon.Hash256.digest message)
      (Ascon.Hash256.get hash_context)
  done;
  Printf.printf "Properties: 250 deterministic cases passed\n%!"

let run name test =
  try
    test ();
    Printf.printf "Unit %s: passed\n%!" name
  with
  | Test_failure message -> fail "%s: %s" name message

let () =
  if Array.length Sys.argv <> 5 then fail "expected four official vector paths";
  try
    run "little-endian helpers" test_endian;
    run "permutation" test_permutation;
    test_hash_kats Sys.argv.(2);
    test_xof_kats Sys.argv.(3);
    test_cxof_kats Sys.argv.(4);
    test_aead_kats Sys.argv.(1);
    run "Hash incremental" test_hash_incremental;
    run "XOF streaming" test_xof_streaming;
    run "CXOF edges" test_cxof_edges;
    run "AEAD edges and tampering" test_aead_edges;
    run "AEAD every-bit tampering" test_aead_all_bit_tampering;
    run "tag comparison" test_tag_comparison;
    run "properties" test_properties;
    Printf.printf "All Ascon tests passed.\n%!"
  with Test_failure message ->
    prerr_endline ("FAIL: " ^ message);
    exit 1
