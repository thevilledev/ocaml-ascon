let fail message =
  prerr_endline message;
  exit 2

let nibble = function
  | '0' .. '9' as c -> Char.code c - Char.code '0'
  | 'a' .. 'f' as c -> Char.code c - Char.code 'a' + 10
  | 'A' .. 'F' as c -> Char.code c - Char.code 'A' + 10
  | _ -> fail "invalid hex"

let bytes_of_hex input =
  if String.length input mod 2 <> 0 then fail "odd-length hex";
  Bytes.init (String.length input / 2) (fun i ->
      Char.chr ((nibble input.[2 * i] lsl 4) lor nibble input.[(2 * i) + 1]))

let print_hex bytes =
  Bytes.iter (fun byte -> Printf.printf "%02x" (Char.code byte)) bytes;
  print_newline ()

let key input =
  match Ascon.Aead128.Key.of_bytes (bytes_of_hex input) with
  | Ok key -> key
  | Error _ -> fail "invalid key"

let nonce input =
  match Ascon.Aead128.Nonce.of_bytes (bytes_of_hex input) with
  | Ok nonce -> nonce
  | Error _ -> fail "invalid nonce"

let get = function Ok value -> value | Error _ -> fail "operation failed"

let () =
  match Array.to_list Sys.argv with
  | [ _; "aead"; key_hex; nonce_hex; ad_hex; plaintext_hex ] ->
      let output =
        Ascon.Aead128.encrypt_combined ~key:(key key_hex)
          ~nonce:(nonce nonce_hex) ~associated_data:(bytes_of_hex ad_hex)
          ~plaintext:(bytes_of_hex plaintext_hex)
      in
      print_hex output
  | [ _; "hash"; message_hex ] ->
      print_hex (Ascon.Hash256.digest (bytes_of_hex message_hex))
  | [ _; "xof"; message_hex; length ] ->
      print_hex
        (get
           (Ascon.Xof128.digest (bytes_of_hex message_hex)
              ~length:(int_of_string length)))
  | [ _; "cxof"; customization_hex; message_hex; length ] ->
      print_hex
        (get
           (Ascon.Cxof128.digest ~customization:(bytes_of_hex customization_hex)
              ~message:(bytes_of_hex message_hex) ~length:(int_of_string length)))
  | _ -> fail "invalid arguments"
