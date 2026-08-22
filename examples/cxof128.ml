let () =
  let customization = Bytes.of_string "com.example.protocol/transcript" in
  let output =
    Common.get_ok "CXOF"
      (Ascon.Cxof128.digest ~customization
         ~message:(Bytes.of_string "protocol message") ~length:32)
  in
  Printf.printf "Ascon-CXOF128: %s\n" (Common.hex output)
