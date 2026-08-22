let () =
  let absorbing = Ascon.Xof128.init () in
  let absorbing = Ascon.Xof128.absorb absorbing (Bytes.of_string "streamed ") in
  let absorbing = Ascon.Xof128.absorb absorbing (Bytes.of_string "message") in
  let squeezing = Ascon.Xof128.start_squeezing absorbing in
  let squeezing, first =
    Common.get_ok "first squeeze" (Ascon.Xof128.squeeze squeezing ~length:16)
  in
  let _, second =
    Common.get_ok "second squeeze" (Ascon.Xof128.squeeze squeezing ~length:16)
  in
  Printf.printf "Ascon-XOF128: %s%s\n" (Common.hex first) (Common.hex second)
