let () =
  let digest = Ascon.Hash256.digest_string "Ascon in pure OCaml" in
  Printf.printf "Ascon-Hash256: %s\n" (Common.hex digest)
