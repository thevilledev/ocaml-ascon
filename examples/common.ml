let hex bytes =
  let alphabet = "0123456789abcdef" in
  let output = Bytes.create (2 * Bytes.length bytes) in
  Bytes.iteri
    (fun i byte ->
      let value = Char.code byte in
      Bytes.set output (2 * i) alphabet.[value lsr 4];
      Bytes.set output ((2 * i) + 1) alphabet.[value land 0x0f])
    bytes;
  Bytes.to_string output

let get_ok label = function
  | Ok value -> value
  | Error _ -> failwith (label ^ " failed")
