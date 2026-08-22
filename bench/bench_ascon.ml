let sizes = [ 0; 8; 16; 32; 64; 256; 1024; 4096; 16384; 1024 * 1024 ]
let sink = ref 0

let consume bytes =
  if Bytes.length bytes <> 0 then sink := !sink lxor Char.code (Bytes.get bytes 0)

let iterations size =
  if size = 0 then 2_000 else max 1 (min 20_000 (16 * 1024 * 1024 / size))

let allocated_words before after =
  (after.Gc.minor_words +. after.major_words)
  -. (before.Gc.minor_words +. before.major_words)

let measure name size action =
  let count = iterations size in
  Gc.compact ();
  let before_gc = Gc.quick_stat () in
  let before = Unix.gettimeofday () in
  for _ = 1 to count do
    consume (action ())
  done;
  let elapsed = Unix.gettimeofday () -. before in
  let after_gc = Gc.quick_stat () in
  let ns_per_operation = elapsed *. 1e9 /. float_of_int count in
  let throughput =
    if size = 0 then "-"
    else Printf.sprintf "%.2f" (float_of_int (size * count) /. elapsed /. 1e6)
  in
  let words = allocated_words before_gc after_gc /. float_of_int count in
  Printf.printf "%-16s %8d %12.1f %12s %14.1f\n%!" name size
    ns_per_operation throughput words

let benchmark_permutation () =
  let count = 500_000 in
  let state = Ascon__State.create 0L 1L 2L 3L 4L in
  let before = Unix.gettimeofday () in
  for _ = 1 to count do
    Ascon__Permutation.p12 state
  done;
  let elapsed = Unix.gettimeofday () -. before in
  sink := !sink lxor Int64.to_int (Int64.logand state.x0 0xffL);
  Printf.printf "Permutation p[12]: %.1f ns/op, %.2f Mperm/s\n\n"
    (elapsed *. 1e9 /. float_of_int count)
    (float_of_int count /. elapsed /. 1e6)

let () =
  let key =
    match Ascon.Aead128.Key.of_bytes (Bytes.init 16 (fun i -> Char.chr i)) with
    | Ok key -> key
    | Error _ -> assert false
  in
  let nonce =
    match
      Ascon.Aead128.Nonce.of_bytes
        (Bytes.init 16 (fun i -> Char.chr (i + 16)))
    with
    | Ok nonce -> nonce
    | Error _ -> assert false
  in
  benchmark_permutation ();
  Printf.printf "%-16s %8s %12s %12s %14s\n" "algorithm" "bytes" "ns/op"
    "MB/s" "allocated words";
  List.iter
    (fun size ->
      let message = Bytes.init size (fun i -> Char.chr (i land 0xff)) in
      let associated_data = Bytes.of_string "benchmark-associated-data" in
      let ciphertext, tag =
        Ascon.Aead128.encrypt ~key ~nonce ~associated_data ~plaintext:message
      in
      measure "AEAD encrypt" size (fun () ->
          fst
            (Ascon.Aead128.encrypt ~key ~nonce ~associated_data
               ~plaintext:message));
      measure "AEAD decrypt" size (fun () ->
          match
            Ascon.Aead128.decrypt ~key ~nonce ~associated_data ~ciphertext ~tag
          with
          | Ok plaintext -> plaintext
          | Error _ -> assert false);
      measure "Hash256" size (fun () -> Ascon.Hash256.digest message);
      measure "XOF128/32" size (fun () ->
          match Ascon.Xof128.digest message ~length:32 with
          | Ok output -> output
          | Error _ -> assert false);
      measure "CXOF128/32" size (fun () ->
          match
            Ascon.Cxof128.digest
              ~customization:(Bytes.of_string "benchmark") ~message ~length:32
          with
          | Ok output -> output
          | Error _ -> assert false))
    sizes;
  if !sink = -1 then prerr_endline "unreachable"
