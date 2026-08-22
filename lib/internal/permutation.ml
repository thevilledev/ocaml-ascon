open State

let round_constants =
  [| 0xf0L; 0xe1L; 0xd2L; 0xc3L; 0xb4L; 0xa5L; 0x96L; 0x87L; 0x78L;
     0x69L; 0x5aL; 0x4bL |]

let[@inline] ror x n =
  Int64.logor (Int64.shift_right_logical x n)
    (Int64.shift_left x (64 - n))

let[@inline] round s c =
  (* Constant addition to the least significant byte of S2. *)
  s.State.x2 <- Int64.logxor s.x2 c;

  (* The bitsliced five-bit substitution layer from SP 800-232, Fig. 3. *)
  s.x0 <- Int64.logxor s.x0 s.x4;
  s.x4 <- Int64.logxor s.x4 s.x3;
  s.x2 <- Int64.logxor s.x2 s.x1;
  let t0 = Int64.logxor s.x0 (Int64.logand (Int64.lognot s.x1) s.x2) in
  let t1 = Int64.logxor s.x1 (Int64.logand (Int64.lognot s.x2) s.x3) in
  let t2 = Int64.logxor s.x2 (Int64.logand (Int64.lognot s.x3) s.x4) in
  let t3 = Int64.logxor s.x3 (Int64.logand (Int64.lognot s.x4) s.x0) in
  let t4 = Int64.logxor s.x4 (Int64.logand (Int64.lognot s.x0) s.x1) in
  let t1 = Int64.logxor t1 t0 in
  let t0 = Int64.logxor t0 t4 in
  let t3 = Int64.logxor t3 t2 in
  let t2 = Int64.lognot t2 in

  (* Per-word linear diffusion. *)
  s.x0 <- Int64.logxor t0 (Int64.logxor (ror t0 19) (ror t0 28));
  s.x1 <- Int64.logxor t1 (Int64.logxor (ror t1 61) (ror t1 39));
  s.x2 <- Int64.logxor t2 (Int64.logxor (ror t2 1) (ror t2 6));
  s.x3 <- Int64.logxor t3 (Int64.logxor (ror t3 10) (ror t3 17));
  s.x4 <- Int64.logxor t4 (Int64.logxor (ror t4 7) (ror t4 41))

let rounds s n =
  if n < 1 || n > 12 then invalid_arg "Ascon permutation round count";
  for i = 12 - n to 11 do
    round s (Array.unsafe_get round_constants i)
  done

let p12 s = rounds s 12
let p8 s = rounds s 8
