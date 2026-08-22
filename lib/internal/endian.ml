let byte b i = Int64.of_int (Char.code (Bytes.unsafe_get b i))

let load_partial_le b off len =
  if off < 0 || len < 0 || len > 8 || off > Bytes.length b - len then
    invalid_arg "Ascon internal little-endian load";
  let x = ref 0L in
  for i = 0 to len - 1 do
    x := Int64.logor !x (Int64.shift_left (byte b (off + i)) (8 * i))
  done;
  !x

let load64_le b off = load_partial_le b off 8

let store_partial_le b off x len =
  if off < 0 || len < 0 || len > 8 || off > Bytes.length b - len then
    invalid_arg "Ascon internal little-endian store";
  for i = 0 to len - 1 do
    Bytes.unsafe_set b (off + i)
      (Char.chr
         (Int64.to_int
            (Int64.logand (Int64.shift_right_logical x (8 * i)) 0xffL)))
  done

let store64_le b off x = store_partial_le b off x 8

let padding i =
  if i < 0 || i > 7 then invalid_arg "Ascon internal padding position";
  Int64.shift_left 1L (8 * i)

let replace_low_bytes old replacement len =
  if len < 0 || len > 8 then invalid_arg "Ascon internal byte replacement";
  if len = 8 then replacement
  else
    let low_mask = Int64.sub (Int64.shift_left 1L (8 * len)) 1L in
    Int64.logor (Int64.logand old (Int64.lognot low_mask))
      (Int64.logand replacement low_mask)
