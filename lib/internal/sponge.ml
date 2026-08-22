open State

type absorbing = { state : State.t; buffer : bytes; buffered : int }
type squeezing = { state : State.t; offset : int }

let of_state state : absorbing =
  { state = State.copy state; buffer = Bytes.make 8 '\000'; buffered = 0 }

let init ~iv =
  let state = State.create iv 0L 0L 0L 0L in
  Permutation.p12 state;
  of_state state

let absorb_block state block off =
  state.State.x0 <- Int64.logxor state.x0 (Endian.load64_le block off);
  Permutation.p12 state

let absorb (context : absorbing) input =
  let state = State.copy context.state in
  let buffer = Bytes.copy context.buffer in
  let buffered = ref context.buffered in
  let input_offset = ref 0 in
  let input_length = Bytes.length input in
  if !buffered <> 0 then (
    let take = min (8 - !buffered) input_length in
    Bytes.blit input 0 buffer !buffered take;
    buffered := !buffered + take;
    input_offset := take;
    if !buffered = 8 then (
      absorb_block state buffer 0;
      buffered := 0));
  while input_length - !input_offset >= 8 do
    absorb_block state input !input_offset;
    input_offset := !input_offset + 8
  done;
  let remaining = input_length - !input_offset in
  if remaining <> 0 then (
    Bytes.blit input !input_offset buffer 0 remaining;
    buffered := remaining);
  { state; buffer; buffered = !buffered }

let squeezing_of_state state : squeezing = { state = State.copy state; offset = 0 }

let finish_state (context : absorbing) =
  let state = State.copy context.state in
  state.State.x0 <-
    Int64.logxor state.x0
      (Endian.load_partial_le context.buffer 0 context.buffered);
  state.x0 <- Int64.logxor state.x0 (Endian.padding context.buffered);
  Permutation.p12 state;
  state

let finish context = squeezing_of_state (finish_state context)

let squeeze (context : squeezing) length =
  if length < 0 || length > Sys.max_string_length then
    invalid_arg "Ascon XOF output length";
  let state = State.copy context.state in
  let offset = ref context.offset in
  let output = Bytes.create length in
  let written = ref 0 in
  while !written < length do
    let take = min (8 - !offset) (length - !written) in
    for i = 0 to take - 1 do
      let shift = 8 * (!offset + i) in
      Bytes.unsafe_set output (!written + i)
        (Char.chr
           (Int64.to_int
              (Int64.logand (Int64.shift_right_logical state.x0 shift) 0xffL)))
    done;
    written := !written + take;
    offset := !offset + take;
    if !offset = 8 then (
      Permutation.p12 state;
      offset := 0)
  done;
  ({ state; offset = !offset }, output)
