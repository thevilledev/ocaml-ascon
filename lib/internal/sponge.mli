(** Shared 64-bit-rate sponge machinery for the hash and XOF constructions. *)

type absorbing
type squeezing

val init : iv:int64 -> absorbing
val of_state : State.t -> absorbing
val absorb : absorbing -> bytes -> absorbing
val finish_state : absorbing -> State.t
val finish : absorbing -> squeezing
val squeeze : squeezing -> int -> squeezing * bytes
val squeezing_of_state : State.t -> squeezing
