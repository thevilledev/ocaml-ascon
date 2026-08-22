(** The standardized Ascon permutation. This module is internal. *)

val rounds : State.t -> int -> unit
val p12 : State.t -> unit
val p8 : State.t -> unit
