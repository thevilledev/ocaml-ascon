(** Mutable five-word representation of the 320-bit Ascon state. *)

type t = {
  mutable x0 : int64;
  mutable x1 : int64;
  mutable x2 : int64;
  mutable x3 : int64;
  mutable x4 : int64;
}

val create : int64 -> int64 -> int64 -> int64 -> int64 -> t
val copy : t -> t
