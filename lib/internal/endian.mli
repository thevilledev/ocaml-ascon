(** Explicit little-endian conversion and partial-word helpers. *)

val load64_le : bytes -> int -> int64
val load_partial_le : bytes -> int -> int -> int64
val store64_le : bytes -> int -> int64 -> unit
val store_partial_le : bytes -> int -> int64 -> int -> unit
val padding : int -> int64
val replace_low_bytes : int64 -> int64 -> int -> int64
