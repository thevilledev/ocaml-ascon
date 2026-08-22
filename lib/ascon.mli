(** Pure OCaml implementations of the algorithms standardized by NIST SP 800-232.

    This library implements the final standardized, little-endian algorithms. It
    is not compatible with Ascon v1.2. All message-oriented inputs and outputs
    are byte strings; arbitrary bit-length inputs are not supported. *)

(** Authenticated encryption with Ascon-AEAD128. *)
module Aead128 : sig
  val key_size : int
  (** Required key length in bytes. *)

  val nonce_size : int
  (** Required nonce length in bytes. *)

  val tag_size : int
  (** Authentication-tag length in bytes. *)

  module Key : sig
    type t
    (** A validated, copied 128-bit key. *)

    val of_bytes : bytes -> (t, [ `Invalid_length ]) result
    (** [of_bytes key] copies and validates [key]. *)

    val of_string : string -> (t, [ `Invalid_length ]) result
    (** [of_string key] copies and validates [key]. *)
  end

  module Nonce : sig
    type t
    (** A validated, copied 128-bit public nonce. *)

    val of_bytes : bytes -> (t, [ `Invalid_length ]) result
    (** [of_bytes nonce] copies and validates [nonce]. *)

    val of_string : string -> (t, [ `Invalid_length ]) result
    (** [of_string nonce] copies and validates [nonce]. *)
  end

  val encrypt :
    key:Key.t ->
    nonce:Nonce.t ->
    associated_data:bytes ->
    plaintext:bytes ->
    bytes * bytes
  (** [encrypt] returns detached [(ciphertext, tag)]. A nonce must never be
      reused with the same key. *)

  val decrypt :
    key:Key.t ->
    nonce:Nonce.t ->
    associated_data:bytes ->
    ciphertext:bytes ->
    tag:bytes ->
    (bytes, [ `Authentication_failure | `Invalid_tag_length ]) result
  (** [decrypt] releases plaintext only after successful tag verification. *)

  val encrypt_combined :
    key:Key.t ->
    nonce:Nonce.t ->
    associated_data:bytes ->
    plaintext:bytes ->
    bytes
  (** [encrypt_combined] returns [ciphertext || tag]. *)

  val decrypt_combined :
    key:Key.t ->
    nonce:Nonce.t ->
    associated_data:bytes ->
    bytes ->
    (bytes, [ `Authentication_failure | `Invalid_tag_length ]) result
  (** [decrypt_combined] accepts the unambiguous [ciphertext || tag] format. *)
end

(** The fixed-output Ascon-Hash256 hash function. *)
module Hash256 : sig
  type ctx
  (** An immutable incremental hashing context. *)

  val digest_size : int
  (** Digest length in bytes. *)

  val init : unit -> ctx
  (** [init ()] returns a fresh empty context. *)

  val feed : ctx -> bytes -> ctx
  (** [feed ctx input] returns a new context with [input] absorbed. *)

  val feed_string : ctx -> string -> ctx
  (** String-input version of {!feed}. *)

  val get : ctx -> bytes
  (** [get ctx] returns the digest without changing [ctx]. *)

  val digest : bytes -> bytes
  (** One-shot byte-string hashing. *)

  val digest_string : string -> bytes
  (** One-shot string hashing. *)
end

(** The Ascon-XOF128 extendable-output function. *)
module Xof128 : sig
  type absorbing
  (** An immutable state that accepts more message bytes. *)

  type squeezing
  (** An immutable state that can only produce output. *)

  type length_error = [ `Invalid_length ]
  (** Error returned when a requested byte length is invalid. *)

  val init : unit -> absorbing
  (** [init ()] starts a new XOF computation. *)

  val absorb : absorbing -> bytes -> absorbing
  (** [absorb state input] returns a state containing [input]. *)

  val start_squeezing : absorbing -> squeezing
  (** Finalizes absorption. Its result cannot be passed to {!absorb}. *)

  val squeeze :
    squeezing -> length:int ->
    (squeezing * bytes, length_error) result
  (** [squeeze state ~length] emits the next [length] bytes. Repeated calls
      concatenate to the same output as one longer call. *)

  val digest : bytes -> length:int -> (bytes, length_error) result
  (** One-shot XOF output. [length] must be positive, as required by SP 800-232. *)
end

(** The customized Ascon-CXOF128 extendable-output function. *)
module Cxof128 : sig
  type absorbing
  (** An immutable state that accepts message bytes. *)

  type squeezing
  (** An immutable state that can only produce output. *)

  type error = [ `Customization_too_long | `Invalid_length ]
  (** Errors for customization strings over 256 bytes or invalid output lengths. *)

  val init : customization:bytes -> (absorbing, [ `Customization_too_long ]) result
  (** Initializes CXOF with a customization string of at most 256 bytes. The
      bytes are fully processed before this function returns. *)

  val absorb : absorbing -> bytes -> absorbing
  (** Absorbs message bytes after customization processing. *)

  val start_squeezing : absorbing -> squeezing
  (** Finalizes message absorption and permanently starts squeezing. *)

  val squeeze :
    squeezing -> length:int ->
    (squeezing * bytes, [ `Invalid_length ]) result
  (** Emits the next [length] bytes. *)

  val digest :
    customization:bytes ->
    message:bytes ->
    length:int ->
    (bytes, error) result
  (** One-shot customized XOF output. [length] must be positive, as required by
      SP 800-232. *)
end
