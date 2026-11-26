(* A written type as decoding reads it: the checker describes the type,
   and one decoder (Json.decode) reads the description in every run. *)

type t =
  | Json (* the data as it is *)
  | Int
  | Float
  | String
  | Bool
  | Vector of t
  | Option of t (* null *)
  | Record of (string * t) list (* these keys; the data's others are ignored *)
  | Words of (string * string) list (* each constructor, by its outside word *)
  | Message of (string * t list) list (* the constructors JavaScript may send *)
