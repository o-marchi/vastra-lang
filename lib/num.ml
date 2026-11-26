(* The number types. A fixed-width integer keeps its bits in an
   int32 on every target, since js_of_ocaml's ints have 32 bits: a narrower
   type its low bits, sign-extended if signed; a U32 all 32, read unsigned. *)
type fixed = U8 | U16 | U32 | I8 | I16 | I32
type t = Int | Float | Fixed of fixed

let fixed = [ U8; U16; U32; I8; I16; I32 ]
let all = Int :: Float :: List.map (fun f -> Fixed f) fixed

let name = function
  | Int -> "Int"
  | Float -> "Float"
  | Fixed U8 -> "U8"
  | Fixed U16 -> "U16"
  | Fixed U32 -> "U32"
  | Fixed I8 -> "I8"
  | Fixed I16 -> "I16"
  | Fixed I32 -> "I32"

let of_name n = List.find (fun t -> name t = n) all
let is_name n = List.exists (fun t -> name t = n) all
let signed = function I8 | I16 | I32 -> true | U8 | U16 | U32 -> false
let bits = function U8 | I8 -> 8 | U16 | I16 -> 16 | U32 | I32 -> 32

(* [x]'s bits as [f] keeps them. *)
let wrap f x =
  let unused = 32 - bits f in
  if signed f then Int32.shift_right (Int32.shift_left x unused) unused
  else Int32.shift_right_logical (Int32.shift_left x unused) unused

(* The whole numbers [f] holds. *)
let range f =
  let b = bits f in
  if signed f then (Z.neg (Z.shift_left Z.one (b - 1)), Z.pred (Z.shift_left Z.one (b - 1)))
  else (Z.zero, Z.pred (Z.shift_left Z.one b))

let of_z f n = wrap f (Z.to_int32 (Z.signed_extract n 0 32))
let to_z f x = if f = U32 then Z.extract (Z.of_int32 x) 0 32 else Z.of_int32 x
let compare f a b = if f = U32 then Int32.unsigned_compare a b else Int32.compare a b
