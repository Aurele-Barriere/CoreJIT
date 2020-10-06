open BinNums
open BinInt
open BinPos
open Values
open Camlcoq

(* Converting values to OCaml int *)
let rec int64_of_positive = function
  | Coq_xI p -> Int64.add (Int64.shift_left (int64_of_positive p) 1) 1L
  | Coq_xO p -> Int64.shift_left (int64_of_positive p) 1
  | Coq_xH -> 1L

let rec int_of_positive = function
  | Coq_xI p -> ((int_of_positive p) lsl 1) + 1
  | Coq_xO p -> (int_of_positive p) lsl 1
  | Coq_xH -> 1

let int64_of_val = function
  | Z0 -> 0L
  | Zpos p -> int64_of_positive p
  | Zneg p -> Int64.neg (int64_of_positive p)

let int_of_val v = Int64.to_int (int64_of_val v)

let val_of_int64 (i:int64) =
  if (i > 0L)
  then Zpos (P.of_int64 i)
  else if i < 0L
  then Zneg (P.of_int64 (Int64.neg i))
  else Z0
;;

let val_of_positive (i:P.t) =
  Zpos i

let val_of_int (i:int) =
  val_of_int64 (Int64.of_int i)
