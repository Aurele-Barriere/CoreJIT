(* Realizing a few JIT parameters that are not part of the profiler *)
open Datatypes
open BinPos
open BinNums
open Values

(* don't use on negative numbers *)
let rec make_nat (x:int) : Datatypes.nat =
  if x = 0 then O else S (make_nat (x-1))
   
(* JIT Parameters *)
let max_optim = make_nat 10
let interpreter_fuel = make_nat 100

(* Heuristics for the spacing of label and finding fresh_labels *)
let fuel_fresh = make_nat 3
let spacing = Coq_xI Coq_xH

(* Realizing the hint Type *)
type hint =
  | Hint_Eq of (positive * positive) (* speculating on equality between 2 registers *)
  | Hint_Eq_val of (positive * value) (* speculating on the value of a register *)
