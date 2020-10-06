(* Implementations of the memory *)

open Bigarray
open Common
open BinNums
open Maps
open Values

(* A first implementation of the memory  *)
(* Load and Store fail on non-strictly positive values *)
type mem_state = value PTree.t
let initial_memory : mem_state = PTree.empty

(* The native heap *)
let heap_limit = 300
let heap = Array1.create Bigarray.int64 Bigarray.c_layout (heap_limit+1)

let load_ (ms:mem_state) (addr:value): value option =
  let load () =
    match addr with
    | Zneg _ -> None
    | Z0 -> None
    | Zpos p -> PTree.get p ms
  in
  if !Flags.enable_native
  then (assert (ms = initial_memory);
        Some (Conv.val_of_int64 heap.{Conv.int_of_val addr}))
  else load ()

let store_ (ms:mem_state) (addr:value) (v:value): mem_state option =
  let store () =
    match addr with
    | Zneg _ -> None
    | Z0 -> None
    | Zpos p ->  Some (PTree.set p v ms)
  in
  if !Flags.enable_native
  then (assert (ms = initial_memory);
        heap.{Conv.int_of_val addr} <- (Conv.int64_of_val v);
        Some ms)
  else store ()
