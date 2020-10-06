open SpecIR
open Llvm
open Native_llvm
open Bigarray
open Conv
open Ctypes
open Ctypes_static
open Maps
open Camlcoq

(* Primitive Functions by the native lib *)

(* external hooks, needs to be provided by main *)
let jit_main_hook = ref (fun _ -> assert false);;

(* Converting ocaml objects to opaque ptrs *)
let to_opaque (ovalue : Jit.jit_state)  =
   Int64.of_nativeint (raw_address_of_ptr (Root.create ovalue))
let of_opaque opaque : Jit.jit_state =
  let addr = ptr_of_raw_address (Int64.to_nativeint opaque) in
  Root.get addr
let release_opaque opaque : Jit.jit_state =
  let addr = ptr_of_raw_address (Int64.to_nativeint opaque) in
  let res = Root.get addr in
  Root.release addr;
  res

(* Print *)
let print_prim_ty = function_type void_type [|int_val_type|]
let print_prim = declare_function "c_print_prim" print_prim_ty the_module

(* Print String *)
let print_string_prim_ty = function_type void_type [|char_ptr|]
let print_string_prim = declare_function "c_print_string_prim" print_string_prim_ty the_module

(* Fail *)
let fail_prim_ty = function_type void_type [|char_ptr|]
let fail_prim = declare_function "c_fail_prim" fail_prim_ty the_module

(* Deopt *)
type native_deopt_metadata = (deopt_target * varmap * synth_frame list)
let native_deopt_metadata : (native_deopt_metadata array) ref = ref [||]

let deopt_prim_ty = function_type void_type [|i32_type; i32_type; arg_buf_type|]
let deopt_prim = declare_function "c_deopt_prim" deopt_prim_ty the_module

let ocaml_deopt_prim (id:int) args : unit =
  let (deopt_trg, deopt_vm, deopt_sl) = (!native_deopt_metadata).(id) in
  if !Flags.print_debug_native then begin
    let (deopt_f,deopt_l) = deopt_trg in
    Printf.printf "[native->] Deopt @ %d :\n" id;
    Printf.printf "  target : (%s,%s)\n" (Printer.print_fun_id deopt_f)
                                         (Printer.print_lbl deopt_l);
    Printf.printf "  frames : {%s} [%s]\n" (Printer.print_varmap deopt_vm)
                                           (Printer.print_synth_list deopt_sl);
    Printf.printf "  values : ";
    let n = Array1.dim args in
    for i = 0 to (n-1) do Printf.printf "%Ld " args.{i} done;
    Printf.printf "\n%!"
  end;
  let state = of_opaque args.{0} in
  let find_base_version f =
    match find_base_version f state.prog with
    | Some ver -> ver | None -> assert false
  in
  let md_pos = ref 1 in
  let synth_rm (vm:SpecIR.varmap) =
    let do_synth (s, _) =
      let res = (s, val_of_int64 args.{!md_pos}) in
      md_pos := !md_pos + 1;
      res
    in
    let rm = List.map do_synth vm in
    List.fold_left (fun m (r,v) ->
      PTree.set r v m) PTree.empty rm
  in
  let new_rm = synth_rm deopt_vm in
  let stack' = List.map (fun  (((f,l), reg),vm)->
    Stackframe (reg,find_base_version f,l,synth_rm vm)) deopt_sl
  in
  let new_state = Interpreter.S_Deopt (deopt_trg, stack', new_rm) in
  ignore ((!jit_main_hook) {state with synchro = new_state})
;;
Callback.register "ocaml_deopt_prim" ocaml_deopt_prim

(* Call *)
let call_prim_ty = function_type void_type [|i32_type; i32_type; i32_type; arg_buf_type|]
let call_prim = declare_function "c_call_prim" call_prim_ty the_module
let ocaml_call_prim (func:int) (nargs:int) args : unit =
  let argv = ref [] in
  if !Flags.print_debug_native then begin
    Printf.printf "[native->] calling fun%d with %d args\n%!" func nargs;
  end;
  for i = 0 to (nargs-1) do argv := (val_of_int64 args.{nargs-i})::(!argv) done;
  let state = release_opaque args.{0} in
  let synchro = Interpreter.S_Call (P.of_int func, !argv, None) in
  let (res, state) = (!jit_main_hook) {state with synchro} in
  (* return results via args buffer *)
  args.{0} <- to_opaque state;
  args.{1} <- int64_of_val res;
  if !Flags.print_debug_native then begin
    Printf.printf "[->native] returning %Ld to native\n%!" args.{1};
  end;
;;
Callback.register "ocaml_call_prim" ocaml_call_prim
