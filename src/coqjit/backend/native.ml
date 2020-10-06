open Llvm
open Llvm_target
open Llvm_scalar_opts
open Ctypes
open Ctypes_static
open Foreign
open Common
open Maps
open SpecIR
open Values
open Bigarray
open Camlcoq
open Conv
open Native_llvm
open Native_prim

(* preprocessing: collect all BB's and registers and allocate them in llvm *)
module RegSet = Set.Make(struct
  let compare = Stdlib.compare; type t = reg
end)
module RegMap = Map.Make(struct
  let compare = Stdlib.compare; type t = reg
end)
module LblSet = Set.Make(struct
  let compare = Stdlib.compare; type t = label
end)
module LblMap = Map.Make(struct
  let compare = Stdlib.compare; type t = label
end)

let find_regs f fn_params code builder =
  let registers = ref (RegSet.of_list fn_params) in
  List.iter (function
    | _, Load (_,r,_) | _, Call (_,_,r,_) | _, Op (_,r,_) ->
        registers := RegSet.add r !registers
    | _, Move (ml,l) ->
        registers := RegSet.union !registers (RegSet.of_list (List.map (fun (r,_) -> r) ml))
    | _ -> ()
  ) (PTree.elements code);
  let regmap =
    RegSet.fold (fun reg map ->
      let name = Printer.print_reg reg in
      let store = build_alloca int_val_type name builder in
      RegMap.add reg store map) !registers RegMap.empty
  in
  regmap

(* The calling convention for native functions is:
 *
 *   ( heap* , arg* ) -> ()
 *
 * The (int64) heap* points to the first cell of the heap.
 * The (int64) arg* points to a mixed array [jit_state; arg0; ...; argN]
 *
 * The result of the function is a tuple (jit_state, res) which is returned
 * as the first two entries in the arg array. The jit_state is an opaque int64.
 *
 * The following helpers allocate such an arg buf in llvm and ocaml
 *)
let arg_buf_at arg_buf i builder =
  build_in_bounds_gep arg_buf [|const_int i32_type i|] "" builder

let global_arg_buf_at arg_buf i builder =
  build_in_bounds_gep arg_buf [|zero; const_int i32_type i|] "" builder

let arg_buf jit_state args builder =
  (* arg buffer must at least have length 2 since it is reused to return js
   * and result *)
  let n = max (1+(List.length args)) 2 in
  let n = const_int i32_type n in
  let arg_buf = build_array_alloca int_val_type n "" builder in
  List.iteri (fun i a ->
    ignore (build_store a (arg_buf_at arg_buf i builder) builder))
  (jit_state::args);
  (n, arg_buf)

let global_arg_buf jit_state args builder =
  (* arg buffer must at least have length 2 since it is reused to return js
   * and result *)
  let n = max (1+(List.length args)) 2 in
  let n = const_int i32_type n in
  (*let arg_buf = build_array_alloca int_val_type n "" builder in*)
  List.iteri (fun i a ->
    ignore (build_store a (global_arg_buf_at global_arg_buffer i builder) builder))
  (jit_state::args);
  (n, global_arg_buffer)


let arg_buf_ocaml jit_state args =
  let n = max (1+(List.length args)) 2 in
  let arg_buf = CArray.make int64_t n in
  CArray.set arg_buf 0 (to_opaque jit_state);
  List.iteri (fun i v -> CArray.set arg_buf (i+1) (int64_of_val v)) args;
  (n, arg_buf)

let arg_buf_ocaml_result arg_buf =
  (release_opaque (CArray.get arg_buf 0), val_of_int64 (CArray.get arg_buf 1))

(* compiles a bounds check for the heap *)
let boundscheck f i ok builder =
  let start_bb = insertion_block builder in
  let is_inbounds = build_icmp Icmp.Ult i (const_int heap_ptr_type Memory.heap_limit) "" builder in

  let out_of_bounds = append_block context "" f in
  position_at_end out_of_bounds builder;
  let msg = build_global_string "Heap idx out of bounds" "" builder in
  let msgp = build_in_bounds_gep msg [|zero; zero|] "" builder in
  let _ = build_call fail_prim [| msgp |] "" builder in
  let _ = build_ret_void builder in

  let inbounds = append_block context "" f in
  position_at_end inbounds builder;
  ok ();

  position_at_end start_bb builder;
  let _ = build_cond_br is_inbounds inbounds out_of_bounds builder in
  position_at_end inbounds builder


module VersionMap = Map.Make(struct
  let compare = Stdlib.compare; type t = version
end)
let compiled_functions = ref VersionMap.empty

let lower symbol =
  let ft_c = funptr (ptr int64_t @-> ptr int64_t @-> returning (void)) in
  Llvm_executionengine.get_function_address symbol ft_c (execution_engine ())

type next_label =
| Returns
| Goto of label
| Branch of llvalue * label * label

let rec get_or_compile prog fid func version =
  match VersionMap.find_opt version (!compiled_functions) with
  | Some (_,_,None) -> assert false
  | Some (_,_,Some fp) -> fp
  | None ->
    let f, builder, symbol = declare fid in
    compiled_functions := VersionMap.add version (f, symbol, None) (!compiled_functions);
    compile prog fid func version f builder;
    let fp = lower symbol in
    compiled_functions := VersionMap.add version (f, symbol, Some fp) (!compiled_functions);
    fp

and get_or_compile_llvm prog fid func version =
  match VersionMap.find_opt version (!compiled_functions) with
  | Some (f, _, _) -> f
  | None ->
    let f, builder, symbol = declare fid in
    compiled_functions := VersionMap.add version (f, symbol, None) (!compiled_functions);
    compile prog fid func version f builder;
    f

and compile prog fid {fn_params} {ver_code=code; ver_entry=entry} f builder =
  if !Flags.print_debug_native then begin
    Printf.printf "[native] compiling fun%d\n%!" (int_of_positive fid)
  end;

  (* first arg points to the heap, second arg is the argument buffer *)
  let mem = (params f).(0) in
  let args = (params f).(1) in

  (* opaque jit_state is the first arg in argument buffer *)
  let jit_state_pos = arg_buf_at args 0 builder in
  let get_jit_state () = build_load jit_state_pos "" builder in
  let set_jit_state js = ignore (build_store js jit_state_pos builder) in

  let regmap = find_regs f fn_params code builder in
  let lblmap = ref LblMap.empty in
  let get_bb lbl =
     match LblMap.find_opt lbl (!lblmap) with
     | Some bb -> bb
     | None ->
         let name = Printer.print_lbl lbl in
         let bb = append_block context name f in
         lblmap := LblMap.add lbl bb (!lblmap);
         bb
  in

  (* helpers for accessing registers *)
  let set1 (reg: SpecIR.reg) v =
    ignore (build_store v (RegMap.find reg regmap) builder)
  in
  let get1 (reg: SpecIR.reg) =
    build_load (RegMap.find reg regmap) "" builder
  in
  let rec set = function
    | [] -> ()
    | (r, v)::ml -> set1 r v; set ml
  in

  (* load arguments and store them to their registers*)
  List.iteri (fun i r ->
    let p = arg_buf_at args (i+1) builder in
    let a = build_load p ("arg"^(string_of_int i)) builder in
    set1 r a) fn_params;

  (* expressions *)
  let op = function
    | Reg r -> get1 r
    | Cst v -> const_int int_val_type (int_of_val v)
  in
  let rec expr = function
    | Binexpr (Plus, o1, o2)  -> build_add (op o1) (op o2) "" builder
    | Binexpr (Minus, o1, o2) -> build_sub (op o1) (op o2) "" builder
    | Binexpr (Mult, o1, o2)  -> build_mul (op o1) (op o2) "" builder
    | Binexpr (Gt, o1, o2)    -> let v = build_icmp Icmp.Sgt (op o1) (op o2) "" builder in build_zext v int_val_type "" builder
    | Binexpr (Lt, o1, o2)    -> let v = build_icmp Icmp.Slt (op o1) (op o2) "" builder in build_zext v int_val_type "" builder
    | Binexpr (Geq, o1, o2)   -> let v = build_icmp Icmp.Sge (op o1) (op o2) "" builder in build_zext v int_val_type "" builder
    | Binexpr (Leq, o1, o2)   -> let v = build_icmp Icmp.Sle (op o1) (op o2) "" builder in build_zext v int_val_type "" builder
    | Binexpr (Eq, o1, o2)    -> let v = build_icmp Icmp.Eq  (op o1) (op o2) "" builder in build_zext v int_val_type "" builder
    | Unexpr (UMinus, o)      -> build_neg (op o) "" builder
    | Unexpr (Neg, o)         -> build_select
                                    (build_icmp Icmp.Eq (op o) (const_int int_val_type 0) "" builder)
                                    (const_int int_val_type 1)
                                    (const_int int_val_type 0)
                                    "" builder
    | Unexpr (Assign,o) -> op o
  in
  let rec movelist = function
    | [] -> []
    | (r, e)::ml -> (r, expr e)::movelist ml
  in

  (* instructions *)
  let instr label =
    match PTree.get label code with
    | None -> assert false
    | Some i -> begin match i with
      | Nop (oh,l) ->
          Goto l                (* ignoring the hint *)
      | Op (e,r,l) ->
          set1 r (expr e);
          Goto l
      | Move (ml,l) ->
          set (movelist ml);
          Goto l
      | Printstring (str,l) ->
          let msg = build_global_string str "" builder in
          let msgp = build_in_bounds_gep msg [|zero; zero|] "" builder in
          let _ = build_call print_string_prim [|msgp|] "" builder in
          Goto l
      | Printexpr (e,l) ->
          let v = expr e in
          let _ = build_call print_prim [|v|] "" builder in
          Goto l
      | Fail msg ->
          let msg = build_global_string (msg ^ " @ " ^(string_of_int (int_of_positive label))) "" builder in
          let msgp = build_in_bounds_gep msg [|zero; zero|] "" builder in
          let _ = build_call fail_prim [|msgp|] "" builder in
          ignore (build_ret_void builder);
          Returns
      | IReturn e ->
          let res = expr e in
          let p = arg_buf_at args 1 builder in
          let _  = build_store res p builder in
          ignore (build_ret_void builder);
          Returns
      | Store (e,s,l) ->
          let v = expr e in
          let i = expr s in
          boundscheck f i (fun () ->
            let p = build_in_bounds_gep mem [|i|] "" builder in
            build_store v p builder) builder;
          Goto l
      | Load (s,r,l) ->
          let i = expr s in
          boundscheck f i (fun () ->
            let p = build_in_bounds_gep mem [|i|] "" builder in
            let v = build_load p ("Mem["^Printer.print_expr s^"]") builder in
            set1 r v) builder;
          Goto l
      | Cond (e,a,b) ->
          let v = expr e in
          let cond = build_icmp Icmp.Ne v (const_int int_val_type 0) "" builder in
          Branch (cond, a, b)
      | Call (f, args, r, l) ->
          (* compile args *)
          let args = List.map expr args in
          let n, argb = arg_buf (get_jit_state ()) args builder in
          let direct_call = if (!Flags.native_call_always_jit_loop)
                            then None
                            else match find_function f prog with
                            | None -> None
                            | Some func ->
                                let vers = (current_version func) in
                                if (func.fn_base <> vers) then Some (func, vers) else None
          in
          begin match direct_call with
            | None ->
              ignore (build_call call_prim [|
                  const_int i32_type (int_of_positive f);
                  const_int i32_type (List.length args);
                  n;
                  argb|] "" builder)
            | Some (func, vers) ->
              (* alternative: directly call into next function without going back to the jit *)
                  let compiled_f = get_or_compile_llvm prog f func vers in
                  ignore (build_call compiled_f [|mem; argb|] "" builder)
          end;
          (* update our jit state and store result *)
          set_jit_state (build_load (arg_buf_at argb 0 builder) "" builder);
          set1 r (build_load (arg_buf_at argb 1 builder) "" builder);
          Goto l
      | Assume (g, d, vm, sl, l) ->
          (* compile guards *)
          let g' = List.map expr g in
          let g' = List.map (fun g -> build_icmp Icmp.Ne g (const_int int_type 0) "" builder) g' in
          let g' = List.fold_left (fun r g -> build_and r g "" builder) ltrue g' in

          (* Each deopt point has an id which maps to its metadata.
           * Metadata needs to be copied, since there is no guarantee the input version is constant *)
          let id = Array.length !native_deopt_metadata in
          native_deopt_metadata := Array.append !native_deopt_metadata [|(d,vm,sl)|];

          let start_bb = insertion_block builder in

          (* Deopt branch.
           *
           * The deopt primitive uses a buffer for the serialized values. Given
           *
           *     d1 {x1=v1,x2=v2} [d2 r2 {x3=v3}, d3 r3 {x4=v4}]
           *
           * layout of the buffer is:
           *
           *     [jit_state, state, v1, v2, v3, v4]
           *)
          let fail = append_block context ("fail "^(Printer.print_expr_list g)) f in
          position_at_end fail builder;
          let compile_vm (reg,e) = expr e in
          let state = List.fold_left (fun l (((_,_),varmap):synth_frame) ->
            l @ (List.map compile_vm varmap)) (List.map compile_vm vm) sl in
          let n, a = arg_buf (get_jit_state ()) state builder in
          let _ = build_call deopt_prim [|
            const_int i32_type id; n; a|] "" builder in
          let _ = build_ret_void builder in

          (* fall through pass branch *)
          let ok = append_block context "" f in
          position_at_end start_bb builder;
          let _ = build_cond_br g' ok fail builder in
          position_at_end ok builder;
          Goto l
      | Framestate _ as i->
          Printf.printf "unsupported instruction: %s\n%!" (Printer.print_instr i);
          assert false
    end
  in

  let rec compile_at seen lbls =
    match lbls with
    | label::rest ->
        if LblSet.find_opt label seen = None then begin
          (* update current bb if this lbl starts a new one *)
          position_at_end (get_bb label) builder;
          (* compile instr *)
          let next = instr label in
          (* connect blocks and recurse *)
          let seen = (LblSet.add label seen) in
          begin match next with
            | Returns ->
                compile_at seen rest
            | Goto l ->
                ignore (build_br (get_bb l) builder);
                compile_at seen (l::rest)
            | Branch (cond, l1, l2) ->
                ignore (build_cond_br cond (get_bb l1) (get_bb l2) builder);
                compile_at seen (l1::l2::rest)
          end
        end else
          compile_at seen rest
    | [] -> ()
  in
  ignore (build_br (get_bb entry) builder);
  compile_at LblSet.empty [entry];

  if !Flags.print_debug_native_code then begin
    Printf.printf "===== Before Opt\n%!";
    (dump_value f)
  end;
  Llvm_analysis.assert_valid_function f;
  let _ = PassManager.run_function f the_fpm in
  if !Flags.print_debug_native_code then begin
    Printf.printf "===== After Opt\n%!";
    (dump_value f)
  end

let call ptr s args =
  (* allocate arg buffer *)
  let _, argb = arg_buf_ocaml s args in
  (* call the native function *)
  ptr (bigarray_start array1 Memory.heap) (CArray.start argb);
  (* extract result *)
  arg_buf_ocaml_result argb

(* This is the hook to enter native land. It takes care of:
  * 1. (lazily) compiling to llvm
  * 2. (lazily) lowering to native
  * 3. calling the function
  * 4. extracting the result *)
let compile_and_call ({prog} as js : Jit.jit_state) fid param_vals : Jit.jit_state =
  match find_function fid prog with
  | None -> assert false
  | Some f ->
    let v = current_version f in
    let fp = get_or_compile prog fid f v in
    if !Flags.print_debug_native then begin
      Printf.printf "[->native] calling native %d\n%!" (int_of_positive fid);
    end;
    let js, res = call fp js param_vals in
    if !Flags.print_debug_native then begin
      Printf.printf "[native->] returning with %s\n%!" (Printer.print_value res);
      if !Flags.print_debug_native_heap then begin
        print_string "[native->] The heap contains ";
        for i = 0 to Memory.heap_limit do Printf.printf "%Ld " Memory.heap.{i} done;
        print_newline ()
      end;
    end;
    {js with synchro = S_Return res}
;;
Jit.do_native_call := compile_and_call;;

(* ensure everything is loaded *)
let init () = ()
