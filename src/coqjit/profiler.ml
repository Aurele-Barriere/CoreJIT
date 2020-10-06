(* The profiler gathers information and chooses when to optimize the program *)
(* It sends optimizing information: which function to optimize, with which values... *)
(* This info is not relevant to the correctness proof *)
open Common
open BinNums
open Maps
open Values
open SpecIR
open Interpreter
open List
open Profiler_types
open Printf
open Printer
open Conv

   
type optim_id = fun_id
   
(* So far, the profiler associates to each function its number of calls *)
type profiler_state =
  { fun_map : int PMap.t;
    status : jit_status;
    already: fun_id list;       (* already optimized functions *)
    fidoptim : optim_id; }
(* In already, we put functions that we already ASKED to optimize *)
(* Maybe these suggestions weren't followed by the JIT, and the functions weren't actually optimized *)

(* Initially, each function has been called 0 times, with no arguments *)
let initial_profiler_state =
  { fun_map = PMap.init 0;      (* initially no functions have been called *)
    status = Exe;
    already = [];               (* no optimized functions *)
    fidoptim = Coq_xH; }

(* The number of calls to a function before optimization *)
let nb_calls_optim = 3

(* Keep the same profiler state information, but with Exe status *)
let exe_ps (ps:profiler_state) =
  {fun_map = ps.fun_map; status = Exe; already = ps.already; fidoptim = ps.fidoptim }

(* The function that analyzes the current synchronization state *)
let profiler (ps:profiler_state) (s:synchro_state) =
  match s with
  | S_Call (fid,val_list,osf) ->  (* Just before a Call *)
     let psmap = ps.fun_map in
     let newpsmap = PMap.set fid ((PMap.get fid psmap)+1) psmap in (* updating the number of executions *)
     begin match (PMap.get fid newpsmap > nb_calls_optim && not(List.mem fid ps.already)) with
     (* The profiler suggests optimizing the called function *)
     | true ->
        let _ = Printf.printf ("\027[95mPROFILER:\027[0m Optimizing %s\n%!") (print_fun_id fid) in
        {fun_map = newpsmap; status = Opt; already = fid::ps.already; fidoptim = fid}
     (* Either already optimized or not been called enough: we keep executing *)
     | false -> {fun_map = newpsmap; status = Exe; already = ps.already; fidoptim = ps.fidoptim }
     end
  | _ -> exe_ps ps              (* On all other states, we simply keep executing *)
  
    
let optim_policy (ps:profiler_state) = ps.status

(* Where to insert Framestate Instructions at the beginning of an optimization step *)
(* First we insert Framesates wherever there is a hint, and after each Call to allow inlining *)
let framestates_to_insert_single (ps:profiler_state) (p:program) =
  match find_function ps.fidoptim p with
  | None -> ps.fidoptim, []
  | Some f ->
    let collect acc = function
      | l, Nop (Some _, lbl) ->
         lbl::acc
      | l, Call (callee,args,retreg,nextlbl) ->
         nextlbl::acc
      | _ -> acc
    in
    ps.fidoptim, List.fold_left collect [] (PTree.elements f.fn_base.ver_code)

let framestates_to_insert (ps:profiler_state) (p:program) =
  [framestates_to_insert_single ps p]

let collect_hints ps (func:version) =
  let collect acc = function
    | l, Nop (Some (Hint_Eq(r1, r2)), lbl) ->
        (ps.fidoptim,
         AS_INS(
          [Binexpr(Eq, Reg r1, Reg r2)],
          lbl)) :: acc
    | l, Nop (Some (Hint_Eq_val(r, v)), lbl) ->
        (ps.fidoptim,
         AS_INS(
          [Binexpr(Eq, Reg r, Cst v)],
          lbl)) :: acc
    | _ -> acc
  in
  List.fold_left collect [] (PTree.elements func.ver_code)

(* finding call instructions to inline *)
(* Here we suggest inlining every calls *)
let collect_calls (ps:profiler_state) (func:version) =
  let collect acc = function
    | l, Call (_, _, _, _) -> (ps.fidoptim, INLINE l) :: acc
    | _ -> acc
  in
  List.fold_left collect [] (PTree.elements func.ver_code)

let optim_list (ps:profiler_state) (p:program) =
  let cf = List.init 10 (fun _ -> (ps.fidoptim, CST_PROP)) in
  (if !Flags.disable_profiler_hints then
     []
   else
     match find_function ps.fidoptim p with
     | None -> []
     | Some f ->
        (collect_hints ps f.fn_base) @ (collect_calls ps f.fn_base))@
    cf


