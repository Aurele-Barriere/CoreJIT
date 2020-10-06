(* Printing programs and coq extracted types *)
open Common
open BinNums
open BinPos
open Maps
open SpecIR
open Printf
open Events
open Values
open Conv

(* What debugging information should be printed *)
let print_debug_strings = ref false
let print_debug_opt_fun = ref false

let print_debug_info (di:debug_info): string =
  match di with
  | DebugOpt n -> "Optimizing Fun" ^ (string_of_int (int_of_positive n))
  | DebugString s -> s

let print_value (v:value): string =
  Printf.sprintf "%Ld" (int64_of_val v)

let print_event = function
  | Debug di -> begin match (di, !print_debug_strings, !print_debug_opt_fun) with
                | (DebugOpt _,    _,    true)
                | (DebugString _, true, _)    -> Printf.printf ("\027[31mDEBUG:\027[0m  %s\n%!") (print_debug_info di)
                | (_,_,_) -> ()
                end
  | Valprint v -> Printf.printf ("\027[32mOUTPUT:\027[0m %s\n%!") (print_value v)
  | Stringprint str -> Printf.printf ("\027[32mOUTPUT:\027[0m %s\n%!") str
  | Loud_Deopt -> ()
  | Loud_Go_on -> ()

let rec print_trace (t:trace): unit =
  match t with
  | [] -> ()
  | e::t' -> let _ = print_event e in print_trace t'

(* Pretty-printing Programs *)
let print_fun_id (f:fun_id): string =
  "Fun" ^ string_of_int(int_of_positive f)

let print_reg (r:reg): string =
  "reg" ^ string_of_int(int_of_positive r)

let print_lbl (l:label): string =
  "lbl" ^ string_of_int(int_of_positive l)

let print_binop (b:bin_operation): string =
  match b with
  | Plus -> "Plus"
  | Minus -> "Minus"
  | Mult -> "Mult"
  | Gt -> "Gt"
  | Lt -> "Lt"
  | Geq -> "Geq"
  | Leq -> "Leq"
  | Eq -> "Eq"

let print_unop (u:un_operation): string =
  match u with
  | UMinus -> "Uminus"
  | Neg -> "Neg"
  | Assign -> ""

let print_op (o:op): string =
  match o with
  | Reg r -> print_reg r
  | Cst v -> print_value v

let print_expr (e:expr): string =
  match e with
  | Binexpr (b,o1,o2) -> print_binop b ^" "^ print_op o1 ^" "^ print_op o2
  | Unexpr (Assign,o) -> print_op o
  | Unexpr (u,o) -> print_unop u ^" "^ print_op o

let rec print_expr_list (el:expr list): string =
  match el with
  | [] -> ""
  | [e] -> print_expr e
  | e::el' -> print_expr e ^ "," ^ print_expr_list el'

let print_args (el:expr list): string =
  " (" ^ print_expr_list el ^ ") "

let rec print_varmap (vm:varmap): string =
  match vm with
  | [] -> ""
  | [(r,e)] -> "(" ^ print_reg r ^ "," ^ print_expr e ^ ")"
  | (r,e)::vm' -> "(" ^ print_reg r ^ "," ^ print_expr e ^ ") " ^ print_varmap vm'

let rec print_movelist (ml:movelist): string =
  match ml with
  | [] -> ""
  | [(r,e)] -> "(" ^ print_reg r ^ "," ^ print_expr e ^ ")"
  | (r,e)::ml' -> "(" ^ print_reg r ^ "," ^ print_expr e ^ ") " ^ print_movelist ml'

                 
let print_frame ((((f,l),r),vm):synth_frame):string =
  print_fun_id f ^ "." ^
      print_lbl l ^ " " ^
        print_reg r ^ " {" ^
          print_varmap vm ^ "}"

let rec print_synth_list (sl:synth_frame list): string =
  match sl with
  | [] -> ""
  | [f] -> print_frame f
  | f::sl' -> print_frame f ^ " " ^ print_synth_list sl'
  
let print_instr (i:instruction): string =
  match i with
  | Nop (None,lbl) -> "Nop " ^ print_lbl lbl
  | Nop (Some(Hint_Eq(r1,r2)),lbl) -> "# "^print_reg r1^" = "^print_reg r2 ^ " "^print_lbl lbl
  | Nop (Some(Hint_Eq_val(r,v)),lbl) -> "# "^print_reg r^" = "^print_value v^ " "^print_lbl lbl
  | Op (e,r,lbl) -> print_reg r ^ " <- " ^ print_expr e ^" "^ print_lbl lbl
  | Move (ml,lbl) -> "Move " ^ print_movelist ml ^ " " ^ print_lbl lbl
  | Call (f,el,r,lbl) ->
     print_reg r ^ " <- Call " ^ print_fun_id f ^ print_args el ^ print_lbl lbl
  | IReturn e -> "Return " ^ print_expr e
  | Cond (e,lbl1,lbl2) -> "Cond (" ^ print_expr e ^") "^ print_lbl lbl1 ^" "^ print_lbl lbl2
  | Store (ex1,ex2,lbl) -> "Store Mem[" ^ print_expr ex2 ^ "] <- " ^ print_expr ex1 ^" "^ print_lbl lbl
  | Load (ex,r,lbl) -> print_reg r ^ " <- Load Mem[" ^ print_expr ex ^ "] " ^ print_lbl lbl
  | Printexpr (e,lbl) -> "Print " ^ print_expr e ^" "^ print_lbl lbl
  | Printstring (s,lbl) -> "SPrint " ^ s ^" "^ print_lbl lbl
  | Assume (el,(f,l),vm,sl,lbl) ->
     "Assume" ^ print_args el ^" "^ print_fun_id f ^"."^ print_lbl l ^
       " "^ "{" ^ print_varmap vm ^ "} [" ^
         print_synth_list sl ^"] "^ print_lbl lbl
  | Framestate ((f,l), vm, sl, lbl) -> "Framestate "^ print_fun_id f ^"."^ print_lbl l ^
                                         " "^ "{" ^ print_varmap vm ^ "} [" ^
                                           print_synth_list sl ^"] "^ print_lbl lbl
  | Fail s -> "Fail " ^ s 


let positive_sort (pi1:positive* 'a) (pi2:positive* 'a): int =
  match (Pos.leb (fst pi1) (fst pi2)) with
  | true -> -1
  | false -> 1

let rec print_ilist (il:(positive*instruction) list): string =
  match il with
  | [] -> ""
  | (p,i)::il' -> "<" ^ print_lbl (p) ^ "> " ^ print_instr i ^ "\n" ^ print_ilist il'
  
let print_code (c:code): string =
  let ilist = PTree.elements c in
  let silist = List.sort positive_sort ilist in
  print_ilist silist
  
let print_version (v:version): string =
  "[Entry: " ^ print_lbl (v.ver_entry) ^ "]\n" ^
    print_code (v.ver_code) ^ "EndVersion\n"

let print_option_version (o): string =
  match o with
  | None -> ""
  | Some v -> "Version: " ^ print_version v ^ "\n"

let rec print_params (pl:reg list): string =
  match pl with
  | [] -> ""
  | [r] -> print_reg r
  | r::pl' -> print_reg r ^ ", " ^ print_params pl' 

let print_function (f:coq_function): string =
  "Parameters: (" ^ print_params (f.fn_params) ^ ")\n" ^
    "Version: " ^ print_version (f.fn_base) ^ "\n" ^
      print_option_version (f.fn_opt) ^ "EndFunction\n\n"

let rec print_funlist (fl: (fun_id * coq_function) list): string =
  match fl with
  | [] -> "EndProgram\n"
  | (fid,f)::fl' ->
     "Function " ^ print_fun_id fid ^ ":\n" ^
       print_function f ^
         print_funlist fl'

let print_function_list (fl:coq_function PTree.t): string =
  let flist = PTree.elements fl in
  let sflist = List.sort positive_sort flist in
  print_funlist sflist
  
let print_program (p:program): string =
  "[Main: " ^ print_fun_id (p.prog_main) ^ "]\n\n" ^
    print_function_list (p.prog_funlist)

(* We could add more than just the pc *)
(* let print_semantic_state (s:state): string =
 *   match s with
 *   | State (stack,v,pc,rm,ms) -> "Current label: " ^ print_lbl pc
 *   | Final (v,ms) -> "Final State" *)
                                  
  
