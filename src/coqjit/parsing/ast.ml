(* AST of a program and transformation to an IR program *)
open Common
open Values
open SpecIR
open BinNums
open BinPos
open Camlcoq
open Maps
   
(* AST is just like IR, except it uses int instead of Coq positive, and no records *)
(* And using lists instead of PTrees *)
type abinop =
  | Aplus
  | Aminus
  | Amult
  | Agt
  | Alt
  | Ageq
  | Aleq
  | Aeq

type aunop =
  | Auminus
  | Aneg
  | Aassign
   
type acst = int
  
type areg = int

type aop =
  | Acsti of acst
  | Areg of areg

type aexpr =
  | Abinexpr of abinop * aop * aop
  | Aunexpr of aunop * aop
          
type alabel = int

type afun_id = int

type adeopt_target = afun_id * alabel

type amovelist = (areg * aexpr) list
                   
type avarmap = (areg * aexpr) list

type asynth_frame = adeopt_target * areg * avarmap

type ahint =
  | Ahint_eq of (areg * areg)
  | Ahint_eq_val of (areg * acst)

type ainstruction =
  | Anop of ahint option * alabel
  | Aop of aexpr * areg * alabel
  | Amove of amovelist * alabel
  | Acall of afun_id * aexpr list * areg * alabel
  | Aireturn of aexpr
  | Acond of aexpr * alabel * alabel
  | Astore of aexpr * aexpr * alabel
  | Aload of aexpr * areg * alabel
  | Aprintexpr of aexpr * alabel
  | Aprintstring of string * alabel
  | Aframestate of adeopt_target * avarmap * asynth_frame list * alabel
  | Aassume of aexpr list * adeopt_target * avarmap * asynth_frame list * alabel
  | Afail of string
       
type anode = alabel * ainstruction

type aversion_decl =  alabel * anode list

type afun_decl = afun_id * areg list * aversion_decl * aversion_decl option

type aprogram = afun_id * afun_decl list

(* Convert Ocaml int to Coq positive *)
(* We assume that the argument is a strictly positive integer *)
let pos_of_int (i:int): positive = 
  P.of_int i

let z_of_int (i:int) =
  Z.of_sint i

let convert_binop (ab:abinop): bin_operation =
  match ab with
  | Aplus -> Plus
  | Aminus -> Minus
  | Amult -> Mult
  | Agt -> Gt
  | Alt -> Lt
  | Ageq -> Geq
  | Aleq -> Leq
  | Aeq -> Eq

let convert_unop (au:aunop): un_operation =
  match au with
  | Auminus -> UMinus
  | Aneg -> Neg
  | Aassign -> Assign

let convert_lbl = pos_of_int
let convert_reg = pos_of_int
             
let convert_op (ao:aop): op =
  match ao with
  | Acsti c -> Cst  ((z_of_int c))
  | Areg r -> Reg (pos_of_int r)

let convert_expr (ae:aexpr): expr =
  match ae with
  | Abinexpr (b,o1,o2) -> Binexpr (convert_binop b, convert_op o1, convert_op o2)
  | Aunexpr (u,o) -> Unexpr (convert_unop u, convert_op o)

let convert_exprlist (el:aexpr list): expr list =
  List.map convert_expr el

let convert_varmap (vm:avarmap): varmap =
  List.map (fun (r,e) -> ((convert_reg r),(convert_expr e))) vm

let convert_movelist (ml:amovelist): movelist =
  List.map (fun (r,e) -> ((convert_reg r),(convert_expr e))) ml

let convert_target (at:adeopt_target): deopt_target =
  match at with
  | (afid, albl) -> (pos_of_int afid, convert_lbl albl)
  
let convert_frame ((tgt,r,vm):asynth_frame) =
  ((convert_target tgt, convert_reg r), convert_varmap vm)

let convert_synthlist (sl:asynth_frame list) =
  List.map convert_frame sl

let convert_hint (h:ahint): hint =
  match h with
  | Ahint_eq (r1,r2) -> Hint_Eq (convert_reg r1, convert_reg r2)
  | Ahint_eq_val (r1,v2) -> Hint_Eq_val (convert_reg r1, z_of_int v2)

let convert_instr (ai:ainstruction): instruction =
  match ai with
  | Anop (None,l) -> Nop (None,convert_lbl l)
  | Anop (Some ah, l) -> Nop (Some (convert_hint ah), convert_lbl l)
  | Aop (e,r,l) -> Op (convert_expr e, convert_reg r, convert_lbl l)
  | Amove (ml, l) -> Move (convert_movelist ml, convert_lbl l)
  | Acall (f,el,r,l) -> Call(pos_of_int f, convert_exprlist el, convert_reg r, convert_lbl l)
  | Aireturn (e) -> IReturn(convert_expr e)
  | Acond (e,l1,l2) -> Cond(convert_expr e, convert_lbl l1, convert_lbl l2)
  | Astore (e1,e2,l) -> Store(convert_expr e1, convert_expr e2, convert_lbl l)
  | Aload (e,r,l) -> Load(convert_expr e, convert_reg r, convert_lbl l)
  | Aprintexpr(e,l) -> Printexpr(convert_expr e, convert_lbl l)
  | Aprintstring(str,l) -> Printstring(str, convert_lbl l)
  | Aframestate(tgt,vm,sl,next) -> Framestate(convert_target tgt, convert_varmap vm, convert_synthlist sl, convert_lbl next)
  | Aassume(el,tgt,vm,sl,next) -> Assume(convert_exprlist el,convert_target tgt, convert_varmap vm, convert_synthlist sl,convert_lbl next)
  | Afail s -> Fail s

let rec convert_code (anl:anode list): code =
  match anl with
  | [] -> PTree.empty
  | (l,i)::anl' -> PTree.set (convert_lbl l) (convert_instr i) (convert_code anl')

let convert_version ((lbl,anl):aversion_decl): version =
  { ver_code = convert_code anl; ver_entry = convert_lbl lbl }

let convert_version_option (verop:aversion_decl option): version option=
  match verop with
  | None -> None
  | Some v -> Some (convert_version v)
  
let convert_function ((f,rl,base,optop):afun_decl): coq_function =
  { fn_params = List.map convert_reg rl;
    fn_base = convert_version base;
    fn_opt = convert_version_option optop
  }

let id_function ((f,rl,vid,avl):afun_decl): fun_id =
  pos_of_int f
                 
(* Transform an AST into a program *)
let convert_program ((main,funlist):aprogram) : program =
  { prog_main = pos_of_int main;
    prog_funlist = List.fold_left
                     (fun t af -> PTree.set (id_function af) (convert_function af) t)
                     PTree.empty funlist }
