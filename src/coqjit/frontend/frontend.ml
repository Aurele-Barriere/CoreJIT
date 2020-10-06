open Lexer
open Lexing
open Lua_syntax
open SpecIR
open Values
open Conv
open Maps
open Ast
open Camlcoq

let print_position fmt lexbuf =
  let pos = lexbuf.lex_curr_p in
  Format.fprintf fmt "%s:%d:%d"
    pos.pos_fname
    pos.pos_lnum
    (pos.pos_cnum - pos.pos_bol + 1)

let parse_with_error lexbuf =
  try Lua_parser.chunk Lua_lexer.read lexbuf with
  | Lua_parser.Error -> begin
    print_endline "error";
    Format.(fprintf std_formatter "%a: syntax error\n"
              print_position lexbuf);
    exit (-1)
  end

let exp_of_op op =
  Unexpr (Assign, op)
let heap_addr v =
  (exp_of_op (Cst v))

let create_counter () = begin
  let counter = ref 0 in
  fun () ->
    P.of_int (
      counter := !counter + 1;
      !counter)
end

let get2 counter =
  counter (), counter ()
let get3 counter =
  counter (), counter (), counter ()
let get4 counter =
  counter (), counter (), counter (), counter ()
let get5 counter =
  counter (), counter (), counter (), counter (), counter ()

let fresh_label = create_counter ()
let fresh_fun_id = create_counter ()
let fresh_heapcell = begin
  let counter = ref 1 in
  fun sz ->
    val_of_positive (
      P.of_int (
        let res = !counter in
        counter := !counter + sz;
        res))
end
let return_type_cell = (exp_of_op (Cst (fresh_heapcell 1))) ;;

let append ((pos:label), (instrs:(label * instruction) list)) (next:(label->instruction)) =
  let l = fresh_label () in
  l, (pos, next l)::instrs

let ( >>= ) a b = append a b

class register_handler =
  object (self)
    val mutable next = 1
    val mutable locals = []
    val mutable temps = []
    val mutable args = []
    method get_local () =
      let reg = P.of_int next in
      next <- next + 1;
      locals <- reg :: locals;
      reg
    method get_temp () =
      let reg = P.of_int next in
      next <- next + 1;
      temps <- reg :: temps;
      reg
    method get_arg () =
      let reg = P.of_int next in
      next <- next + 1;
      args <- reg :: args;
      reg
    method get_locals_and_temps () =
      locals @ temps
  end;;

type dyn_value = op * op

module VarMap = Map.Make(struct
  let compare = Stdlib.compare; type t = string
end)

type local_binding_cell =
| Function of fun_id
| Local of (reg * reg)
type global_binding_cell =
| Function of fun_id
| Global of (value * value)

type local_bindings = local_binding_cell VarMap.t
type global_bindings = global_binding_cell VarMap.t

type scope =
| Global of global_bindings
| Function of fun_id * scope
| Block of scope * local_bindings

type binding_kind =
| NotFound
| FromGlobal of global_binding_cell
| FromLocal of local_binding_cell
| FromOuter of local_binding_cell

let lookup var scope =
  let rec lookup var scope is_inner =
    match scope with
    | Global gs ->
      begin match VarMap.find_opt var gs with
      | Some b -> FromGlobal b
      | None -> NotFound
      end
    | Function (id, s) ->
      lookup var s false
    | Block (s, bs) ->
      begin match VarMap.find_opt var bs with
      | Some b ->
        if (is_inner)
        then FromLocal b
        else FromOuter b
      | None ->
        lookup var s is_inner
      end
  in
  lookup var scope true
;;

let declare_local var value scope =
  match scope with
  | Global gs ->
    assert false
  | Function _ ->
    assert false
  | Block (s, bs) ->
    Block (s, (VarMap.add var value bs))
;;

let rec declare_global var value scope =
  match scope with
  | Global gs ->
    Global (VarMap.add var value gs)
  | Function (id, s) ->
    Function (id, declare_global var value s)
  | Block (s, bs) ->
    Block (declare_global var value s, bs)
;;

let store_local pos (t,v) (rt,rv) =
  let c1,c2 = get2 fresh_label in
  c2,
  (pos, Op (exp_of_op t, rt, c1)) ::
    (c1, Op (exp_of_op v, rv, c2)) :: []

let store_global pos (t,v) (ht,hv) =
  let c1,c2 = get2 fresh_label in
  c2,
  (pos, Store (exp_of_op t, heap_addr ht, c1)) ::
    (c1, Store (exp_of_op v, heap_addr hv, c2)) :: []

let t_nil_v = val_of_int 1;;
let t_nil   = Cst (t_nil_v);;
let t_bool_v= val_of_int 2;;
let t_bool  = Cst (t_bool_v);;
let t_int_v = val_of_int 3;;
let t_int   = Cst t_int_v;;
let t_tbl_v = val_of_int 4;;
let t_tbl   = Cst t_tbl_v;;
let zero    = Cst (val_of_int 0);;
let one     = Cst (val_of_int 1);;
let the_nil = (t_nil, zero);;
let the_true = (t_bool, one);;
let the_false = (t_bool, zero);;

let test_eq a b =
  Binexpr (Eq, a, b)

let typecase pos (tag,v) is_nil is_bool is_int is_tbl =
  let nil_lbl, bool_lbl, int_lbl, tbl_lbl = get4 fresh_label in
  let c1, c2, c3 = get3 fresh_label in
  let instrs = [
    (pos, Cond (test_eq tag t_nil,  nil_lbl,  c1));
    (c1,  Cond (test_eq tag t_bool, bool_lbl, c2));
    (c2,  Cond (test_eq tag t_int,  int_lbl,  c3));
  ] @
  (if (!Flags.enable_frontend_assert)
  then let c4,c5 = get2 fresh_label in [
    (c3,  Cond (test_eq tag t_tbl,  tbl_lbl,   c4));
    (c4,  Printexpr (exp_of_op tag, c5));
    (c5,  Fail "broken typetag")]
  else [
    (c3, Nop (None,tbl_lbl))])
  in
  (is_nil  v nil_lbl)  @
  (is_bool v bool_lbl) @
  (is_int  v int_lbl)  @
  (is_tbl  v tbl_lbl)  @
  instrs

type fun_ref = fun_id * scope * funcbody

let arith_binop = function
  | Addition -> Plus
  | Subtraction -> Minus
  | Multiplication -> Mult
  | Greater -> Lt
  | Less -> Gt
  | GreaterEq -> Leq
  | LessEq -> Geq
  | FloatDivision  -> failwith "unupported /"
  | FloorDivision  -> failwith "unupported //"
  | Modulo         -> failwith "unupported %"
  | Exponentiation -> failwith "unupported exp"
  | BitwiseAnd     -> failwith "unupported &"
  | BitwiseOr      -> failwith "unupported |"
  | BitwiseXor     -> failwith "unupported ^"
  | ShiftRight     -> failwith "unupported >>"
  | ShiftLeft      -> failwith "unupported <<"
  | Equality -> assert false
  | Inequality -> assert false
  | LogicalAnd -> assert false
  | LogicalOr -> assert false
  | Concat -> assert false

(* breadth-first relabling for register analyis *)
let rec breadth_first_labels instrs cur map = function
  | [] -> map
  | l::rest ->
      begin match PTree.get l map with
        | Some _ -> breadth_first_labels instrs cur map rest
        | None ->
            let map = PTree.set l cur map in
            let cur = cur+10 in
            let i = match PTree.get l instrs with
              | None -> assert false
              | Some i -> i
            in
            let rest = (match i with
                | Assume _ | Framestate _ -> assert false
                | Nop (_,l) | Op (_,_,l) | Move (_, l) | Call (_,_,_,l)
                | Store (_,_,l) | Load (_,_,l) | Printexpr(_,l) | Printstring (_,l) -> [l]
                | IReturn (_) | Fail (_)     -> []
                | Cond (_,a,b) -> [a;b]
              ) @ rest
            in
            breadth_first_labels instrs cur map rest
      end
let rec relabel_ map inp outp = function
  | [] -> outp
  | l::lrest ->
      let lbl l = match PTree.get l map with
        | None -> assert false
        | Some l -> P.of_int l
      in
      begin match PTree.get (lbl l) outp with
      | Some _ -> relabel_ map inp outp lrest
      | None ->
          let i = match PTree.get l inp with
            | None -> assert false
            | Some i -> i
          in
          let newi, next = match i with
            | Assume _ | Framestate _ -> assert false
            | Nop (q,l) -> Nop(q,lbl l),[l]
            | Op (q,w,l) -> Op(q,w,lbl l),[l]
            | Move (q, l) -> Move(q,lbl l),[l]
            | Call (q,w,e,l) -> Call(q,w,e,lbl l),[l]
            | Store (q,w,l) -> Store(q,w,lbl l),[l]
            | Load (q,w,l) -> Load(q,w,lbl l),[l]
            | Printexpr(q,l) -> Printexpr(q,lbl l),[l]
            | Printstring (q,l) -> Printstring(q,lbl l),[l]
            | Cond (q,a,b) -> Cond(q,lbl a, lbl b),[a;b]
            | IReturn (_) | Fail (_) -> i,[]
          in
          let outp = PTree.set (lbl l) newi outp in
          relabel_ map inp outp (next@lrest)
      end

let relabel instrs entry =
  let lblmap = breadth_first_labels instrs 10 PTree.empty [entry] in
  let instrs = relabel_ lblmap instrs PTree.empty [entry] in
  let entry = match PTree.get entry lblmap with
    | Some l -> P.of_int l
    | None -> assert false
  in
  instrs, entry


let next_lbls i =
  match i with
    | Assume _ | Framestate _ -> assert false
    | Nop (_, l)
    | Op (_,_,l)
    | Move (_, l)
    | Call (_,_,_,l)
    | Store (_,_,l)
    | Load (_,_,l)
    | Printexpr (_,l)
    | Printstring (_,l) ->
        [l]
    | Cond (_,a,b) ->
        [a;b]
    | Fail _
    | IReturn _ ->
        []

let declared_regs i =
  match i with
    | Assume _ | Framestate _ -> assert false
    | Op (_,r,l)
    | Call (_,_,r,l)
    | Load (_,r,l) ->
        [r]
    | Move (ml, l) ->
        List.map (fun (r,_) -> r) ml
    | Printexpr _
    | Cond _
    | Printstring _
    | IReturn _
    | Fail _
    | Nop _
    | Store _ ->
        []

let used_regs i =
  let apply_op = function
    | Reg r -> [r]
    | Cst _ -> []
  in
  let apply = function
    | Binexpr (_, o1, o2) -> (apply_op o1) @ (apply_op o2)
    | Unexpr (_, o) -> apply_op o
  in
  match i with
    | Assume _ | Framestate _ -> assert false
    | Nop (Some (Hint_Eq (a,b)), l) ->
        [a; b]
    | Nop (Some (Hint_Eq_val (a,_)), l) ->
        [a]
    | Op (e,r,l) ->
        apply e
    | Move (ml, l) ->
        List.fold_left (@) [] (List.map (fun (r,e) -> apply e) ml)
    | Call (_,es,r,l) ->
        List.fold_left (@) [] (List.map apply es)
    | Store (e1,e2,l) ->
        apply e1 @ apply e2
    | Load (e,r,l) ->
        apply e
    | Printexpr(e,l) ->
        apply e
    | Cond (e,a,b) ->
        apply e
    | Printstring (_, l)
    | Nop (None,l) ->
        []
    | Fail _ ->
        []
    | IReturn e ->
        apply e

module PSet = Set.Make(struct
  let compare = Stdlib.compare; type t = P.t
end)
module PMap = Map.Make(struct
  let compare = Stdlib.compare; type t = P.t
end)

let compute_liveness instrs entry =
  let preds = ref (PMap.add entry [] PMap.empty) in
  List.iter (fun (pos,i) ->
    let next = next_lbls i in
    List.iter (fun (n:label) ->
      match PMap.find_opt n (!preds) with
      | None -> preds := PMap.add n [pos] (!preds)
      | Some ps -> preds := PMap.add n (pos::ps) (!preds)
    ) next
  ) (PTree.elements instrs);
  let res = ref PMap.empty in
  let rec compute = function
    | [] -> ()
    | (pos, cur)::todo ->
      begin match PTree.get pos instrs with
      | None -> assert false
      | Some i ->
        let regs = used_regs i in
        let cur = PSet.union cur (PSet.of_list regs) in
        let fixpoint = match PMap.find_opt pos (!res) with
                       | None ->
                           res := PMap.add pos cur (!res);
                           false
                       | Some rs ->
                           if PSet.subset cur rs
                           then true
                           else (res := PMap.add pos (PSet.union rs cur) (!res);
                                 false)
        in
        let todo' = if fixpoint then [] else
          let cur = PSet.diff cur (PSet.of_list (declared_regs i)) in
          let ps = match PMap.find_opt pos (!preds) with
          | None -> []
          | Some ls -> ls
          in
          List.map (fun p -> (p,cur)) ps
        in
        compute (todo'@todo)
      end
  in
  let exits = List.fold_left (fun acc (pos,i) ->
      match i with
      | IReturn _ | Fail _ -> pos::acc
      | _ -> acc
    ) [] (PTree.elements instrs) in
  let _ = compute (List.map (fun e -> (e, PSet.empty)) exits) in
  !res

let shorten_liveness instrs entry =
  let res = ref instrs in
  let liveness = compute_liveness instrs entry in

  (*
  List.iter (fun (l,i) ->
    Printf.printf "%s: " (Printer.print_lbl l);
    begin match PMap.find_opt l liveness with
    | None -> Printf.printf "???"
    | Some rs ->
      List.iter (fun r ->
        Printf.printf "%s " (Printer.print_reg r)) (PSet.elements rs)
    end;
    Printf.printf "\n";
  ) (PTree.elements instrs);
  *)

  let patch (pos,i) =
    let patch next apply =
      match PTree.get next (!res) with
      | Some (IReturn _ | Fail _) -> ()
      | _ ->
        let live = match PMap.find_opt pos liveness with
        | None -> assert false
        | Some l -> l
        in
        let live' = match PMap.find_opt next liveness with
        | None ->assert false
        | Some l -> l
        in
        let dead = PSet.diff live live' in
        if PSet.is_empty dead
        then ()
        else begin
          let entry_label = fresh_label () in
          let end_label,to_insert = List.fold_left (fun istream r ->
              istream >>= (fun l -> Op (Unexpr (Assign, Cst (val_of_int 42)), r, l))
            ) (entry_label,[]) (PSet.elements dead) in
          let to_insert = (end_label, (Nop (None, next)))::to_insert in
          List.iter (fun (pos,i) -> res := PTree.set pos i (!res)) to_insert;
          res := PTree.set pos (apply entry_label) (!res)
        end
    in
    match i with
    | Assume _ | Framestate _ -> assert false
    | Nop (q,l) ->         patch l (fun l -> Nop(q,l))
    | Op (q,w,l) ->        patch l (fun l -> Op(q,w,l))
    | Move (q, l) ->       patch l (fun l -> Move(q,l))
    | Call (q,w,e,l) ->    patch l (fun l -> Call(q,w,e,l))
    | Store (q,w,l) ->     patch l (fun l -> Store(q,w,l))
    | Load (q,w,l) ->      patch l (fun l -> Load(q,w,l))
    | Printexpr(q,l) ->    patch l (fun l -> Printexpr(q,l))
    | Printstring (q,l) -> patch l (fun l -> Printstring(q,l))
    | Cond (q,a,b) ->
        patch a (fun a -> Cond (q,a,b));
        patch b (fun b -> Cond (q,a,b))
    | IReturn _ | Fail _ -> ()
  in
  List.iter patch (PTree.elements instrs);
  !res

let verify code =
  let check_lbl l =
    if (PTree.get l code = None)
    then begin
      Printf.printf "%s\n" (Printer.print_code code);
      Printf.printf "Broken jump to missing label %d\n" (int_of_positive l);
      assert false
    end
  in
  let verify (lbl, instr) =
    match instr with
    | Nop (oh,lbl) ->
        check_lbl lbl
    | Op (e,r,lbl) ->
        check_lbl lbl
    | Move (ml,lbl) ->
        check_lbl lbl
    | Call (f,el,r,lbl) ->
        check_lbl lbl
    | Cond (e,lbl1,lbl2) ->
        check_lbl lbl1; check_lbl lbl2
    | Store (ex1,ex2,lbl) ->
        check_lbl lbl
    | Load (ex,r,lbl) ->
        check_lbl lbl
    | Printstring (s,lbl) ->
        check_lbl lbl
    | Printexpr (e,lbl) ->
        check_lbl lbl
    | Assume _
    | Framestate _ ->
        assert false
    | IReturn _
    | Fail _ ->
        ()
  in
  List.iter verify (PTree.elements code)
;;

let rec compile_functioncall (pos: label) (fc:functioncall) (scope:scope) regs :
                                         (dyn_value * label * ((label * instruction) list)) =
  match fc with
  | Function (Var (Name "assert"), [e]) ->
      let v, pos, instrs1 = compile_exp pos e scope regs in
      let t,f = get2 fresh_label in
      let instrs2 = typecase pos v
        (fun a_nil  l -> [(l, Nop (None,f))])
        (fun a_bool l -> [(l, Cond (test_eq a_bool zero, f, t))])
        (fun an_int l -> [(l, Nop (None,t))])
        (fun a_tbl  l -> [(l, Nop (None,t))]) in
      let fail = Fail ("assertion failed!") in
      the_true, t, (f, fail) :: (instrs1 @ instrs2)
  | Function (Var (Name "print"), [e]) ->
      let v, pos, instrs = compile_exp pos e scope regs in
      let next = fresh_label () in
      let instrs2 = typecase pos v
        (fun _ l -> [(l, Printstring ("nil", next))])
        (fun a_bool l ->
          let c1,c2 = get2 fresh_label in
          [
            (l, Cond (Binexpr (Eq, a_bool, zero), c1, c2));
            (c1, Printstring ("false", next));
            (c2, Printstring ("true", next));
          ])
        (fun an_int l -> [(l, Printexpr (exp_of_op an_int, next))])
        (fun a_tbl  l ->
          let c = fresh_label () in
            [(l, Printstring ("table: ", c));
             (c, Printexpr (exp_of_op a_tbl, next))])
      in
      the_nil, next, instrs2 @ instrs
  | Function (Var (Name "__hint_int"), [PrefixExp (Var (Name n))]) ->
      let c = fresh_label () in
      let hint = match lookup n scope with
      | FromLocal (Local (t, v)) -> Some (Params.Hint_Eq_val (t, t_int_v))
      | _ -> None
      in
      the_nil, c, [(pos, Nop(hint, c))]
  | Function (Var (Name "__hint_tbl"), [PrefixExp (Var (Name n))]) ->
      let c = fresh_label () in
      let hint = match lookup n scope with
      | FromLocal (Local (t, v)) -> Some (Params.Hint_Eq_val (t, t_tbl_v))
      | _ -> None
      in
      the_nil, c, [(pos, Nop(hint, c))]
  | Function (Var (Name "__hint_val"), [PrefixExp (Var (Name n)); (False|True|Integer _) as h]) ->
      let c1,c2 = get2 fresh_label in
      let th, vh = match h with
      | False     -> (t_bool_v, val_of_int 0)
      | True      -> (t_bool_v, val_of_int 1)
      | Integer i -> (t_int_v,  val_of_int i)
      | _ -> assert false
      in
      let instrs = match lookup n scope with
      | FromLocal (Local (t, v)) ->
          [(pos, Nop(Some (Params.Hint_Eq_val (t, th)), c1));
           (c1,  Nop(Some (Params.Hint_Eq_val (v, vh)), c2))]
      | _ ->
          [(pos, Nop(None, c2))]
      in
      the_nil, c2, instrs
  | Function (Var (Name "__hint_val"), _)
  | Function (Var (Name "__hint_int"), _) ->
      failwith "unsupported hint"
  | Function (Var (Name n), es) ->
      begin match lookup n scope with
      | FromLocal (Function f)
      | FromOuter (Function f)
      | FromGlobal (Function f) ->
          let pos, instrs, args = List.fold_left (fun (pos, instrs, args) e ->
            let (t,v), pos, instrs' = compile_exp pos e scope regs in
            pos, instrs'@instrs, (exp_of_op t)::(exp_of_op v)::args) (pos, [], []) es
          in
          let c1,c2 = get2 fresh_label in
          let t,v = get2 regs#get_temp in
          let call = (pos, Call (f, args, v, c1)) in
          let lt = (c1, Load (return_type_cell, t, c2)) in
          (Reg t, Reg v), c2, call::lt::instrs
      | _ ->
          failwith (Printf.sprintf "cannot statically resolve call target %s" n)
      end
  | Function _ ->
      failwith "unsupported function call"
  | Method _ ->
      failwith "unsupported method call"

and compile_exp_tbl (pos: label) (e:exp) (scope:scope) (regs) : (dyn_value * label * ((label * instruction) list)) = 
  match e with
  | Table tb ->
      let p = regs#get_temp () in
      let apply (pos, instrs) = function
        | Some e1, e2 ->
            failwith "only integer indices are supported"
        | None, e1 ->
            let (vt,vv), pos, instrs' = compile_exp pos e1 scope regs in
            (pos,instrs'@instrs) >>=
              (fun l -> Op (Binexpr (Plus, Reg p, Cst(val_of_int 1)), p, l)) >>=
              (fun l -> Store (exp_of_op vt, exp_of_op (Reg p), l)) >>=
              (fun l -> Op (Binexpr (Plus, Reg p, Cst(val_of_int 1)), p, l)) >>=
              (fun l -> Store (exp_of_op vv, exp_of_op (Reg p), l))
      in
      let len = List.length tb in
      let addr = Cst (fresh_heapcell ((len*2)+1)) in
      let pos,instrs = (pos,[]) >>=
        (fun l -> Op (Unexpr (Assign, addr), p, l)) >>=
        (fun l -> Store (exp_of_op (Cst (val_of_int len)), (exp_of_op (Reg p)), l))
      in
      let pos, instrs = List.fold_left apply (pos, instrs) tb in
      (t_tbl, addr), pos, instrs
  | _ -> compile_exp pos e scope regs

and compile_exp (pos: label) (e:exp) (scope:scope) (regs) : (dyn_value * label * ((label * instruction) list)) = 
  match e with
  | Table tb ->
      failwith "only global tables are supported"
  | PrefixExp (Var (Name n)) ->
      begin match lookup n scope with
      | FromLocal (Function _)
      | FromOuter (Function _)
      | FromGlobal (Function _) ->
        failwith "function references not supported"
      | FromLocal (Local (t,v)) ->
        (Reg t, Reg v), pos, []
      | FromGlobal (Global (th,vh)) ->
        let t, v = get2 regs#get_temp in
        let pos,instrs = (pos,[]) >>=
          (fun l -> Load (exp_of_op (Cst th), t, l)) >>=
          (fun l -> Load (exp_of_op (Cst vh), v, l))
        in
        (Reg t, Reg v), pos, instrs
      | FromOuter _ ->
        failwith (Printf.sprintf "Closures not supported, cannot capture %s" n)
      | NotFound ->
        failwith (Printf.sprintf "variable %s not found, could be nil or global which is not supported" n)
        (* the_nil, pos, [] *)
      end
  | PrefixExp (Exp e) ->
      compile_exp pos e scope regs
  | PrefixExp (FunctionCallExp e) ->
      compile_functioncall pos e scope regs
  | PrefixExp (Var (IndexTable (te, ie))) ->
      let lhs, pos, instrs0 = compile_exp pos (PrefixExp te) scope regs in
      let (it, iv), pos, instrs1 = compile_exp pos ie scope regs in
      let tres, vres = get2 regs#get_temp in
      let sz, p = get2 regs#get_temp in
      let c1,c2,c3,c4,c5 = get5 fresh_label in
      let c6,c7,c8,c1',next = get5 fresh_label in
      let c9,c2' = get2 fresh_label in
      (* non int index -> nil *)
      let instrs3 = [
        (pos, Cond (test_eq it t_int, c2, c1));
        (c1,  Op (Unexpr (Assign, t_nil), tres, c1'));
        (c1', Op (Unexpr (Assign, zero),  vres, next))] in
      let instrs4 = typecase c2 lhs
        (fun _ l -> [(l, Fail "attempt to index a nil value")])
        (fun _ l -> [(l, Fail "attempt to index a boolean value")])
        (fun _ l -> [(l, Fail "attempt to index a number value")])
        (fun a_table l -> [
          (l,   Load (exp_of_op a_table, sz, c2'));
          (c2', Op (Unexpr (Assign, a_table), p, c3))
        ]) in
      let instrs5 = [
        (c3, Cond (Binexpr(Geq, zero, iv), c1, c4));
        (c4, Cond (Binexpr(Lt, Reg sz, iv), c1, c5));
        (c5, Op (Binexpr (Mult, iv, Cst(val_of_int 2)), sz, c6));
        (c6, Op (Binexpr (Plus, Reg p, Reg sz), p, c7));
        (c7, Load (exp_of_op (Reg p), vres, c8));
        (c8, Op (Binexpr (Minus, Reg p, Cst(val_of_int 1)), p, c9));
        (c9, Load (exp_of_op (Reg p), tres, next))] in
      (Reg tres, Reg vres), next, instrs0@instrs1@instrs3@instrs4@instrs5
  | FunctionDef (ns, u, b) ->
      failwith "unsupported position for functions definition"
  | BinOp (Concat, e1, e2) ->
      failwith "concat and strings not supported"
  | UnOp (BitwiseNot, e) ->
      failwith "bitwise not not supported"
  | UnOp (Length, e) ->
      let res = regs#get_temp () in
      let next = fresh_label () in
      let v, pos, instrs = compile_exp pos e scope regs in
      let instrs2 = typecase pos v
        (fun _ l -> [(l, Fail "attempt to get length of a nil value")])
        (fun _ l -> [(l, Fail "attempt to get length of a boolean value")])
        (fun _ l -> [(l, Fail "attempt to get length of a number value")])
        (fun a_table l -> [(l, Load (exp_of_op a_table, res, next))])
      in
      (t_int, Reg res), next, instrs@instrs2
  | UnOp (UnaryMinus, e) ->
      let v, pos, instrs = compile_exp pos e scope regs in
      let next = fresh_label () in
      let rt, rv = get2 regs#get_temp in
      let instrs2 = typecase pos v
        (fun _ l -> [(l, Fail "attempt to perform arithmetic on nil")])
        (fun _ l -> [(l, Fail "attempt to perform arithmetic on a boolean value")])
        (fun an_int l ->
          let c = fresh_label () in [
            (l, Op (Unexpr (Assign, t_int), rt, c));
            (c, Op (Unexpr (UMinus, an_int), rv, next));
          ])
        (fun _ l -> [(l, Fail "attempt to perform arithmetic on a table value")])
      in
      (Reg rt, Reg rv), next, instrs @ instrs2
  | UnOp (LogicalNot, e) ->
      let v, pos, instrs = compile_exp pos e scope regs in
      let next = fresh_label () in
      let rt, rv = get2 regs#get_temp in
      let c = fresh_label () in
      let instrs2 = [(pos, Op (Unexpr (Assign, t_bool), rt, c))] in
      let instrs3 = typecase c v
        (fun _ l -> [(l, Op (Unexpr (Assign, one), rv, next))])
        (fun an_bool l -> [(l, Op (Unexpr (Neg, an_bool), rv, next))])
        (fun _ l -> [(l, Op (Unexpr (Assign, zero), rv, next))])
        (fun _ l -> [(l, Op (Unexpr (Assign, zero), rv, next))])
      in
      (Reg rt, Reg rv), next, instrs @ instrs2 @ instrs3
  | BinOp (LogicalAnd, e1, e2) ->
      let (t1,v1), pos, instrs1 = compile_exp pos e1 scope regs in
      let (t2,v2), pos, instrs2 = compile_exp pos e2 scope regs in

      let next = fresh_label () in
      let rt, rv = get2 regs#get_temp in

      let instrs3 = typecase pos (t1,v1)
        (fun _ l ->
          let c = fresh_label () in [
          (l, Op (Unexpr (Assign, t_nil), rt, c));
          (c, Op (Unexpr (Assign, zero), rv, next));
        ])
        (fun a_bool l ->
          let c1,c2,c3,c4,c5 = get5 fresh_label in [
            (l, Op (Binexpr (Eq, a_bool, zero), rv, c1));
            (c1, Op (Unexpr (Neg, Reg rv), rv, c2));
            (c2, Cond (exp_of_op (Reg rv), c3, c5));

            (c3, Op (Unexpr (Assign, t2), rt, c4));
            (c4, Op (Unexpr (Assign, v2), rv, next));

            (c5, Op (Unexpr (Assign, t_bool), rt, next));
          ])
        (fun _ l ->
          let c = fresh_label () in [
          (l, Op (Unexpr (Assign, t2), rt, c));
          (c, Op (Unexpr (Assign, v2), rv, next));
        ])
        (fun _ l ->
          let c = fresh_label () in [
          (l, Op (Unexpr (Assign, t2), rt, c));
          (c, Op (Unexpr (Assign, v2), rv, next));
        ])
      in
      (Reg rt, Reg rv), next, instrs1 @ instrs2 @ instrs3
  | BinOp (LogicalOr, e1, e2) ->
      let (t1,v1), pos, instrs1 = compile_exp pos e1 scope regs in
      let (t2,v2), pos, instrs2 = compile_exp pos e2 scope regs in

      let next = fresh_label () in
      let rt, rv = get2 regs#get_temp in

      let instrs3 = typecase pos (t1,v1)
        (fun _ l ->
          let c = fresh_label () in [
          (l, Op (Unexpr (Assign, t2), rt, c));
          (c, Op (Unexpr (Assign, v2), rv, next));
        ])
        (fun a_bool l ->
          let c1,c2,c3,c4,c5 = get5 fresh_label in [
            (l, Op (Binexpr (Eq, a_bool, zero), rv, c1));
            (c1, Op (Unexpr (Neg, Reg rv), rv, c2));
            (c2, Cond (exp_of_op (Reg rv), c5, c3));

            (c3, Op (Unexpr (Assign, t2), rt, c4));
            (c4, Op (Unexpr (Assign, v2), rv, next));

            (c5, Op (Unexpr (Assign, t_bool), rt, next));
          ])
        (fun _ l ->
          let c = fresh_label () in [
          (l, Op (Unexpr (Assign, t1), rt, c));
          (c, Op (Unexpr (Assign, v1), rv, next));
        ])
        (fun _ l ->
          let c = fresh_label () in [
          (l, Op (Unexpr (Assign, t1), rt, c));
          (c, Op (Unexpr (Assign, v1), rv, next));
        ])
      in
      (Reg rt, Reg rv), next, instrs1 @ instrs2 @ instrs3
  | BinOp ((Equality|Inequality) as op, e1, e2) ->
      let (t1,v1), pos, instrs1 = compile_exp pos e1 scope regs in
      let (t2,v2), pos, instrs2 = compile_exp pos e2 scope regs in
      let c1,c2,c3,c4 = get4 fresh_label in
      let r1,r2  = get2 regs#get_temp in
      let instrs3 =
        (pos, Op (Binexpr (Eq, t1, t2), r1, c1)) ::
          (c1, Op (Binexpr (Eq, v1, v2), r2, c2)) ::
            (c2, Op (Binexpr (Plus, Reg r1, Reg r2), r1, c3)) ::
              (c3, Op (Binexpr (Eq, Reg r1, Cst (val_of_int 2)), r1, c4)) :: []
      in
      let next, instrs3 = if (op == Inequality)
        then begin
          let c = fresh_label () in
          c, (c4, Op (Unexpr (Neg, Reg r1), r1, c)) :: instrs3
        end
        else c4, instrs3
      in
      (t_bool, Reg r1), next, instrs1 @ instrs2 @ instrs3
  | BinOp ((Addition|Subtraction|Multiplication|Greater|Less|GreaterEq|
            LessEq|FloatDivision|FloorDivision|Modulo|Exponentiation|
            BitwiseAnd|BitwiseOr|BitwiseXor|ShiftRight|ShiftLeft) as o, e1, e2) ->
      let v1, pos, instrs1 = compile_exp pos e1 scope regs in
      let v2, pos, instrs2 = compile_exp pos e2 scope regs in
      let next = fresh_label () in
      let res  = regs#get_temp () in
      let instrs3 = typecase pos v1
        (fun _ l -> [(l, Fail "attempt to perform arithmetic on nil")])
        (fun _ l -> [(l, Fail "attempt to perform arithmetic on a boolean value")])
        (fun a_int l ->
          typecase l v2
            (fun _ l -> [(l, Fail "attempt to perform arithmetic on nil")])
            (fun _ l -> [(l, Fail "attempt to perform arithmetic on a boolean value")])
            (fun b_int l ->
              [(l, Op (Binexpr (arith_binop o, a_int, b_int), res, next))]
            )
            (fun _ l -> [(l, Fail "attempt to perform arithmetic on a table value")])
        )
        (fun _ l -> [(l, Fail "attempt to perform arithmetic on a table value")])
      in
      let typ = match o with
      | Greater|Less|GreaterEq|LessEq -> t_bool
      | _ -> t_int
      in
      (typ, Reg res), next, (instrs3 @ instrs2 @ instrs1)
  | Nil ->
      (t_nil, zero), pos, []
  | False ->
      the_false, pos, []
  | True  ->
      the_true, pos, []
  | Integer i  ->
      (t_int, Cst (val_of_int i)), pos, []
  | Float f  ->
      failwith "floats not supported"
  | LiteralString s ->
      failwith "strings not supported"
  | Vararg ->
      failwith "varargs not supported"

and compile_stat (pos: label) (statement:stat) (scope:scope) (regs) :
                                    (label * (label * instruction) list * scope * fun_ref list) =
  match statement with
  | FunctionCall e ->
      let res, pos, instrs = compile_functioncall pos e scope regs in
      pos, instrs, scope, []
  | LocalAssign (ns, es) ->
      let rec assign (pos, instrs, scope, funref) ns es =
        match ns, es with
        | [], [] ->
          pos, instrs, scope, funref
        | n::nrest, (FunctionDef def)::erest ->
          begin match lookup n scope with
          | NotFound ->
              let fun_id = fresh_fun_id () in
              let scope = declare_local n (Function fun_id) scope in
              let funref = (fun_id, scope, def)::funref in
              let acc = pos, instrs, scope, funref in
              assign acc nrest erest
          | _ ->
              failwith "function references cannot be changed"
          end
        | n::nrest, e::erest ->
          let value, pos, instrs1 = compile_exp pos e scope regs in
          begin match lookup n scope with
          | FromGlobal (Function _)
          | FromOuter (Function _)
          | FromLocal (Function _) ->
              failwith "function references cannot be changed";
          | NotFound
          | FromGlobal _
          | FromOuter _ ->
              let local = get2 regs#get_local in
              let scope = declare_local n (Local local) scope in
              let pos, instrs2 = store_local pos value local in
              let acc = pos, instrs2@instrs1@instrs, scope, funref in
              assign acc nrest erest
          | FromLocal (Local local) ->
              (* fails since this would not respect parallel semantics for multiple assigns, need to first eval all rhs like in Assign below *)
              if (nrest <> []) then
                failwith "no support for multiple local assign to existing val";
              let pos, instrs2 = store_local pos value local in
              let acc = pos, instrs2@instrs1@instrs, scope, funref in
              assign acc nrest erest
          end
        | _, _ ->
            failwith ("no support for tuple local assignment")
      in
      begin match es with
      | Some es -> assign (pos, [], scope, []) ns es
      | None -> assign (pos, [], scope, []) ns (List.map (fun _ -> Nil) ns)
      end
  | Assign (ns, es) ->
      let rec eval ((pos, vs, instrs, scope, funref) as acc) ns es =
        match ns, es with
        | (Name n)::nrest, (FunctionDef def)::erest ->
          begin match lookup n scope with
          | NotFound ->
              let fun_id = fresh_fun_id () in
              let scope = declare_global n (Function fun_id) scope in
              let funref = (fun_id, scope, def)::funref in
              let acc = pos, vs, instrs, scope, funref in
              eval acc nrest erest
          | _ ->
              failwith "function references cannot be changed"
          end
        | (IndexTable (te, ie))::nrest, e::erest ->
          let v, pos, instrs' = compile_exp pos e scope regs in
          let acc = pos, v::vs, instrs'@instrs, scope, funref in
          eval acc nrest erest
        | (Name n)::nrest, e::erest ->
          begin match lookup n scope with
          | FromLocal _ ->
              let v, pos, instrs' = compile_exp pos e scope regs in
              let acc = pos, v::vs, instrs'@instrs, scope, funref in
              eval acc nrest erest
          | NotFound
          | FromGlobal _ ->
              let v, pos, instrs' = compile_exp_tbl pos e scope regs in
              let acc = pos, v::vs, instrs'@instrs, scope, funref in
              eval acc nrest erest
          | _ -> acc
          end
        | _ ->
          acc
      in
      let pos, vs, instrs0, scope, funref = eval (pos, [], [], scope, []) ns es in

      let rec assign ((pos, instrs, scope, funref) as acc) ns es =
        match ns, es with
        | [], [] ->
          acc
        | (IndexTable (te, ie))::nrest, (vt,vv)::vrest ->
          let lhs, pos, instrs0 = compile_exp pos (PrefixExp te) scope regs in
          let (it, iv), pos, instrs1 = compile_exp pos ie scope regs in
          let sz, p = get2 regs#get_temp in
          let c1,c2,c3,c4,c5 = get5 fresh_label in
          let c6,c7,c8,c9,c10 = get5 fresh_label in
          let c11,c12,c2' = get3 fresh_label in
          let instrs3 = [
            (pos, Cond (test_eq it t_int, c2, c1));
            (c1,  Fail "sorry, only integer indices are supported")] in
          let instrs4 = typecase c2 lhs
            (fun _ l -> [(l, Fail "attempt to index a nil value")])
            (fun _ l -> [(l, Fail "attempt to index a boolean value")])
            (fun _ l -> [(l, Fail "attempt to index a number value")])
            (fun a_table l ->
              [(l,   Load (exp_of_op a_table, sz, c2'));
               (c2', Op (Unexpr (Assign, a_table), p, c3))]) in
          let instrs5 = [
            (c3, Cond (Binexpr(Geq, zero, iv), c4, c5));
            (c4, Fail "sorry, no support for growing tables");
            (c5, Cond (Binexpr(Lt, Reg sz, iv), c6, c7));
            (c6, Fail "sorry, no support for growing tables");
            (c7, Op (Binexpr (Mult, iv, Cst(val_of_int 2)), sz, c8));
            (c8, Op (Binexpr (Plus, Reg p, Reg sz), p, c9));
            (c9, Store (exp_of_op vv, exp_of_op (Reg p), c10));
            (c10, Op (Binexpr (Minus, Reg p, Cst(val_of_int 1)), p, c11));
            (c11, Store (exp_of_op vt, exp_of_op (Reg p), c12))] in
          let acc = c12, instrs0@instrs1@instrs3@instrs4@instrs5@instrs, scope, funref in
          assign acc nrest vrest
        | (Name n)::nrest, vs ->
          let v,vrest = match vs with
            | v::vrest -> v, vrest
            | [] -> the_nil, []
          in
          begin match lookup n scope with
          | FromGlobal (Function f)
          | FromLocal (Function f)
          | FromOuter (Function f) ->
              (* handled in "eval" *)
              assign acc nrest vrest
          | FromLocal (Local local) ->
              let pos, instrs2 = store_local pos v local in
              let acc = pos, instrs2@instrs, scope, funref in
              assign acc nrest vrest
          | NotFound ->
              let addr = fresh_heapcell 1, fresh_heapcell 1 in
              let scope = declare_global n (Global addr) scope in
              let pos, instrs2 = store_global pos v addr in
              let acc = pos, instrs2@instrs, scope, funref in
              assign acc nrest vrest
          | FromGlobal (Global addr) ->
              let pos, instrs2 = store_global pos v addr in
              let acc = pos, instrs2@instrs, scope, funref in
              assign acc nrest vrest
          | FromOuter _ ->
              failwith (Printf.sprintf "Closures not supported, cannot capture %s" n)
          end
        | _, [] ->
          failwith ("no support for surplus names in assignment")
        | [], _ ->
          failwith ("no support for tuple assignment")
      in
      assign (pos, instrs0, scope, funref) ns (List.rev vs)
  | If (ebs, b_else) ->
      let next = fresh_label () in

      let rec apply (pos, instrs, funref) ebs =
        match ebs with
        | [] ->
          (pos, instrs, funref)
        | (e,b)::ebs ->
          let v, pos, instrs' = compile_exp pos e scope regs in
          let matches, skip = get2 fresh_label in
          let instrs2 = typecase pos v
            (fun _ l -> [(l, Nop (None,skip))])
            (fun a_bool l -> [(l, Cond (exp_of_op a_bool, matches, skip))])
            (fun _ l -> [(l, Nop (None,matches))])
            (fun _ l -> [(l, Nop (None,matches))])
          in
          let pos, instrs3, funref = compile_block matches b scope regs funref in
          let merge = match pos with
            | None -> []
            | Some pos -> [(pos, Nop (None,next))]
          in
          apply (skip, merge @ instrs' @ instrs2 @ instrs3 @ instrs, funref) ebs
      in
      let pos, instrs, funref = apply (pos, [], []) ebs in

      let pos, instrs', funref =
        match b_else with
        | Some b_else ->
            compile_block pos b_else scope regs funref
        | None ->
            Some pos, [], funref
      in
      let merge = match pos with
        | None -> []
        | Some pos -> [(pos, Nop (None,next))]
      in
      next, merge @ instrs @ instrs', scope, funref
  | DoEnd b ->
      begin match compile_block pos b scope regs [] with
      | Some pos, instrs, funref ->
          pos, instrs, scope, funref
      | None, instrs, funref ->
          fresh_label (), instrs, scope, funref
      end
  | WhileDoEnd (e,b) ->
      let check = pos in
      let v, pos, instrs = compile_exp pos e scope regs in
      let body, fin = get2 fresh_label in
      let instrs2 = typecase pos v
        (fun _ l -> [(l, Nop (None,fin))])
        (fun a_bool l -> [(l, Cond (exp_of_op a_bool, body, fin))])
        (fun _ l -> [(l, Nop (None,body))])
        (fun _ l -> [(l, Nop (None,body))])
      in
      let body_end, instrs3, funref = compile_block body b scope regs [] in
      let instrs4 = match body_end with
        | None -> []
        | Some body_end -> [(body_end, Nop (None, check))]
      in
      fin, instrs @ instrs2 @ instrs3 @ instrs4, scope, funref
  | Label n ->
      failwith "unsupported label"
  | Break ->
      failwith "unsupported break"
  | Goto n ->
      failwith "unsupported goto"
  | RepeatUntil (b,e) ->
      let body = pos in
      let body_end, instrs1, funref = compile_block pos b scope regs [] in
      let body_end = match body_end with
        | None -> fresh_label ()
        | Some body_end -> body_end
      in
      let v, pos, instrs2 = compile_exp body_end e scope regs in
      let next = fresh_label () in
      let instrs3 = typecase pos v
        (fun _ l -> [(l, Nop (None,body))])
        (fun a_bool l -> [(l, Cond (exp_of_op a_bool, next, body))])
        (fun _ l -> [(l, Nop (None,next))])
        (fun _ l -> [(l, Nop (None,next))])
      in
      next, instrs1 @ instrs2 @ instrs3, scope, funref
  | ForStep (n, e1, e2, None, b) ->
      (* error messages for non numeric e1/e2 are not quite right *)
      let scope = Block (scope, VarMap.empty) in
      let end_val = "--loop-end--" in
      let pos, instrs1, scope, funref1 = compile_stat pos (LocalAssign([n], Some [e1])) scope regs in
      let pos, instrs2, scope, funref2 = compile_stat pos (LocalAssign([end_val], Some [e2])) scope regs in
      let body, next = get2 fresh_label in
      let condition = pos in
      let (_,condition_val), pos, instrs3 = compile_exp pos (BinOp (GreaterEq, PrefixExp (Var (Name n)), PrefixExp (Var (Name end_val)))) scope regs in
      let instrs4 = [(pos, Cond (exp_of_op condition_val, body, next))] in
      let body_end, instrs5, funref3 = compile_block body b scope regs (funref1@funref2) in
      let instrs6 = match body_end with
      | None -> []
      | Some pos ->
          let pos, instrs', _, _= compile_stat pos (
            LocalAssign([n], Some [BinOp (Addition, PrefixExp (Var (Name n)), Integer 1)])) scope regs in
          [(pos, Nop (None, condition))] @ instrs'
      in
      next, instrs1@instrs2@instrs3@instrs4@instrs5@instrs6, scope, funref3
  | ForStep (n, e1, e2, Some eo, b) ->
      failwith "unsupported for"
  | ForIn (ns, es, b) ->
      failwith "unsupported for in"

and compile_block entry (sts, ret) scope regs funref =
  let scope = Block (scope, VarMap.empty) in
  let pos, instrs, scope, funref = List.fold_left (fun (pos, instrs, scope, funref) st ->
    let next, res, scope, funref' = compile_stat pos st scope regs in
    next, res@instrs, scope, funref'@funref) (entry, [], scope, funref) sts in
  match ret with
  | Some (e::[]) ->
      let (t,v), next, instrs1 = compile_exp pos e scope regs in

      let next' = fresh_label () in
      let instrs2 = [
        (next, Store ((exp_of_op t), return_type_cell, next'));
         next', IReturn (exp_of_op v)] in

      None, (instrs2 @ instrs1 @ instrs), funref
  | None ->
      Some pos, instrs, funref
  | _ ->
      failwith "unsupported block return statement"

and compile_fun fun_id (formals:name list) (body:block) scope : (coq_function * fun_ref list) =
  let regs = new register_handler in
  let entry = fresh_label () in
  let scope = Function (fun_id, scope) in
  let scope = Block (scope, VarMap.empty) in
  let scope, args = List.fold_left (fun (scope, rest) n ->
    if (n = "self") then failwith "only support for functions, no methods (add 'local' to fix)";
    let t,v = get2 regs#get_arg in
    let scope = declare_local n (Local (t,v)) scope in
    scope, t::v::rest) (scope, []) formals
  in
  let next, instrs, funref = compile_block entry body scope regs [] in
  let instrs = match next with
    | None -> instrs
    | Some pos ->
        let next' = fresh_label () in
        (pos, Store (exp_of_op t_nil, return_type_cell, next')) ::
          (next', IReturn (exp_of_op zero)) :: instrs
  in
  (* zero initialize all used regs *)
  let pre_entry = fresh_label () in
  let init_end,init_code = List.fold_left (fun istream r ->
    istream >>= (fun l -> Op (Unexpr (Assign, Cst(val_of_int 0)), r, l)))
      (pre_entry,[]) (regs#get_locals_and_temps ())
  in
  let instrs = init_code @ [(init_end, Nop(None,entry))] @ instrs in
  let entry = pre_entry in
  (* convert instr list into PTree *)
  let instrs = List.fold_left (fun p (l,i) ->
    assert ((PTree.get l p) = None);
    PTree.set l i p) PTree.empty instrs in
  let instrs = shorten_liveness instrs entry in
  verify instrs;
  (* breadth first relabling *)
  let instrs,entry = relabel instrs entry in
  let version = {ver_code=instrs; ver_entry=entry} in
  {fn_params=(args); fn_base=version; fn_opt=None}, funref
;;

let compile filename =
  let b = parse_with_error (Lexing.from_channel (open_in filename)) in
  let rec compile_all next acc =
    match next with
    | [] -> acc
    | (f, scope, (names, _, b))::rest ->
      let fc, funref = compile_fun f names b scope in
      assert ((PTree.get f acc) = None);
      let acc = PTree.set f fc acc in
      compile_all (funref@rest) acc
  in
  let lbl = fresh_fun_id () in
  let global = Global VarMap.empty in
  {prog_main=lbl;
   prog_funlist = (compile_all [(lbl, global, ([], None, b))] PTree.empty)}
