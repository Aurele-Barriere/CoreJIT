(* Tests an optimization on a given program *)
open Common
open BinNums
open Maps
open Values
open SpecIR
open Interpreter
open Jit
open Printf
open Printer
open Camlcoq
open Ast
open Lexer
open Lexing
open Memory
open Assume_insertion
open Assume_insertion_delay
open Framestate_insertion
open Const_prop
open Inlining
open Lowering
open Optimizer
open Profiler_types
   
let print_position outx lexbuf =
  let pos = lexbuf.lex_curr_p in
  fprintf outx "%s:%d:%d" pos.pos_fname
    pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1)

   
let parse_with_error lexbuf =
  try Parser.prog Lexer.read lexbuf with
  | SyntaxError msg ->
     fprintf stderr "%a: %s\n" print_position lexbuf msg;
     None
  | Parser.Error ->
     fprintf stderr "%a: syntax error\n" print_position lexbuf;
     exit (-1)
   
let get_program filename: program =
  let inx = open_in filename in
  let lexbuf = Lexing.from_channel inx in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = filename };
  let (apo:Ast.aprogram option) = parse_with_error lexbuf in
  match apo with
  | None -> let _ = close_in inx in failwith "Failed to parse a program"
  | Some ap -> let _ = close_in inx in Ast.convert_program ap

let main =
  let _ = Printf.printf "%s" "Testing optimizations\n" in
  let path = ref "progs_specIR/test.specir" in
  let p = get_program !path in
  let fid1 = (Coq_xH) in
  let call_lbl1 = Coq_xO(Coq_xH) in (* lbl2 *)
  let fs_lbl1 = Coq_xI(Coq_xH) in   (* lbl3 *)
  let fid2 = Coq_xO(Coq_xH) in
  let call_lbl2 =  Coq_xI (Coq_xH) in
  let fs_lbl2 = Coq_xO(Coq_xO(Coq_xH)) in
  let fid3 = Coq_xI(Coq_xH) in
  let fs_lbl3 = Coq_xO(Coq_xH) in
  let guard = [Binexpr(Eq,Reg Coq_xH,Cst Z0)] in

  let fs_list = (fid1,[fs_lbl1])::(fid2,[fs_lbl2])::(fid3,[fs_lbl3])::[] in
  let opt_list = (fid3,AS_INS (guard,fs_lbl3)):: (* insert assume in Fun3 *)
                   (fid2,INLINE call_lbl2)::     (* inline Fun3 in Fun2 *)
                     (fid1,INLINE call_lbl1)::[] in (* inline Fun2 in Fun1 *)

  begin match (test_optimizer p fs_list opt_list) with
  | OK optp ->
     Printf.printf "After Optimizations\n %s" (print_program optp)
  | Error s -> Printf.printf "%s\n" s
  end
