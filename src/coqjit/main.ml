(* Looping the extracted jit_step function *)
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

   
(* Parsing and Lexing functions *)
(* https://v1.realworldocaml.org/v1/en/html/parsing-with-ocamllex-and-menhir.html *)
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


exception Return of (value*jit_state)
exception RunTimeErr of (string*jit_state)

let get_program filename: program =
  let inx = open_in filename in
  let lexbuf = Lexing.from_channel inx in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = filename };
  let (apo:Ast.aprogram option) = parse_with_error lexbuf in
  match apo with
  | None -> let _ = close_in inx in failwith "Failed to parse a program"
  | Some ap -> let _ = close_in inx in Ast.convert_program ap

let get_lua_program filename: program =
  Frontend.compile filename


(* Looping the jit step *)
let rec jit_main (s:jit_state) =
  match (Jit.jit_step s) with
  | Error mess -> raise (RunTimeErr (mess, s))
  | OK (nexts, t) ->
     let _ = print_trace t in
     match (jit_final_value nexts) with
     | None -> jit_main nexts   (* recursive call *)
     | Some v -> raise (Return (v, nexts))

let print_debug_program = ref false;;

(* Initializing and executing the JIT *)
let jit (p:program) =
  if (!print_debug_program) then begin
    let _ = Printf.printf ("\027[96mInput Program:\027[0m \n%s\n%!") (print_program p) in
    Printf.printf ("\027[96mStarting the JIT\027[0m\n%!")
  end;
  match initial_jit_state p with
  | Error mess -> Printf.printf ("\027[33mInitialization Error:\027[0m %s\n") mess
  | OK js -> try jit_main js with
               Return (v,js) -> begin
                 Printf.printf ("\027[33mEnd of execution, final value is:\027[0m %s\n") (print_value v);
                 if (!print_debug_program) then
                     Printf.printf ("\027[96mFinal Program:\027[0m \n%s\n") (print_program js.prog)
               end
             | RunTimeErr (e,js) -> begin
               Printf.printf ("\027[33mRun-Time Error:\027[0m %s\n%!") e;
               if (!print_debug_program) then
                 Printf.printf ("\027[96mFinal JIT Program:\027[0m \n%s\n") (print_program js.prog)
             end
;;

(* provide a re-entry hook for the jit *)
Native_prim.jit_main_hook := function state ->
  try jit_main state with
  | Return (v,p) -> (v,p)
  | RunTimeErr _ as ex -> raise ex
;;
Native.init ()

let main =
  let path = ref "" in
  let enable_lua = ref false in
  let cmd_args = [
    ("-o", Arg.Set Printer.print_debug_opt_fun, "Print Optimized Functions");
    ("-s", Arg.Set Printer.print_debug_strings, "Print Debug Strings");
    ("-p", Arg.Set print_debug_program, "Print Debug Program");
    ("-k", Arg.Set Flags.disable_profiler_hints, "Disable profiler using hints");
    ("-n", Arg.Set Flags.enable_native, "Enable unverified native backend");
    ("-f", Arg.Set enable_lua, "Enable unverified lua frontend");
    ("-t", Arg.Set Flags.enable_frontend_assert, "Enable asserts in frontend");
    ("-d", Arg.Set Flags.print_debug_native,  "Print Native Debugging");
    ("-a", Arg.Set Flags.print_debug_native_code,  "Print Native Code");
    ("-m", Arg.Set Flags.print_debug_native_heap,  "Print Native Heap");
    ("-c", Arg.Set Flags.native_call_always_jit_loop, "Native call always goes through jit_step, even when calling optimized code");
  ] in
  let usage () =
    Printf.printf "%s" "\027[91mPlease use the jit executable on exactly one argument: the program to execute\027[0m\n\027[33m  Example: \027[0m ./jit progs/fact1.jitir\n";
    Arg.usage cmd_args "Options:"
  in

  Arg.parse cmd_args (fun s ->
    if !path <> "" then raise (Arg.Bad ("Invalid argument "^s));
    path := s) "Options:";
  if !path = "" then (
    usage ();
    exit 1);
  let p = (if (!enable_lua) then get_lua_program else get_program) !path in jit p
