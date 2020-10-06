open Llvm
open Llvm_target
open Llvm_scalar_opts
open Ctypes
open Ctypes_static
open Foreign
open Conv

let context = global_context ()
let the_module = create_module context "my cool jit"

let execution_engine () =
  assert (Llvm_executionengine.initialize ());
  Llvm_executionengine.create the_module

let double_type = double_type context
let void_type = void_type context
let void_ptr = pointer_type void_type
let int_type = i64_type context (* assuming int is 64 *)
let i32_type = i32_type context
let int_val_type = int_type
let char_type = i8_type context
let char_ptr = pointer_type char_type
let heap_ptr_type = int_type
let heap_backing_store = pointer_type int_val_type
let arg_buf_type = pointer_type int_val_type

let zero = const_int i32_type 0
let ltrue = const_int (i1_type context) 1
let lfalse = const_int (i1_type context) 0

let global_arg_buffer_content_ty = array_type int_type 256
let global_arg_buffer_ty = pointer_type global_arg_buffer_content_ty
let global_arg_buffer = define_global "global_arg_buffer" (const_null global_arg_buffer_content_ty) the_module

let declare fid =
  let args = [| heap_backing_store ; arg_buf_type |] in
  let ft = function_type void_type args in
  let name = "fun" ^ (string_of_int (int_of_positive fid)) in
  let rec fresh_name suff =
    match lookup_function (name^suff) the_module with
    | None -> suff
    | Some _ -> fresh_name (suff ^ "_")
  in
  let name = name ^ (fresh_name "") in
  let f = declare_function name ft the_module in
  let bb = append_block context "entry" f in
  let builder = builder context in
  position_at_end bb builder;
  (f, builder, name)

(* llvm optimization pipeline *)
let the_fpm = begin
  let the_fpm = PassManager.create_function the_module in
  add_aggressive_dce the_fpm;
  add_cfg_simplification the_fpm;
  add_dead_store_elimination the_fpm;
  add_scalarizer the_fpm;
  add_merged_load_store_motion the_fpm;
  add_gvn the_fpm;
  add_ind_var_simplification the_fpm;
  add_instruction_combination the_fpm;
  add_jump_threading the_fpm;
  add_licm the_fpm;
  add_loop_deletion the_fpm;
  add_loop_idiom the_fpm;
  add_loop_rotation the_fpm;
  add_loop_reroll the_fpm;
  add_loop_unroll the_fpm;
  add_loop_unswitch the_fpm;
  add_memcpy_opt the_fpm;
  add_partially_inline_lib_calls the_fpm;
  add_lower_switch the_fpm;
  add_memory_to_register_promotion the_fpm;
  add_early_cse the_fpm;
  add_reassociation the_fpm;
  add_sccp the_fpm;
  add_constant_propagation the_fpm;
  add_aggressive_dce the_fpm;
  add_cfg_simplification the_fpm;
  add_scalar_repl_aggregation the_fpm;
  add_scalar_repl_aggregation_ssa the_fpm;
  add_scalar_repl_aggregation_with_threshold 4 the_fpm;
  add_lib_call_simplification the_fpm;
  add_tail_call_elimination the_fpm;
  add_constant_propagation the_fpm;
  (*add_memory_to_register_demotion the_fpm;*)
  add_verifier the_fpm;
  add_correlated_value_propagation the_fpm;
  add_lower_expect_intrinsic the_fpm;
  add_type_based_alias_analysis the_fpm;
  add_scoped_no_alias_alias_analysis the_fpm;
  add_basic_alias_analysis the_fpm;
  ignore (PassManager.initialize the_fpm);
  the_fpm
end
