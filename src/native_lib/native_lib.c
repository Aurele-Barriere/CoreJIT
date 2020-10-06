#include <caml/callback.h>
#include <caml/fail.h>
#include <caml/bigarray.h>
#include <caml/memory.h>
#include <stdio.h>

extern void c_fail_prim(const char* msg) {
  printf("\033[;33mRun-Time Error:\033[;0m %s\n", msg);
  exit(0);
}
extern void c_print_prim(int64_t i) {
  printf("\033[;32mOUTPUT:\033[;0m %ld\n", i);
}
extern void c_print_string_prim(const char* msg) {
  printf("\033[;32mOUTPUT:\033[;0m %s\n", msg);
}

extern void c_deopt_prim(int32_t id, int32_t n, int64_t* args) {
  static const value * closure_f = NULL;
  if (closure_f == NULL) {
    closure_f = caml_named_value("ocaml_deopt_prim");
    if (!closure_f) {
      caml_failwith("deopt callback not registered");
    }
  }
  intnat len[1] = {n};
  caml_callback2(*closure_f,
      Val_int(id),
      caml_ba_alloc(CAML_BA_INT64|CAML_BA_C_LAYOUT, 1, args, len));
}

extern void c_call_prim(int32_t id, int32_t nargs, int32_t n, int64_t* args) {
  static const value * closure_f = NULL;
  if (closure_f == NULL) {
    closure_f = caml_named_value("ocaml_call_prim");
    if (!closure_f) {
      caml_failwith("call callback not registered");
    }
  }
  intnat len[1] = {n};
  caml_callback3(*closure_f,
      Val_int(id),
      Val_int(nargs),
      caml_ba_alloc(CAML_BA_INT64|CAML_BA_C_LAYOUT, 1, args, len));
}
