(* Profiler_types: the types used by the profiler functions *)

Require Export specIR.

(* The different kinds of Optimizations passes the profiler wishes to make *)
Inductive optim_wish : Type :=
| AS_INS: list expr -> label -> optim_wish
| AS_INS_DELAY: list expr -> label -> optim_wish
| CST_PROP: optim_wish
| INLINE: label -> optim_wish
| LOWER: optim_wish.
