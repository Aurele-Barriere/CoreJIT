(* The values of our language *)

Require Export Coqlib.

(* Values stored inside registers and inside the memory *)
Inductive value : Type :=
| Vint : Z -> value.
