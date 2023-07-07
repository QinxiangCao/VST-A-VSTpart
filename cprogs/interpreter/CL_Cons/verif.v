Require Import utils.VSTALib.

Require Import cprogs.interpreter.program.
Require Import cprogs.interpreter.definitions.
Require Import cprogs.interpreter.annotation.
Require cprogs.interpreter.CL_Cons.ret_path0_verif.

Ltac simplify_SH :=
  rewrite semax_remove_skip; simpl remove_skip.

Theorem f_CL_Cons_functionally_correct :
  semax_body Vprog Gprog f_CL_Cons CL_Cons_spec.
Proof.
  VST_A_start_function f_CL_Cons_hint; simplify_SH.
  apply ret_path0_verif.SH_Proof.proof.
Qed.
