Require Import utils.VSTALib.

Require Import cprogs.bst.program.
Require Import cprogs.bst.definitions.
Require Import cprogs.bst.annotation.
Require cprogs.bst.pushdown_left.path0_verif.
Require cprogs.bst.pushdown_left.path1_verif.
Require cprogs.bst.pushdown_left.ret_path0_verif.

Ltac simplify_SH :=
  rewrite semax_remove_skip; simpl remove_skip.

Theorem f_pushdown_left_functionally_correct :
  semax_body Vprog Gprog f_pushdown_left pushdown_left_spec.
Proof.
  VST_A_start_function f_pushdown_left_hint; simplify_SH.
  - apply path0_verif.SH_Proof.proof.
  - apply path1_verif.SH_Proof.proof.
  - apply ret_path0_verif.SH_Proof.proof.
Qed.
