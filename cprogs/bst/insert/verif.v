Require Import utils.VSTALib.

Require Import cprogs.bst.program.
Require Import cprogs.bst.definitions.
Require Import cprogs.bst.annotation.
Require cprogs.bst.insert.path0_verif.
Require cprogs.bst.insert.path1_verif.
Require cprogs.bst.insert.path2_verif.
Require cprogs.bst.insert.ret_path0_verif.
Require cprogs.bst.insert.ret_path1_verif.

Ltac simplify_SH :=
  rewrite semax_remove_skip; simpl remove_skip.

Theorem f_insert_functionally_correct :
  semax_body Vprog Gprog f_insert insert_spec.
Proof.
  VST_A_start_function f_insert_hint; simplify_SH.
  - apply path0_verif.SH_Proof.proof.
  - apply path1_verif.SH_Proof.proof.
  - apply path2_verif.SH_Proof.proof.
  - apply ret_path0_verif.SH_Proof.proof.
  - apply ret_path1_verif.SH_Proof.proof.
Qed.