Require Import utils.VSTALib.

Require Import cprogs.bst.program.
Require Import cprogs.bst.definitions.
Require Import cprogs.bst.annotation.
Require cprogs.bst.lookup.path0_verif.
Require cprogs.bst.lookup.path1_verif.
Require cprogs.bst.lookup.path2_verif.
Require cprogs.bst.lookup.ret_path0_verif.
Require cprogs.bst.lookup.ret_path1_verif.

Ltac simplify_SH :=
  rewrite semax_remove_skip; simpl remove_skip.

Theorem f_lookup_functionally_correct :
  semax_body Vprog Gprog f_lookup lookup_spec.
Proof.
  VST_A_start_function f_lookup_hint; simplify_SH.
  - apply path0_verif.SH_Proof.proof.
  - apply path1_verif.SH_Proof.proof.
  - apply path2_verif.SH_Proof.proof.
  - apply ret_path0_verif.SH_Proof.proof.
  - apply ret_path1_verif.SH_Proof.proof.
Qed.
