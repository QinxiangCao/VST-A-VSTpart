Require Import utils.VSTALib.

Require Import cprogs.dlist.program.
Require Import cprogs.dlist.definitions.
Require Import cprogs.dlist.annotation.
Require cprogs.dlist.reverse.path0_verif.
Require cprogs.dlist.reverse.path1_verif.
Require cprogs.dlist.reverse.ret_path0_verif.

Ltac simplify_SH :=
  rewrite semax_remove_skip; simpl remove_skip.

Theorem f_reverse_functionally_correct :
  semax_body Vprog Gprog f_reverse reverse_spec.
Proof.
  VST_A_start_function f_reverse_hint; simplify_SH.
  - apply path0_verif.SH_Proof.proof.
  - apply path1_verif.SH_Proof.proof.
  - apply ret_path0_verif.SH_Proof.proof.
Qed.