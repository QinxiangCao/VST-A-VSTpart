Require Import utils.VSTALib.

Require Import cprogs.list.program.
Require Import cprogs.list.definitions.
Require Import cprogs.list.annotation.
Require cprogs.list.rev_append.path0_verif.
Require cprogs.list.rev_append.path1_verif.
Require cprogs.list.rev_append.ret_path0_verif.
Require cprogs.list.rev_append.ret_path1_verif.

Theorem f_rev_append_functionally_correct :
  semax_body Vprog Gprog f_rev_append rev_append_spec.
Proof.
  VST_A_start_function f_rev_append_hint.
  - apply path0_verif.SH_Proof.proof.
  - apply path1_verif.SH_Proof.proof.
  - apply ret_path0_verif.SH_Proof.proof.
  - apply ret_path1_verif.SH_Proof.proof.
Qed.
