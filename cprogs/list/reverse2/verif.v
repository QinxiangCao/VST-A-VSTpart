Require Import utils.VSTALib.

Require Import cprogs.list.program.
Require Import cprogs.list.definitions.
Require Import cprogs.list.annotation.
Require cprogs.list.reverse2.path0_verif.
Require cprogs.list.reverse2.path1_verif.
Require cprogs.list.reverse2.ret_path0_verif.
Require cprogs.list.reverse2.ret_path1_verif.

Theorem f_reverse_functionally_correct :
  semax_body Vprog Gprog f_reverse2 reverse2_spec.
Proof.
  VST_A_start_function f_reverse2_hint.
  - apply path0_verif.SH_Proof.proof.
  - apply path1_verif.SH_Proof.proof.
  - apply ret_path0_verif.SH_Proof.proof.
  - apply ret_path1_verif.SH_Proof.proof.
Qed.
