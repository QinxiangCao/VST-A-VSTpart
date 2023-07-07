Require Import utils.VSTALib.

Require Import cprogs.list.program.
Require Import cprogs.list.definitions.
Require Import cprogs.list.annotation.
Require cprogs.list.max.path0_verif.
Require cprogs.list.max.path1_verif.
Require cprogs.list.max.path2_verif.
Require cprogs.list.max.ret_path0_verif.

Theorem f_max_functionally_correct :
  semax_body Vprog Gprog f_max max_spec.
Proof.
  VST_A_start_function f_max_hint.
  - apply path0_verif.SH_Proof.proof.
  - apply path1_verif.SH_Proof.proof.
  - apply path2_verif.SH_Proof.proof.
  - apply ret_path0_verif.SH_Proof.proof.
Qed.
