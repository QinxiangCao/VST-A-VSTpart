Require Import utils.VSTALib.

Require Import cprogs.list.program.
Require Import cprogs.list.definitions.
Require Import cprogs.list.annotation.
Require cprogs.list.merge.path0_verif.
Require cprogs.list.merge.path1_verif.
Require cprogs.list.merge.path2_verif.
Require cprogs.list.merge.ret_path0_verif.
Require cprogs.list.merge.ret_path1_verif.

Theorem f_merge_functionally_correct :
  semax_body Vprog Gprog f_merge merge_spec.
Proof.
  VST_A_start_function f_merge_hint.
  + apply path0_verif.SH_Proof.proof.
  + apply path1_verif.SH_Proof.proof.
  + apply path2_verif.SH_Proof.proof.
  + apply ret_path0_verif.SH_Proof.proof.
  + apply ret_path1_verif.SH_Proof.proof.
Qed.

