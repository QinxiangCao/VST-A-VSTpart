Require Import utils.VSTALib.

Require Import cprogs.list.program.
Require Import cprogs.list.definitions.
Require Import cprogs.list.annotation.
Require cprogs.list.merge_alter_spec.path0_verif.
Require cprogs.list.merge_alter_spec.path1_verif.
Require cprogs.list.merge_alter_spec.path2_verif.
Require cprogs.list.merge_alter_spec.ret_path0_verif.
Require cprogs.list.merge_alter_spec.ret_path1_verif.

Theorem f_merge_alter_spec_functionally_correct :
  semax_body Vprog Gprog f_merge_alter_spec merge_alter_spec_spec.
Proof.
  VST_A_start_function f_merge_alter_spec_hint.
  + apply path0_verif.SH_Proof.proof.
  + apply path1_verif.SH_Proof.proof.
  + apply path2_verif.SH_Proof.proof.
  + apply ret_path0_verif.SH_Proof.proof.
  + apply ret_path1_verif.SH_Proof.proof.
Qed.

