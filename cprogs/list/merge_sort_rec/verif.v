Require Import utils.VSTALib.

Require Import cprogs.list.program.
Require Import cprogs.list.definitions.
Require Import cprogs.list.annotation.
Require cprogs.list.merge_sort_rec.ret_path0_verif.
Require cprogs.list.merge_sort_rec.ret_path1_verif.

Theorem f_merge_sort_rec_functionally_correct :
  semax_body Vprog Gprog f_merge_sort_rec merge_sort_rec_spec.
Proof.
  VST_A_start_function f_merge_sort_rec_hint.
  + apply ret_path0_verif.SH_Proof.proof.
  + apply ret_path1_verif.SH_Proof.proof.
Qed.
