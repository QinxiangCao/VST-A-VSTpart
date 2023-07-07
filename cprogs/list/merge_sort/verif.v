Require Import utils.VSTALib.

Require Import cprogs.list.program.
Require Import cprogs.list.definitions.
Require Import cprogs.list.annotation.
Require cprogs.list.merge_sort.ret_path0_verif.

Theorem f_merge_sort_functionally_correct :
  semax_body Vprog Gprog f_merge_sort merge_sort_spec.
Proof.
  VST_A_start_function f_merge_sort_hint.
  + apply ret_path0_verif.SH_Proof.proof.
Qed.
