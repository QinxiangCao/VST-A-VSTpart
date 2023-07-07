Require Import utils.VSTALib.

Require Import cprogs.list.program.
Require Import cprogs.list.definitions.
Require Import cprogs.list.annotation.
Require cprogs.list.split_rec.path0_verif.
Require cprogs.list.split_rec.ret_path0_verif.

Theorem f_split_rec_functionally_correct :
  semax_body Vprog Gprog f_split_rec split_rec_spec.
Proof.
  VST_A_start_function f_split_rec_hint.
  + apply path0_verif.SH_Proof.proof.
  + apply ret_path0_verif.SH_Proof.proof.
Qed.
