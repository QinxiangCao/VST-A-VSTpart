Require Import utils.VSTALib.

Require Import cprogs.abs.program.
Require Import cprogs.abs.definitions.
Require Import cprogs.abs.annotation.
Require cprogs.abs.abs.ret_path0_verif.
Require cprogs.abs.abs.ret_path1_verif.

Theorem f_abs_functionally_correct :
  semax_body Vprog Gprog f_abs abs_spec.
Proof.
  VST_A_start_function f_abs_hint.
  + apply ret_path0_verif.SH_Proof.proof.
  + apply ret_path1_verif.SH_Proof.proof.
Qed.
