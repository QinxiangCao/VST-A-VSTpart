Require Import utils.VSTALib.

Require Import cprogs.add.program.
Require Import cprogs.add.definitions.
Require Import cprogs.add.annotation.
Require cprogs.add.slow_add.path0_verif.
Require cprogs.add.slow_add.path1_verif.
Require cprogs.add.slow_add.ret_path0_verif.

Theorem f_slow_add_functionally_correct :
  semax_body Vprog Gprog f_slow_add slow_add_spec.
Proof.
  VST_A_start_function f_slow_add_hint.
  + apply path0_verif.SH_Proof.proof.
  + apply path1_verif.SH_Proof.proof.
  + apply ret_path0_verif.SH_Proof.proof.
Qed.
