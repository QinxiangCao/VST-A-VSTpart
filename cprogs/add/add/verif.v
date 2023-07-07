Require Import utils.VSTALib.

Require Import cprogs.add.program.
Require Import cprogs.add.definitions.
Require Import cprogs.add.annotation.
Require cprogs.add.add.ret_path0_verif.

Theorem f_add_functionally_correct :
  semax_body Vprog Gprog f_add add_spec.
Proof.
  VST_A_start_function f_add_hint.
  apply ret_path0_verif.SH_Proof.proof.
Qed.
