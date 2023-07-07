Require Import utils.VSTALib.

Require Import cprogs.list.program.
Require Import cprogs.list.definitions.
Require Import cprogs.list.annotation.
Require cprogs.list.pop.ret_path0_verif.

Theorem f_pop_functionally_correct :
  semax_body Vprog Gprog f_pop pop_spec.
Proof.
  VST_A_start_function f_pop_hint.
  apply ret_path0_verif.SH_Proof.proof.
Qed.
