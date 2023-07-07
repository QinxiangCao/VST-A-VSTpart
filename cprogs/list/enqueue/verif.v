Require Import utils.VSTALib.

Require Import cprogs.list.program.
Require Import cprogs.list.definitions.
Require Import cprogs.list.annotation.
Require cprogs.list.push.path0_verif.

Theorem f_push_functionally_correct:
  semax_body Vprog Gprog f_push push_spec.
Proof.
  VST_A_start_function f_push_hint.
  apply path0_verif.SH_Proof.proof.
Qed.
