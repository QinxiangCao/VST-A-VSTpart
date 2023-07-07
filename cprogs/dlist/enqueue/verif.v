Require Import utils.VSTALib.

Require Import cprogs.dlist.program.
Require Import cprogs.dlist.definitions.
Require Import cprogs.dlist.annotation.
Require cprogs.dlist.enqueue.path0_verif.
Require cprogs.dlist.enqueue.path1_verif.

Theorem f_enqueue_functionally_correct :
  semax_body Vprog Gprog f_enqueue enqueue_spec.
Proof.
  VST_A_start_function f_enqueue_hint.
  - apply path0_verif.SH_Proof.proof.
  - apply path1_verif.SH_Proof.proof.
Qed.
