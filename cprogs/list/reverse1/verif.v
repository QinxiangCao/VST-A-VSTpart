Require Import utils.VSTALib.

Require Import cprogs.list.program.
Require Import cprogs.list.definitions.
Require Import cprogs.list.annotation.
Require cprogs.list.reverse1.path0_verif.
Require cprogs.list.reverse1.path1_verif.
Require cprogs.list.reverse1.path2_verif.
Require cprogs.list.reverse1.ret_path0_verif.

Theorem f_reverse_functionally_correct :
  semax_body Vprog Gprog f_reverse1 reverse1_spec.
Proof.
  VST_A_start_function f_reverse1_hint.
  - apply path0_verif.SH_Proof.proof.
  - apply path1_verif.SH_Proof.proof.
  - apply path2_verif.SH_Proof.proof.
  - apply ret_path0_verif.SH_Proof.proof.
Qed.
