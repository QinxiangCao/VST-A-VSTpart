Require Import utils.VSTALib.

Require Import cprogs.list.program.
Require Import cprogs.list.definitions.
Require Import cprogs.list.annotation.
Require cprogs.list.append_2p.path0_verif.
Require cprogs.list.append_2p.path1_verif.
Require cprogs.list.append_2p.ret_path0_verif.

Theorem f_append_2p_functionally_correct :
  semax_body Vprog Gprog f_append_2p append_2p_spec.
Proof.
  VST_A_start_function f_append_2p_hint.
  - apply path0_verif.SH_Proof.proof.
  - apply path1_verif.SH_Proof.proof.
  - apply ret_path0_verif.SH_Proof.proof.
Qed.
