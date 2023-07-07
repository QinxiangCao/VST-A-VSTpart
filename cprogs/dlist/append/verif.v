Require Import utils.VSTALib.

Require Import cprogs.dlist.program.
Require Import cprogs.dlist.definitions.
Require Import cprogs.dlist.annotation.
Require cprogs.dlist.append.path0_verif.
Require cprogs.dlist.append.path1_verif.
Require cprogs.dlist.append.path2_verif.
Require cprogs.dlist.append.ret_path0_verif.
Require cprogs.dlist.append.ret_path1_verif.
Require cprogs.dlist.append.ret_path2_verif.

Theorem f_append_functionally_correct :
  semax_body Vprog Gprog f_append append_spec.
Proof.
  VST_A_start_function f_append_hint.
  - apply path0_verif.SH_Proof.proof.
  - apply path1_verif.SH_Proof.proof.
  - apply path2_verif.SH_Proof.proof.
  - apply ret_path0_verif.SH_Proof.proof.
  - apply ret_path1_verif.SH_Proof.proof.
  - apply ret_path2_verif.SH_Proof.proof.
Qed.
