Require Import utils.VSTALib.

Require Import cprogs.interpreter.program.
Require Import cprogs.interpreter.definitions.
Require Import cprogs.interpreter.annotation.
Require cprogs.interpreter.step.ret_path0_verif.
Require cprogs.interpreter.step.ret_path1_verif.
Require cprogs.interpreter.step.ret_path2_verif.
Require cprogs.interpreter.step.ret_path3_verif.
Require cprogs.interpreter.step.ret_path4_verif.
Require cprogs.interpreter.step.ret_path5_verif.
Require cprogs.interpreter.step.ret_path6_verif.
Require cprogs.interpreter.step.ret_path7_verif.
Require cprogs.interpreter.step.ret_path8_verif.
Require cprogs.interpreter.step.ret_path9_verif.
Require cprogs.interpreter.step.ret_path10_verif.

Ltac simplify_SH :=
  rewrite semax_remove_skip; simpl remove_skip.

Theorem f_step_functionally_correct :
  semax_body Vprog Gprog f_step step_spec.
Proof.
  VST_A_start_function f_step_hint; simplify_SH.
  - apply ret_path0_verif.SH_Proof.proof.
  - apply ret_path1_verif.SH_Proof.proof.
  - apply ret_path2_verif.SH_Proof.proof.
  - apply ret_path3_verif.SH_Proof.proof.
  - apply ret_path4_verif.SH_Proof.proof.
  - apply ret_path5_verif.SH_Proof.proof.
  - apply ret_path6_verif.SH_Proof.proof.
  - apply ret_path7_verif.SH_Proof.proof.
  - apply ret_path8_verif.SH_Proof.proof.
  - apply ret_path9_verif.SH_Proof.proof.
  - apply ret_path10_verif.SH_Proof.proof.
Qed.