Require Import utils.VSTALib.

Require Import cprogs.interpreter.program.
Require Import cprogs.interpreter.definitions.
Require Import cprogs.interpreter.annotation.
Require cprogs.interpreter.eval.ret_path0_verif.
Require cprogs.interpreter.eval.ret_path1_verif.
Require cprogs.interpreter.eval.ret_path2_verif.
Require cprogs.interpreter.eval.ret_path3_verif.
Require cprogs.interpreter.eval.ret_path4_verif.
Require cprogs.interpreter.eval.ret_path5_verif.
Require cprogs.interpreter.eval.ret_path6_verif.
Require cprogs.interpreter.eval.ret_path7_verif.
Require cprogs.interpreter.eval.ret_path8_verif.
Require cprogs.interpreter.eval.ret_path9_verif.
Require cprogs.interpreter.eval.ret_path10_verif.
Require cprogs.interpreter.eval.ret_path11_verif.
Require cprogs.interpreter.eval.ret_path12_verif.
Require cprogs.interpreter.eval.ret_path13_verif.
Require cprogs.interpreter.eval.ret_path14_verif.
Require cprogs.interpreter.eval.ret_path15_verif.
Require cprogs.interpreter.eval.ret_path16_verif.
Require cprogs.interpreter.eval.ret_path17_verif.
Require cprogs.interpreter.eval.ret_path18_verif.
Require cprogs.interpreter.eval.ret_path19_verif.
Require cprogs.interpreter.eval.ret_path20_verif.

Ltac simplify_SH :=
  rewrite semax_remove_skip; simpl remove_skip.

Theorem f_eval_functionally_correct :
  semax_body Vprog Gprog f_eval eval_spec.
Proof.
  VST_A_start_function f_eval_hint; simplify_SH.
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
  - apply ret_path11_verif.SH_Proof.proof.
  - apply ret_path12_verif.SH_Proof.proof.
  - apply ret_path13_verif.SH_Proof.proof.
  - apply ret_path14_verif.SH_Proof.proof.
  - apply ret_path15_verif.SH_Proof.proof.
  - apply ret_path16_verif.SH_Proof.proof.
  - apply ret_path17_verif.SH_Proof.proof.
  - apply ret_path18_verif.SH_Proof.proof.
  - apply ret_path19_verif.SH_Proof.proof.
  - apply ret_path20_verif.SH_Proof.proof.
Qed.