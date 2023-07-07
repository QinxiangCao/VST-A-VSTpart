Require Import utils.VSTALib.

Require Import cprogs.interpreter.program.
Require Import cprogs.interpreter.definitions.
Require Import cprogs.interpreter.annotation.
Require cprogs.interpreter.free_cmd_rec.ret_path0_verif.
Require cprogs.interpreter.free_cmd_rec.ret_path1_verif.
Require cprogs.interpreter.free_cmd_rec.ret_path2_verif.
Require cprogs.interpreter.free_cmd_rec.ret_path3_verif.
Require cprogs.interpreter.free_cmd_rec.ret_path4_verif.
Require cprogs.interpreter.free_cmd_rec.ret_path5_verif.

Ltac simplify_SH :=
  rewrite semax_remove_skip; simpl remove_skip.

Theorem f_free_cmd_rec_functionally_correct :
  semax_body Vprog Gprog f_free_cmd_rec free_cmd_rec_spec.
Proof.
  VST_A_start_function f_free_cmd_rec_hint; simplify_SH.
  - apply ret_path0_verif.SH_Proof.proof.
  - apply ret_path1_verif.SH_Proof.proof.
  - apply ret_path2_verif.SH_Proof.proof.
  - apply ret_path3_verif.SH_Proof.proof.
  - apply ret_path4_verif.SH_Proof.proof.
  - apply ret_path5_verif.SH_Proof.proof.
Qed.