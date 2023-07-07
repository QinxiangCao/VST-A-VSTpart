Require Import utils.VSTALib.

Require Import cprogs.max3.program.
Require Import cprogs.max3.definitions.
Require Import cprogs.max3.annotation.
Require cprogs.max3.max3.ret_path0_verif.
Require cprogs.max3.max3.ret_path1_verif.
Require cprogs.max3.max3.ret_path2_verif.
Require cprogs.max3.max3.ret_path3_verif.

Theorem f_max3_functionally_correct :
  semax_body Vprog Gprog f_max3 max3_spec.
Proof.
  VST_A_start_function f_max3_hint.
  + apply ret_path0_verif.SH_Proof.proof.
  + apply ret_path1_verif.SH_Proof.proof.
  + apply ret_path2_verif.SH_Proof.proof.
  + apply ret_path3_verif.SH_Proof.proof.
Qed.
