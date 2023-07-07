Require Import utils.VSTALib.

Require Import cprogs.swap.program.
Require Import cprogs.swap.definitions.
Require Import cprogs.swap.annotation.
Require cprogs.swap.int_swap_arith.path0_verif.

Theorem f_int_swap_arith_functionally_correct :
  semax_body Vprog Gprog f_int_swap_arith int_swap_arith_spec.
Proof.
  VST_A_start_function f_int_swap_arith_hint.
  apply path0_verif.SH_Proof.proof.
Qed.
