Require Import utils.VSTALib.

Require Import cprogs.swap.program.
Require Import cprogs.swap.definitions.
Require Import cprogs.swap.annotation.
Require cprogs.swap.int_pair_swap.path0_verif.

Theorem f_int_pair_swap_functionally_correct :
  semax_body Vprog Gprog f_int_pair_swap int_pair_swap_spec.
Proof.
  VST_A_start_function f_int_pair_swap_hint.
  apply path0_verif.SH_Proof.proof.
Qed.
