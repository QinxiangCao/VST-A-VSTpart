Require Import utils.VSTALib.

Require Import cprogs.swap.program.
Require Import cprogs.swap.definitions.
Require Import cprogs.swap.annotation.
Require cprogs.swap.int_swap.path0.

Module SH_Proof <: STRAIGHTLINE_HOARE_TRIPLE_PROOF.

Include cprogs.swap.int_swap.path0.

Theorem proof: functional_correctness_statement.
Proof.
  cbv delta [functional_correctness_statement].
  intros.
  Intros.
  subst px' py'.
  forward.
  forward.
  forward.
  forward.
  entailer!.
Qed.

End SH_Proof.

