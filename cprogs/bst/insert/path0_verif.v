Require Import utils.VSTALib.

Require Import cprogs.bst.program.
Require Import cprogs.bst.definitions.
Require Import cprogs.bst.annotation.
Require cprogs.bst.insert.path0.

Module SH_Proof <: STRAIGHTLINE_HOARE_TRIPLE_PROOF.

Include cprogs.bst.insert.path0.

Theorem proof: functional_correctness_statement.
Proof.
  cbv delta [functional_correctness_statement].
  intros. Intros. subst b_old. subst value'.
  forward.
  Exists t v x' b'. entailer!.
  apply wand_refl_cancel_right.
Qed.

End SH_Proof.