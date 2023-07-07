Require Import utils.VSTALib.

Require Import cprogs.list.program.
Require Import cprogs.list.definitions.
Require Import cprogs.list.annotation.
Require cprogs.list.rev_append.ret_path1.

Module SH_Proof <: STRAIGHTLINE_HOARE_TRIPLE_PROOF.

Include cprogs.list.rev_append.ret_path1.

Theorem proof: functional_correctness_statement.
Proof.
  cbv delta [functional_correctness_statement].
  intros.
  forward_if; [| forward; apply TT_right ].
  subst p'.
  rewrite listrep_null.
  Intros.
  apply semax_return_return_split_assert.
  forward.
  Exists q'.
  simpl app.
  entailer!.
Qed.

End SH_Proof.
