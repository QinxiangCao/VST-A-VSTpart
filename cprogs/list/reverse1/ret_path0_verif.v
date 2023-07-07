Require Import utils.VSTALib.

Require Import cprogs.list.program.
Require Import cprogs.list.definitions.
Require Import cprogs.list.annotation.
Require cprogs.list.reverse1.ret_path0.

Module SH_Proof <: STRAIGHTLINE_HOARE_TRIPLE_PROOF.

Include cprogs.list.reverse1.ret_path0.

Theorem proof: functional_correctness_statement.
Proof.
  cbv delta [functional_correctness_statement].
  intros.
  Intros l1 l2 w v.
  forward_if; [forward; apply TT_right |].
  unfold POSTCONDITION, abbreviate.
  apply semax_return_return_split_assert.
  forward.
  Exists w; entailer!.
  sep_apply (listrep_null l2).
  entailer!.
  rewrite app_nil_r, rev_involutive.
  entailer!.
Qed.

End SH_Proof.
