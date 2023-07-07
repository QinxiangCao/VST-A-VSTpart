Require Import utils.VSTALib.

Require Import cprogs.dlist.program.
Require Import cprogs.dlist.definitions.
Require Import cprogs.dlist.annotation.
Require cprogs.dlist.reverse.ret_path0.

Module SH_Proof <: STRAIGHTLINE_HOARE_TRIPLE_PROOF.

Include cprogs.dlist.reverse.ret_path0.

Theorem proof: functional_correctness_statement.
Proof.
  cbv delta [functional_correctness_statement].
  intros.
  Intros l1 l2 w v.
  forward.
  forward.
  Exists w; entailer!.
  sep_apply (listrep_pre_null l2).
  entailer!.
  rewrite app_nil_r, rev_involutive.
  unfold listrep. entailer!.
Qed.

End SH_Proof.
