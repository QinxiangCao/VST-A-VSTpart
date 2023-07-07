Require Import utils.VSTALib.

Require Import cprogs.list.program.
Require Import cprogs.list.definitions.
Require Import cprogs.list.annotation.
Require cprogs.list.reverse2.ret_path0.

Module SH_Proof <: STRAIGHTLINE_HOARE_TRIPLE_PROOF.

Include cprogs.list.reverse2.ret_path0.
  
Theorem proof: functional_correctness_statement.
Proof.
  cbv delta [functional_correctness_statement].
  intros.
  Intros l1 a l2b u w v.
  forward. forward.
  forward. forward.
  forward. forward.
  Exists v; entailer!.
  sep_apply (listrep_null l2b).
  entailer!.
  change (cons a nil) with (rev (cons a nil)).
  rewrite <- rev_app_distr, rev_involutive.
  simpl app.
  unfold listrep at 2; fold listrep.
  Exists w.
  entailer!.
Qed.

End SH_Proof.
