Require Import utils.VSTALib.

Require Import cprogs.dlist.program.
Require Import cprogs.dlist.definitions.
Require Import cprogs.dlist.annotation.
Require cprogs.dlist.reverse.path1.

Module SH_Proof <: STRAIGHTLINE_HOARE_TRIPLE_PROOF.

Include cprogs.dlist.reverse.path1.

Theorem proof: functional_correctness_statement.
Proof.
  cbv delta [functional_correctness_statement].
  intros.
  Intros l1 l2 w v.
  forward.
  sep_apply (listrep_pre_isptr l2 v).
  Intros a l2b t.
  forward. forward. forward. forward. forward.
  entailer!.
  Exists (a :: l1) l2b v t.
  entailer!.
  - simpl. rewrite <- app_assoc. reflexivity.
  - unfold listrep_pre; fold listrep_pre.
    Exists w. entailer!.
Qed.

End SH_Proof.
