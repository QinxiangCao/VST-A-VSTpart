Require Import utils.VSTALib.

Require Import cprogs.list.program.
Require Import cprogs.list.definitions.
Require Import cprogs.list.annotation.
Require cprogs.list.max.path1.

Module SH_Proof <: STRAIGHTLINE_HOARE_TRIPLE_PROOF.

Include cprogs.list.max.path1.
  
Theorem proof: functional_correctness_statement.
Proof.
  cbv delta [functional_correctness_statement].
  intros.
  Intros l1 l2 r0 p r.
  subst r.
  forward.
  sep_apply (listrep_isptr l2 p).
  Intros a l2b q.
  subst l2.
  simpl in H4.
  destruct H4.
  forward. forward. forward. forward.
  Exists (l1 ++ a :: nil) l2b a q (Vint (IntRepr a)).
  entailer!.
  - rewrite H2.
    simpl.
    rewrite <- app_assoc.
    assert (Z.max r0 a = a) by lia.
    rewrite H3.
    tauto.
  - sep_apply lseg_store.
    entailer!.
Qed.

End SH_Proof.
