Require Import utils.VSTALib.

Require Import cprogs.list.program.
Require Import cprogs.list.definitions.
Require Import cprogs.list.annotation.
Require cprogs.list.merge_sort_rec.ret_path1.

Module SH_Proof <: STRAIGHTLINE_HOARE_TRIPLE_PROOF.

Include cprogs.list.merge_sort_rec.ret_path1.

Theorem proof: functional_correctness_statement.
Proof.
  cbv delta [functional_correctness_statement].
  intros.
  Intros.
  subst q' p' x'.
  forward. forward.
  forward_call (x0, nullval, ptr_q, ptr_p, nullval, @nil Z, @nil Z, l, ptr_p, x0, ptr_q).
  { unfold listrep; entailer!. }
  { simpl. tauto. }
  Intros ret.
  destruct ret as [ [ [s1 s2] p0] q0].
  simpl in H0; simpl fst; simpl snd.
  forward. forward. forward.
  sep_apply (listrep_is_not_null_no_expand s2).
  Intros s2a s2b. rename H2 into s2_not_nil. clear H1.
  pose proof split_rel_all_nonneg _ _ _ H0.
  forward_call (p0, ptr_q, ptr_p, s1, ptr_p, p0, ptr_q).
  { tauto. }
  Intros ret.
  destruct ret as [s1' p1].
  simpl in H2.
  simpl fst; simpl snd.
  forward.
  forward_call (q0, ptr_q, ptr_p, s2, ptr_p, q0, ptr_q).
  { tauto. }
  Intros ret.
  destruct ret as [s2' p2].
  simpl in H3.
  simpl fst; simpl snd.
  forward.
  pose proof merge_sort_all_nonneg _ _ H2.
  pose proof merge_sort_all_nonneg _ _ H3.
  forward_call (s2', s1', p1, p2).
  { tauto. }
  Intros ret.
  destruct ret as [s r].
  simpl fst; simpl snd; simpl in H6.
  forward.
  Exists s r.
  entailer!.
  pose proof merge_sort_rec _ _ _ s1' s2' s H0.
  apply H9; auto.
  congruence.
Qed.

End SH_Proof.
