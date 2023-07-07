Require Import utils.VSTALib.

Require Import cprogs.list.program.
Require Import cprogs.list.definitions.
Require Import cprogs.list.annotation.
Require cprogs.list.merge_sort_rec.ret_path0.

Module SH_Proof <: STRAIGHTLINE_HOARE_TRIPLE_PROOF.

Include cprogs.list.merge_sort_rec.ret_path0.

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
  sep_apply (listrep_is_null s2).
  Intros.
  subst q0 s2.
  forward.
  Exists s1 p0.
  entailer!.
  apply merge_sort_base.
  tauto.
Qed.

End SH_Proof.
