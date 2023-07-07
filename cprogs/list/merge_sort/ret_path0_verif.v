Require Import utils.VSTALib.

Require Import cprogs.list.program.
Require Import cprogs.list.definitions.
Require Import cprogs.list.annotation.
Require cprogs.list.merge_sort.ret_path0.

Module SH_Proof <: STRAIGHTLINE_HOARE_TRIPLE_PROOF.

Include cprogs.list.merge_sort.ret_path0.

Theorem proof: functional_correctness_statement.
Proof.
  cbv delta [functional_correctness_statement].
  intros.
  Intros.
  subst x'.
  forward_call tt.
  { entailer!. }
  Intros ret.
  destruct ret as [p0 ptr_p].
  forward.
  forward_call tt.
  { entailer!. }
  Intros ret.
  destruct ret as [q0 ptr_q].
  forward.
  simpl fst; simpl snd.
  forward_call (x0, ptr_q, ptr_p, l, ptr_p, x0, ptr_q).
  Intros ret.
  destruct ret as [l0 x0'].
  simpl in H0.
  simpl fst; simpl snd.
  forward.
  forward_call ptr_p.
  forward_call ptr_q.
  forward.
  Exists l0 x0'.
  entailer!.
  split.
  + pose proof merge_sort_increasing _ _ H0.
    tauto.
  + pose proof merge_sort_perm _ _ H0.
    tauto.
Qed.

End SH_Proof.
