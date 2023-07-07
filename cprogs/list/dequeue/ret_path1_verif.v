Require Import utils.VSTALib.

Require Import cprogs.list.program.
Require Import cprogs.list.definitions.
Require Import cprogs.list.annotation.
Require cprogs.list.dequeue.ret_path1.

Module SH_Proof <: STRAIGHTLINE_HOARE_TRIPLE_PROOF.

Include cprogs.list.dequeue.ret_path1.

Theorem proof: functional_correctness_statement.
Proof.
  cbv delta [functional_correctness_statement].
  intros.
  unfold qrep.
  Intros l1 l2 q1 q2.
  subst l'.
  forward. forward.
  sep_apply listrep_is_not_null_no_expand.
  Intros a l1b.
  subst l1.
  simpl in H0.
  injection H0 as ? ?.
  subst a.
  unfold_data_at (store_queue l0 q1 q2).
  forward_call (x0, q1,
                field_address (Tstruct _queue noattr) [StructField _l1] l0,
                l1b, field_address (Tstruct _queue noattr) [StructField _l1] l0).
  { entailer!. f_equal. field_address_solver. }
  { entailer!. }
  Intros ret.
  destruct ret as [q1' x0'].
  simpl fst; simpl snd.
  simpl in H0.
  subst x0'.
  change val in q1'.
  forward.
  Exists (Vint (IntRepr x0)).
  Exists l1b l2 q1' q2.
  entailer!.
  unfold_data_at (store_queue l0 q1' q2).
  entailer!.
Qed.

End SH_Proof.

