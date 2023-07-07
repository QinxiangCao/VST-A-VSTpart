Require Import utils.VSTALib.

Require Import cprogs.list.program.
Require Import cprogs.list.definitions.
Require Import cprogs.list.annotation.
Require cprogs.list.dequeue.ret_path0.

Module SH_Proof <: STRAIGHTLINE_HOARE_TRIPLE_PROOF.

Include cprogs.list.dequeue.ret_path0.

Theorem proof: functional_correctness_statement.
Proof.
  cbv delta [functional_correctness_statement].
  intros.
  unfold qrep.
  Intros l1 l2 q1 q2.
  subst l'.
  forward. forward.
  subst q1.
  sep_apply listrep_null.
  Intros.
  subst l1.
  simpl in H0.
  forward.
  forward_call (l2, q2).
  Intros q1'.
  forward.
  forward.
  rewrite H0.
  unfold_data_at (store_queue l0 q1' (Vint (IntRepr 0))).
  forward_call (x0, q1',
                field_address (Tstruct _queue noattr) [StructField _l1] l0,
                s, field_address (Tstruct _queue noattr) [StructField _l1] l0).
  { entailer!. f_equal. field_address_solver. }
  { entailer!. }
  Intros ret.
  destruct ret as [q1'' x0'].
  simpl fst; simpl snd.
  simpl in H.
  subst x0'.
  change val in q1''.
  forward.
  Exists (Vint (IntRepr x0)).
  Exists s (@nil Z) q1'' nullval.
  entailer!.
  + simpl.
    rewrite app_nil_r.
    reflexivity.
  + unfold_data_at (store_queue l0 q1'' nullval).
    unfold listrep.
    entailer!.
Qed.

End SH_Proof.

