Require Import utils.VSTALib.

Require Import cprogs.list.program.
Require Import cprogs.list.definitions.
Require Import cprogs.list.annotation.
Require cprogs.list.enqueue.path0.

Module SH_Proof <: STRAIGHTLINE_HOARE_TRIPLE_PROOF.

Include cprogs.list.enqueue.path0.

Theorem proof: functional_correctness_statement.
Proof.
  cbv delta [functional_correctness_statement singleton].
  intros.
  Intros.
  subst x' l'.
  unfold qrep at 1.
  Intros l1 l2 q1 q2.
  unfold_data_at (store_queue l0 q1 q2).
  forward_call (x0, q2,
                field_address (Tstruct _queue noattr) [StructField _l2] l0,
                l2,
                field_address (Tstruct _queue noattr) [StructField _l2] l0,
                Vint (IntRepr x0)).
  { entailer!. f_equal. field_address_solver. }
  { entailer!. }
  Intros q2'.
  change val in q2'.
  entailer!.
  unfold qrep.
  Exists l1 (x0 :: l2) q1 q2'.
  entailer!.
  + simpl.
    rewrite app_assoc.
    reflexivity.
  + unfold_data_at (store_queue l0 q1 q2').
    entailer!.
Qed.

End SH_Proof.
