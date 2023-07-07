Require Import utils.VSTALib.

Require Import cprogs.list.program.
Require Import cprogs.list.definitions.
Require Import cprogs.list.annotation.
Require cprogs.list.split_rec.path0.

Module SH_Proof <: STRAIGHTLINE_HOARE_TRIPLE_PROOF.

Include cprogs.list.split_rec.path0.

Theorem proof: functional_correctness_statement.
Proof.
  cbv delta [functional_correctness_statement].
  intros.
  Intros.
  subst x' p' q'.
  forward.
  sep_apply listrep_is_not_null.
  Intros a l' x1.
  subst l.
  forward. forward. forward. forward.
  forward_call (x1, x0, ptr_p, ptr_q, q0, (a :: l1), l2, l', ptr_q, x1, ptr_p).
  { entailer!.
    unfold listrep at 2; fold listrep.
    Exists p0.
    entailer!.
  }
  { simpl in H1. simpl. tauto. }
  Intros ret.
  destruct ret as [ [ [s2 s1] q0'] p0'].
  simpl in H0.
  simpl fst; simpl snd.
  Exists s1 s2 p0' q0'.
  entailer!.
  constructor.
  auto.
Qed.

End SH_Proof.
