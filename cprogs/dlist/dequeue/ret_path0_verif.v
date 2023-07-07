Require Import utils.VSTALib.

Require Import cprogs.dlist.program.
Require Import cprogs.dlist.definitions.
Require Import cprogs.dlist.annotation.
Require cprogs.dlist.dequeue.ret_path0.

Module SH_Proof <: STRAIGHTLINE_HOARE_TRIPLE_PROOF.

Include cprogs.dlist.dequeue.ret_path0.

Theorem proof: functional_correctness_statement.
Proof.
  cbv delta [functional_correctness_statement].
  intros.
  Intros.
  subst l'.
  unfold lbrep.
  Intros p q.
  unfold lseg_pre; fold lseg_pre.
  Intros u.
  forward. forward.
  forward. forward.
  forward_call p.
  forward. forward.
  subst u.
  sep_apply (lseg_pre_null).
  Intros.
  subst s.
  forward. forward.
  Exists (Vint (IntRepr x0)).
  Exists nullval nullval.
  entailer!.
  unfold lseg_pre. entailer!.
Qed.

End SH_Proof.
