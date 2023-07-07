Require Import utils.VSTALib.

Require Import cprogs.dlist.program.
Require Import cprogs.dlist.definitions.
Require Import cprogs.dlist.annotation.
Require cprogs.dlist.enqueue.path1.

Module SH_Proof <: STRAIGHTLINE_HOARE_TRIPLE_PROOF.

Include cprogs.dlist.enqueue.path1.

Theorem proof: functional_correctness_statement.
Proof.
  cbv delta [functional_correctness_statement singleton].
  intros.
  forward_call tt.
  { entailer!. }
  Intros r2.
  subst x' l'.
  simpl fst; simpl snd.
  unfold lbrep.
  Intros p q.
  forward. forward. forward. forward.
  sep_apply (lseg_pre_neq_tail).
  Intros b s1a u.
  forward. forward. forward. forward. forward. forward.
  entailer!.
  unfold lbrep; unfold lseg_pre; fold lseg_pre.
  Exists p r2.
  sep_apply lseg_pre_store.
  sep_apply lseg_pre_store.
  change (Vint (IntRepr 0)) with nullval.
  entailer!.
Qed.

End SH_Proof.
