Require Import utils.VSTALib.

Require Import cprogs.dlist.program.
Require Import cprogs.dlist.definitions.
Require Import cprogs.dlist.annotation.
Require cprogs.dlist.enqueue.path0.

Module SH_Proof <: STRAIGHTLINE_HOARE_TRIPLE_PROOF.

Include cprogs.dlist.enqueue.path0.

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
  forward. forward. forward.
  forward. forward. forward.
  forward.
  subst p.
  sep_apply (lseg_pre_null).
  Intros.
  subst s.
  forward.
  entailer!.
  simpl app.
  unfold lbrep.
  Exists r2 r2.
  unfold lseg_pre; fold lseg_pre.
  Exists nullval.
  entailer!.
Qed.

End SH_Proof.
