Require Import utils.VSTALib.

Require Import cprogs.list.program.
Require Import cprogs.list.definitions.
Require Import cprogs.list.annotation.
Require cprogs.list.push.path0.

Module SH_Proof <: STRAIGHTLINE_HOARE_TRIPLE_PROOF.

Include cprogs.list.push.path0.

Theorem proof: functional_correctness_statement.
Proof.
  cbv delta [functional_correctness_statement].
  intros.
  Intros.
  subst x' p'.
  forward_call tt.
  { entailer!. }
  Intros p1.
  simpl fst; simpl snd.
  forward.
  forward.
  forward.
  forward.
  forward.
  Exists p1.
  entailer!.
  unfold listrep; fold listrep.
  Exists q.
  entailer!.
Qed.

End SH_Proof.
