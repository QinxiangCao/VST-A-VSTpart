Require Import utils.VSTALib.

Require Import cprogs.list.program.
Require Import cprogs.list.definitions.
Require Import cprogs.list.annotation.
Require cprogs.list.rev_append.path1.

Module SH_Proof <: STRAIGHTLINE_HOARE_TRIPLE_PROOF.

Include cprogs.list.rev_append.path1.

Theorem proof: functional_correctness_statement.
Proof.
  cbv delta [functional_correctness_statement].
  intros.
  Intros a l1b l1c p w v q.
  forward.
  sep_apply (listrep_isptr l1c v).
  Intros c l1d v'.
  forward.
  forward.
  forward.
  forward.
  Exists a (c :: l1b) l1d p v v' q.
  sep_apply store_lseg.
  entailer!.
  simpl app.
  rewrite <- app_assoc.
  simpl app.
  reflexivity.
Qed.

End SH_Proof.
