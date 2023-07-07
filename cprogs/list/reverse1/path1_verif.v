Require Import utils.VSTALib.

Require Import cprogs.list.program.
Require Import cprogs.list.definitions.
Require Import cprogs.list.annotation.
Require cprogs.list.reverse1.path1.

Module SH_Proof <: STRAIGHTLINE_HOARE_TRIPLE_PROOF.

Include cprogs.list.reverse1.path1.
  
Theorem proof: functional_correctness_statement.
Proof.
  cbv delta [functional_correctness_statement].
  intros.
  Intros l1 l2 w v.
  forward.
  forward.
  sep_apply (listrep_isptr l2 v).
  Intros a l2b t.
  Exists t l1 a l2b w v.
  entailer!.
Qed.

End SH_Proof.
