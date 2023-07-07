Require Import utils.VSTALib.

Require Import cprogs.list.program.
Require Import cprogs.list.definitions.
Require Import cprogs.list.annotation.
Require cprogs.list.reverse1.path2.

Module SH_Proof <: STRAIGHTLINE_HOARE_TRIPLE_PROOF.

Include cprogs.list.reverse1.path2.
  
Theorem proof: functional_correctness_statement.
Proof.
  cbv delta [functional_correctness_statement].
  intros.
  Intros u l1 x l2 w v.
  forward. forward. forward. forward.
  Exists (x :: l1) l2 v u.
  entailer!.
  - simpl.
    rewrite <- app_assoc.
    reflexivity.
  - unfold listrep at 2; fold listrep.
    Exists w.
    entailer!.
Qed.

End SH_Proof.
