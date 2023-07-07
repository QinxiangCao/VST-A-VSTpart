Require Import utils.VSTALib.

Require Import cprogs.list.program.
Require Import cprogs.list.definitions.
Require Import cprogs.list.annotation.
Require cprogs.list.reverse2.path1.

Module SH_Proof <: STRAIGHTLINE_HOARE_TRIPLE_PROOF.

Include cprogs.list.reverse2.path1.
  
Theorem proof: functional_correctness_statement.
Proof.
  cbv delta [functional_correctness_statement].
  intros.
  Intros l1 a l2b u w v.
  forward. forward.
  forward. forward.
  forward. forward.
  sep_apply (listrep_isptr l2b u).
  Intros b l2c r.
  entailer!.
  Exists (a :: l1) b l2c r v u.
  entailer!.
  - simpl.
    rewrite <- app_assoc.
    reflexivity.
  - unfold listrep at 2; fold listrep.
    Exists w.
    entailer!.
Qed.

End SH_Proof.
