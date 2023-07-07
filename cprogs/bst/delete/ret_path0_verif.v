Require Import utils.VSTALib.

Require Import cprogs.bst.program.
Require Import cprogs.bst.definitions.
Require Import cprogs.bst.annotation.
Require cprogs.bst.delete.ret_path0.

Module SH_Proof <: STRAIGHTLINE_HOARE_TRIPLE_PROOF.

Include cprogs.bst.delete.ret_path0.

Theorem proof: functional_correctness_statement.
Proof.
  cbv delta [functional_correctness_statement].
  intros. Intros t1 x b.
  unfold treebox_rep at 1. Intros p.
  forward. forward.
  subst p.
  forward. simpl. sep_apply treebox_rep_E.
  entailer!. apply wand_frame_elim.
Qed.

End SH_Proof.