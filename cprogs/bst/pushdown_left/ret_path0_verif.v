Require Import utils.VSTALib.

Require Import cprogs.bst.program.
Require Import cprogs.bst.definitions.
Require Import cprogs.bst.annotation.
Require cprogs.bst.pushdown_left.ret_path0.

Module SH_Proof <: STRAIGHTLINE_HOARE_TRIPLE_PROOF.

Include cprogs.bst.pushdown_left.ret_path0.

Theorem proof: functional_correctness_statement.
Proof.
  cbv delta [functional_correctness_statement].
  intros. Intros ta1 tb1 n1 v1 b.
  unfold treebox_rep at 1. Intros p.
  forward. unfold tree_rep at 1; fold tree_rep.
  Intros pa pb. forward. forward.
  subst pb. forward. forward.
  forward_call p.
  forward. sep_apply treerep_treebox_rep.
  simpl. entailer!.
  apply wand_frame_elim.
Qed.

End SH_Proof.
