Require Import utils.VSTALib.

Require Import cprogs.bst.program.
Require Import cprogs.bst.definitions.
Require Import cprogs.bst.annotation.
Require cprogs.bst.pushdown_left.path0.

Module SH_Proof <: STRAIGHTLINE_HOARE_TRIPLE_PROOF.

Include cprogs.bst.pushdown_left.path0.

Theorem proof: functional_correctness_statement.
Proof.
  cbv delta [functional_correctness_statement].
  intros.
  Intros. forward. subst b_old.
  Exists ta tb n v b'.
  unfold treebox_rep at 3.
  unfold treebox_rep at 1. Intros pa.
  unfold treebox_rep at 1. Intros pb.
  Exists t.
  gather_SEP 1 2 3 5.
  replace_SEP 0 (store_tree_cell t n v pa pb).
  { entailer!. unfold_data_at (store_tree_cell t n v pa pb).
    entailer!. }
  entailer!. sep_apply store_tree_rep; auto.
  cancel. apply wand_refl_cancel_right.
Qed.

End SH_Proof.