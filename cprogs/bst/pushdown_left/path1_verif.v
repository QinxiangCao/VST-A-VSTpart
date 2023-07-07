Require Import utils.VSTALib.

Require Import cprogs.bst.program.
Require Import cprogs.bst.definitions.
Require Import cprogs.bst.annotation.
Require cprogs.bst.pushdown_left.path1.

Module SH_Proof <: STRAIGHTLINE_HOARE_TRIPLE_PROOF.

Include cprogs.bst.pushdown_left.path1.

Theorem proof: functional_correctness_statement.
Proof.
  cbv delta [functional_correctness_statement].
  intros. Intros ta1 tb1 n1 v1 b.
  unfold treebox_rep at 1. Intros p.
  forward. unfold tree_rep at 1; fold tree_rep.
  Intros pa pb. forward. forward.
  sep_apply (tree_rep_is_not_null tb1 pb).
  Intros k v0 tl tr pl pr. subst tb1.
  forward. forward. forward. forward. forward.
  simpl offset_val. simpl pushdown_left.
  Exists ta1 tl n1 v1 (field_address (Tstruct _tree noattr) [StructField _left] pb).
  entailer!. sep_apply (store_tree_rep n1 v1 pa pl ta1 tl p); auto.
  sep_apply (bst_left_entail (T ta1 n1 v1 tl) (pushdown_left ta1 tl) tr k v0 p pr pb b).
  cancel. apply wand_frame_ver.
Qed.

End SH_Proof.