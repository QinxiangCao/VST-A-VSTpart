Require Import utils.VSTALib.

Require Import cprogs.bst.program.
Require Import cprogs.bst.definitions.
Require Import cprogs.bst.annotation.
Require cprogs.bst.delete.path1.

Module SH_Proof <: STRAIGHTLINE_HOARE_TRIPLE_PROOF.

Include cprogs.bst.delete.path1.

Theorem proof: functional_correctness_statement.
Proof.
  cbv delta [functional_correctness_statement].
  intros. Intros t1 x b.
  unfold treebox_rep at 1. Intros p.
  forward. forward.
  sep_apply tree_rep_is_not_null.
  Intros k v tl tr pl pr.
  subst t1. simpl delete.
  forward. forward.
  forward. simpl offset_val.
  Exists tl x (field_address (Tstruct _tree noattr) [StructField _left] p).
  entailer!. simpl_if.
  sep_apply (bst_left_entail tl (delete n tl) tr k v pl pr p b).
  cancel. apply wand_frame_ver.
Qed.

End SH_Proof.