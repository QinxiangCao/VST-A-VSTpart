Require Import utils.VSTALib.

Require Import cprogs.bst.program.
Require Import cprogs.bst.definitions.
Require Import cprogs.bst.annotation.
Require cprogs.bst.insert.path1.

Module SH_Proof <: STRAIGHTLINE_HOARE_TRIPLE_PROOF.

Include cprogs.bst.insert.path1.

Theorem proof: functional_correctness_statement.
Proof.
  cbv delta [functional_correctness_statement].
  intros.
  Intros t1 value x b.
  unfold treebox_rep at 3. Intros p.
  forward. forward.
  sep_apply tree_rep_is_not_null.
  Intros k v0 tl tr pl pr.
  forward. forward. forward.
  Exists tl v x (field_address (Tstruct _tree noattr) [StructField _left] p).
  entailer!.
  simpl treebox_rep.
  simpl_if.
  sep_apply (bst_left_entail tl (insert n v tl) tr k v0 pl pr p b).
  cancel. apply wand_frame_ver.
Qed.

End SH_Proof.