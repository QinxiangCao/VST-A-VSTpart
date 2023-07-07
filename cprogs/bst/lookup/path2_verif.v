Require Import utils.VSTALib.

Require Import cprogs.bst.program.
Require Import cprogs.bst.definitions.
Require Import cprogs.bst.annotation.
Require cprogs.bst.lookup.path2.

Module SH_Proof <: STRAIGHTLINE_HOARE_TRIPLE_PROOF.

Include cprogs.bst.lookup.path2.

Theorem proof: functional_correctness_statement.
Proof.
  cbv delta [functional_correctness_statement].
  intros. Intros t1 x p.
  forward_if; [| forward; apply TT_right].
  sep_apply tree_rep_is_not_null.
  Intros k v tl tr pl pr.
  forward. forward. forward. forward.
  Exists tr x pr.
  entailer!.
  - rewrite <- H. simpl.
    simpl_if.
    auto.
  - rewrite <- wand_sepcon_adjoint.
    sep_apply store_tree_rep. auto.
    apply wand_frame_elim.
Qed.

End SH_Proof.