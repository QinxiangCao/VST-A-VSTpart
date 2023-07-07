Require Import utils.VSTALib.

Require Import cprogs.bst.program.
Require Import cprogs.bst.definitions.
Require Import cprogs.bst.annotation.
Require cprogs.bst.insert.ret_path1.

Module SH_Proof <: STRAIGHTLINE_HOARE_TRIPLE_PROOF.

Include cprogs.bst.insert.ret_path1.

Theorem proof: functional_correctness_statement.
Proof.
  cbv delta [functional_correctness_statement].
  intros.
  Intros t1 value x b. subst x.
  unfold treebox_rep at 3. Intros p.
  forward. forward.
  sep_apply tree_rep_is_not_null.
  Intros k v0 tl tr pl pr.
  forward. forward. forward. forward.
  forward. assert (k = n) by lia. subst n.
  sep_apply store_tree_rep; auto.
  replace (insert k v (T tl k v0 tr)) with (T tl k v tr).
  sep_apply treerep_treebox_rep.
  apply wand_frame_elim.
  simpl. simpl_if.
  reflexivity.
Qed.

End SH_Proof.
