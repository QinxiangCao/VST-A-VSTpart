Require Import utils.VSTALib.

Require Import cprogs.bst.program.
Require Import cprogs.bst.definitions.
Require Import cprogs.bst.annotation.
Require cprogs.bst.insert.ret_path0.

Module SH_Proof <: STRAIGHTLINE_HOARE_TRIPLE_PROOF.

Include cprogs.bst.insert.ret_path0.

Theorem proof: functional_correctness_statement.
Proof.
  cbv delta [functional_correctness_statement].
  intros.
  Intros t1 value x b. subst x.
  unfold treebox_rep at 3. Intros p.
  forward. forward. subst p.
  forward_call tt.
  cancel.
  Intros alloc_p.
  forward. forward. forward.
  forward. forward. forward.
  forward. simpl. entailer!.
  change (Vint (Int.repr 0)) with nullval.
  sep_apply treebox_rep_leaf. auto.
  apply wand_frame_elim.
Qed.

End SH_Proof.
