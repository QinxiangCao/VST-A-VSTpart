Require Import utils.VSTALib.

Require Import cprogs.list.program.
Require Import cprogs.list.definitions.
Require Import cprogs.list.annotation.
Require cprogs.list.merge_alter_spec.ret_path1.

Module SH_Proof <: STRAIGHTLINE_HOARE_TRIPLE_PROOF.

Include cprogs.list.merge_alter_spec.ret_path1.

Theorem proof: functional_correctness_statement.
Proof.
  cbv delta [functional_correctness_statement].
  intros.
  Intros l1 l2 l3 u t x y pret.
  forward.
  forward.
  forward.
  sep_apply (listrep_is_null l2).
  Intros.
  subst y l2.
  sep_apply lbseg_listrep.
  Intros ret.
  forward.
  change val in ret.
  forward_call pret.
  forward.
  Exists (l3 ++ l1) ret.
  entailer!.
  pose proof merge_steps_increasing _ _ _ _ _ _ H.
  simpl in H5.
  pose proof merge_steps_perm _ _ _ _ _ _ H.
  simpl in H6.
  rewrite app_nil_r in H6.
  tauto.
Qed.

End SH_Proof.
