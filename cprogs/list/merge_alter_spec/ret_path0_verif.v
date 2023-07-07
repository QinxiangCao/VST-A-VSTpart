Require Import utils.VSTALib.

Require Import cprogs.list.program.
Require Import cprogs.list.definitions.
Require Import cprogs.list.annotation.
Require cprogs.list.merge_alter_spec.ret_path0.

Module SH_Proof <: STRAIGHTLINE_HOARE_TRIPLE_PROOF.

Include cprogs.list.merge_alter_spec.ret_path0.

Theorem proof: functional_correctness_statement.
Proof.
  cbv delta [functional_correctness_statement].
  intros.
  Intros l1 l2 l3 u t x y pret.
  forward.
  forward.
  sep_apply listrep_is_null.
  Intros.
  subst x l1.
  sep_apply lbseg_listrep.
  Intros ret.
  forward.
  change val in ret.
  forward_call pret.
  forward.
  Exists (l3 ++ l2) ret.
  entailer!.
  pose proof merge_steps_increasing _ _ _ _ _ _ H.
  simpl in H4.
  pose proof merge_steps_perm _ _ _ _ _ _ H.
  simpl in H5.
  tauto.
Qed.

End SH_Proof.
