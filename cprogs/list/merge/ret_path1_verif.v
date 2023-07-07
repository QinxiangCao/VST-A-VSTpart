Require Import utils.VSTALib.

Require Import cprogs.list.program.
Require Import cprogs.list.definitions.
Require Import cprogs.list.annotation.
Require cprogs.list.merge.ret_path1.

Module SH_Proof <: STRAIGHTLINE_HOARE_TRIPLE_PROOF.

Include cprogs.list.merge.ret_path1.

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
  apply merge_l. tauto.
Qed.

End SH_Proof.
