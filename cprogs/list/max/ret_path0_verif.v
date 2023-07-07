Require Import utils.VSTALib.

Require Import cprogs.list.program.
Require Import cprogs.list.definitions.
Require Import cprogs.list.annotation.
Require cprogs.list.max.ret_path0.

Module SH_Proof <: STRAIGHTLINE_HOARE_TRIPLE_PROOF.

Include cprogs.list.max.ret_path0.

Theorem proof: functional_correctness_statement.
Proof.
  cbv delta [functional_correctness_statement].
  intros.
  Intros l1 l2 r0 p r.
  subst r.
  forward.
  subst p.
  sep_apply (listrep_null l2).
  Intros.
  forward.
  simpl in H2.
  Exists (Vint (IntRepr r0)).
  subst r0.
  rewrite app_nil_r.
  entailer!.
  sep_apply lseg_nullval_ending.
  entailer!.
Qed.

End SH_Proof.

