Require Import utils.VSTALib.

Require Import cprogs.list.program.
Require Import cprogs.list.definitions.
Require Import cprogs.list.annotation.
Require cprogs.list.rev_append.ret_path0.

Module SH_Proof <: STRAIGHTLINE_HOARE_TRIPLE_PROOF.

Include cprogs.list.rev_append.ret_path0.

Theorem proof: functional_correctness_statement.
Proof.
  cbv delta [functional_correctness_statement].
  intros.
  Intros a l1b l1c p w v q.
  forward.
  subst v.
  sep_apply listrep_null.
  Intros.
  forward.
  forward.
  Exists w.
  entailer!.
  rewrite app_nil_r.
  sep_apply store_listrep.
  sep_apply lseg_listrep.
  simpl rev.
  rewrite rev_involutive, <- app_assoc.
  apply derives_refl.
Qed.

End SH_Proof.
