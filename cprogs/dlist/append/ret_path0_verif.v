Require Import utils.VSTALib.

Require Import cprogs.dlist.program.
Require Import cprogs.dlist.definitions.
Require Import cprogs.dlist.annotation.
Require cprogs.dlist.append.ret_path0.

Module SH_Proof <: STRAIGHTLINE_HOARE_TRIPLE_PROOF.

Include cprogs.dlist.append.ret_path0.

Theorem proof: functional_correctness_statement.
Proof.
  cbv delta [functional_correctness_statement].
  intros.
  Intros z l3 l4 l5 a b t x y u.
  forward.
  subst u. sep_apply listrep_pre_null.
  forward.
  forward.
  sep_apply listrep_pre_is_not_null.
  Intros x0 l' q.
  forward.
  forward. Exists x.
  entailer!.
  sep_apply singleton_lseg_pre.
  sep_apply lseg_pre_listrep_pre_app.
  sep_apply singleton_lseg_pre.
  sep_apply (lseg_pre_lseg_pre l4 [a]).
  sep_apply lseg_pre_listrep_pre_app.
  unfold listrep. rewrite H0.
  simpl app.
  entailer!.
Qed.

End SH_Proof.
