Require Import utils.VSTALib.

Require Import cprogs.list.program.
Require Import cprogs.list.definitions.
Require Import cprogs.list.annotation.
Require cprogs.list.append_2p.ret_path0.

Module SH_Proof <: STRAIGHTLINE_HOARE_TRIPLE_PROOF.

Include cprogs.list.append_2p.ret_path0.
  
Theorem proof: functional_correctness_statement.
Proof.
  cbv delta [functional_correctness_statement].
  intros.
  Intros s1a s1b u t y px.
  subst s1.
  forward.
  forward.
  subst u.
  sep_apply listrep_null.
  Intros.
  subst s1b.
  forward.
  sep_apply lbseg_listrep.
  Intros x.
  forward.
  forward_call px.
  forward.
  Exists x.
  rewrite app_nil_r.
  entailer!.
Qed.

End SH_Proof.
