Require Import utils.VSTALib.

Require Import cprogs.list.program.
Require Import cprogs.list.definitions.
Require Import cprogs.list.annotation.
Require cprogs.list.append2.ret_path0.

Module SH_Proof <: STRAIGHTLINE_HOARE_TRIPLE_PROOF.

Include cprogs.list.append2.ret_path0.
  
Theorem proof: functional_correctness_statement.
Proof.
  cbv delta [functional_correctness_statement].
  intros.
  Intros a s1b t x y u.
  forward.
  subst u.
  sep_apply listrep_null.
  forward.
  forward.
  Exists x.
  sep_apply store_listrep.
  entailer!.
  rewrite sepcon_comm, -> wand_sepcon_adjoint.
  simpl app.
  entailer!.
Qed.

End SH_Proof.
