Require Import utils.VSTALib.

Require Import cprogs.list.program.
Require Import cprogs.list.definitions.
Require Import cprogs.list.annotation.
Require cprogs.list.append2.path1.

Module SH_Proof <: STRAIGHTLINE_HOARE_TRIPLE_PROOF.

Include cprogs.list.append2.path1.
  
Theorem proof: functional_correctness_statement.
Proof.
  cbv delta [functional_correctness_statement].
  intros.
  Intros a s1b t x y u.
  forward.
  forward.
  sep_apply listrep_is_not_null.
  Intros b s1c w.
  forward.
  Exists b s1c u x y w.
  entailer!.
  rewrite <- wand_sepcon_adjoint.
  sep_apply store_listrep.
  rewrite sepcon_comm, -> wand_sepcon_adjoint.
  simpl app.
  entailer!.
Qed.

End SH_Proof.
