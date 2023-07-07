Require Import utils.VSTALib.

Require Import cprogs.list.program.
Require Import cprogs.list.definitions.
Require Import cprogs.list.annotation.
Require cprogs.list.append2.ret_path2.

Module SH_Proof <: STRAIGHTLINE_HOARE_TRIPLE_PROOF.

Include cprogs.list.append2.ret_path2.
  
Theorem proof: functional_correctness_statement.
Proof.
  cbv delta [functional_correctness_statement].
  intros.
  forward.
  sep_apply listrep_is_not_null.
  Intros a s1b z.
  forward. forward. forward. forward.
  Exists x'.
  sep_apply listrep_null.
  Intros.
  subst s1b.
  simpl app.
  sep_apply store_listrep.
  entailer!.
Qed.

End SH_Proof.
