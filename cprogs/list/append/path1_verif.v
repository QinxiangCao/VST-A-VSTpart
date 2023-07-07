Require Import utils.VSTALib.

Require Import cprogs.list.program.
Require Import cprogs.list.definitions.
Require Import cprogs.list.annotation.
Require cprogs.list.append.path1.

Module SH_Proof <: STRAIGHTLINE_HOARE_TRIPLE_PROOF.

Include cprogs.list.append.path1.
  
Theorem proof: functional_correctness_statement.
Proof.
  cbv delta [functional_correctness_statement].
  intros.
  Intros s1a b s1c t x y u.
  subst s1.
  forward.
  forward.
  sep_apply listrep_is_not_null.
  Intros c s1d w.
  forward.
  Exists (s1a ++ b :: nil) c s1d u x y w.
  entailer!.
  + rewrite <- app_assoc.
    reflexivity.
  + sep_apply lseg_store.
    entailer!.
Qed.

End SH_Proof.
