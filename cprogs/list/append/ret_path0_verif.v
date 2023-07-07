Require Import utils.VSTALib.

Require Import cprogs.list.program.
Require Import cprogs.list.definitions.
Require Import cprogs.list.annotation.
Require cprogs.list.append.ret_path0.

Module SH_Proof <: STRAIGHTLINE_HOARE_TRIPLE_PROOF.

Include cprogs.list.append.ret_path0.
  
Theorem proof: functional_correctness_statement.
Proof.
  cbv delta [functional_correctness_statement].
  intros.
  Intros s1a b s1c t x y u.
  forward.
  subst u.
  sep_apply listrep_null.
  forward.
  forward.
  Exists x.
  sep_apply lseg_store.
  sep_apply lseg_listrep.
  entailer!.
Qed.

End SH_Proof.
