Require Import utils.VSTALib.

Require Import cprogs.list.program.
Require Import cprogs.list.definitions.
Require Import cprogs.list.annotation.
Require cprogs.list.reverse2.ret_path1.

Module SH_Proof <: STRAIGHTLINE_HOARE_TRIPLE_PROOF.

Include cprogs.list.reverse2.ret_path1.
  
Theorem proof: functional_correctness_statement.
Proof.
  cbv delta [functional_correctness_statement].
  intros.
  forward.
  forward.
  forward.
  subst p'.
  sep_apply (listrep_null l).
  Intros.
  forward.
  Exists nullval; entailer!.
  simpl rev.
  unfold listrep.
  entailer!.
Qed.

End SH_Proof.
