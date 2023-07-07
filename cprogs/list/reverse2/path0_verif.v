Require Import utils.VSTALib.

Require Import cprogs.list.program.
Require Import cprogs.list.definitions.
Require Import cprogs.list.annotation.
Require cprogs.list.reverse2.path0.

Module SH_Proof <: STRAIGHTLINE_HOARE_TRIPLE_PROOF.

Include cprogs.list.reverse2.path0.
  
Theorem proof: functional_correctness_statement.
Proof.
  cbv delta [functional_correctness_statement].
  intros.
  forward. forward.
  forward. forward.
  sep_apply (listrep_isptr l p').
  Intros a l' q.
  Exists (@nil Z) a l' q nullval p'.
  entailer!.
  unfold listrep.
  entailer!.
Qed.

End SH_Proof.
