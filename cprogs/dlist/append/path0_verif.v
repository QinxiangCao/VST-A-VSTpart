Require Import utils.VSTALib.

Require Import cprogs.dlist.program.
Require Import cprogs.dlist.definitions.
Require Import cprogs.dlist.annotation.
Require cprogs.dlist.append.path0.

Module SH_Proof <: STRAIGHTLINE_HOARE_TRIPLE_PROOF.

Include cprogs.dlist.append.path0.

Theorem proof: functional_correctness_statement.
Proof.
  cbv delta [functional_correctness_statement].
  intros.
  forward.
  unfold listrep.
  sep_apply listrep_pre_is_not_null.
  Intros b l1c w.
  forward.
  Exists b l1c w x' x' y'.
  entailer!.
Qed.

End SH_Proof.
