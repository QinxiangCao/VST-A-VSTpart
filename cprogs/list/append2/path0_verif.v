Require Import utils.VSTALib.

Require Import cprogs.list.program.
Require Import cprogs.list.definitions.
Require Import cprogs.list.annotation.
Require cprogs.list.append2.path0.

Module SH_Proof <: STRAIGHTLINE_HOARE_TRIPLE_PROOF.

Include cprogs.list.append2.path0.

Theorem proof: functional_correctness_statement.
Proof.
  cbv delta [functional_correctness_statement].
  intros.
  forward.
  sep_apply listrep_is_not_null.
  Intros a s1b z.
  forward.
  forward.
  sep_apply listrep_is_not_null.
  Intros b s1c w.
  forward.
  forward.
  Exists a (b :: s1c) x' x' y' z.
  entailer!.
  unfold listrep at 4; fold listrep.
  Exists w.
  cancel. apply wand_sepcon_adjoint.
  cancel.
Qed.

End SH_Proof.

