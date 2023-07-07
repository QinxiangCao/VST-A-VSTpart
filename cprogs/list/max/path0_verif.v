Require Import utils.VSTALib.

Require Import cprogs.list.program.
Require Import cprogs.list.definitions.
Require Import cprogs.list.annotation.
Require cprogs.list.max.path0.

Module SH_Proof <: STRAIGHTLINE_HOARE_TRIPLE_PROOF.

Include cprogs.list.max.path0.

Theorem proof: functional_correctness_statement.
Proof.
  cbv delta [functional_correctness_statement].
  intros.
  Intros.
  subst p'.
  forward.
  Exists (@nil Z) l 0 p0 (Vint (IntRepr 0)).
  entailer!.
  unfold lseg.
  entailer!.
Qed.

End SH_Proof.

