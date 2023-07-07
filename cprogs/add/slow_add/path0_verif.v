Require Import utils.VSTALib.

Require Import cprogs.add.program.
Require Import cprogs.add.definitions.
Require Import cprogs.add.annotation.
Require cprogs.add.slow_add.path0.

Module SH_Proof <: STRAIGHTLINE_HOARE_TRIPLE_PROOF.

Include cprogs.add.slow_add.path0.

Theorem proof: functional_correctness_statement.
Proof.
  cbv delta [functional_correctness_statement].
  intros.
  Intros.
  subst x' y'.
  forward.
  Exists x0 y0 (Vint (IntRepr x0)) (Vint (IntRepr y0)).
  entailer!.
Qed.

End SH_Proof.

