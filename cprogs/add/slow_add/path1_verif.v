Require Import utils.VSTALib.

Require Import cprogs.add.program.
Require Import cprogs.add.definitions.
Require Import cprogs.add.annotation.
Require cprogs.add.slow_add.path1.

Module SH_Proof <: STRAIGHTLINE_HOARE_TRIPLE_PROOF.

Include cprogs.add.slow_add.path1.

Theorem proof: functional_correctness_statement.
Proof.
  cbv delta [functional_correctness_statement].
  intros.
  Intros x1 y1 x' y'; subst x' y'.
  forward.
  forward.
  forward.
  Exists (x1 - 1) (y1 + 1) (Vint (IntRepr (x1 - 1))) (Vint (IntRepr (y1 + 1))).
  entailer!.
Qed.

End SH_Proof.

