Require Import utils.VSTALib.

Require Import cprogs.add.program.
Require Import cprogs.add.definitions.
Require Import cprogs.add.annotation.
Require cprogs.add.add.ret_path0.

Module SH_Proof <: STRAIGHTLINE_HOARE_TRIPLE_PROOF.

Include cprogs.add.add.ret_path0.

Theorem proof: functional_correctness_statement.
Proof.
  cbv delta [functional_correctness_statement].
  intros.
  Intros.
  subst x' y'.
  forward.
  forward.
  Exists (Vint (IntRepr (x0 + y0))).
  entailer!.
Qed.

End SH_Proof.

