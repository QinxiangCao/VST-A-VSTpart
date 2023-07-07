Require Import utils.VSTALib.

Require Import cprogs.max3.program.
Require Import cprogs.max3.definitions.
Require Import cprogs.max3.annotation.
Require cprogs.max3.max3.ret_path3.

Module SH_Proof <: STRAIGHTLINE_HOARE_TRIPLE_PROOF.

Include cprogs.max3.max3.ret_path3.

Theorem proof: functional_correctness_statement.
Proof.
  cbv delta [functional_correctness_statement].
  intros.
  Intros.
  subst x' y' z'.
  forward.
  forward.
  forward.
  Exists x0 (Vint (IntRepr (x0))).
  entailer!.
Qed.

End SH_Proof.

