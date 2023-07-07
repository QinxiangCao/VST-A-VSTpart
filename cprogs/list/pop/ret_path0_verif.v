Require Import utils.VSTALib.

Require Import cprogs.list.program.
Require Import cprogs.list.definitions.
Require Import cprogs.list.annotation.
Require cprogs.list.pop.ret_path0.

Module SH_Proof <: STRAIGHTLINE_HOARE_TRIPLE_PROOF.

Include cprogs.list.pop.ret_path0.

Theorem proof: functional_correctness_statement.
Proof.
  cbv delta [functional_correctness_statement].
  intros.
  unfold listrep; fold listrep.
  Intros y.
  subst p'.
  forward. forward. forward. forward.
  forward_call q.
  forward.
  Exists y (Vint (IntRepr x0)).
  entailer!.
Qed.

End SH_Proof.

