Require Import utils.VSTALib.

Require Import cprogs.interpreter.program.
Require Import cprogs.interpreter.definitions.
Require Import cprogs.interpreter.annotation.
Require cprogs.interpreter.eval.ret_path17.

Module SH_Proof <: STRAIGHTLINE_HOARE_TRIPLE_PROOF.

Include cprogs.interpreter.eval.ret_path17.

Theorem proof: functional_correctness_statement.
Proof.
  cbv delta [functional_correctness_statement].
  intros. unfold expr_rep. Intros e; subst.
  destruct_expr e.
  forward.
  forward_call (st, m, arg, m, arg, st).
  unfold expr_rep. Exists e. cancel.
  Intros ret. forward.
  forward_call. Intros ret2.
  forward. unfold expr_rep. Intros e0.
  Exists (Vint ret2) (E_Deref e0).
  simpl expr_rep'. Exists arg. entailer!.
Qed.

End SH_Proof.
