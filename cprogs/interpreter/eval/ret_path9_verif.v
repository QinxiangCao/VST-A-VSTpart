Require Import utils.VSTALib.

Require Import cprogs.interpreter.program.
Require Import cprogs.interpreter.definitions.
Require Import cprogs.interpreter.annotation.
Require cprogs.interpreter.eval.ret_path9.

Module SH_Proof <: STRAIGHTLINE_HOARE_TRIPLE_PROOF.

Include cprogs.interpreter.eval.ret_path9.

Theorem proof: functional_correctness_statement.
Proof.
  cbv delta [functional_correctness_statement].
  intros. unfold expr_rep. Intros e; subst.
  destruct_expr e.
  forward. forward. forward.
  forward_call (st, m, arg, m, arg, st).
  unfold expr_rep. Exists e1. cancel.
  Intros ret. forward.
  destruct_bop op.
  forward_call (st, m, arg0, m, arg0, st).
  unfold expr_rep. Exists e2. cancel.
  Intros ret2.
  forward. forward.
  forward. unfold expr_rep. Intros e0.
  Exists (Vint (Int.repr 0)) (E_Binop O_Div e e0).
  simpl expr_rep'. Exists arg arg0. entailer!.
Qed.

End SH_Proof.
