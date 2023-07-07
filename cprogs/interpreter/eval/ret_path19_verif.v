Require Import utils.VSTALib.

Require Import cprogs.interpreter.program.
Require Import cprogs.interpreter.definitions.
Require Import cprogs.interpreter.annotation.
Require cprogs.interpreter.eval.ret_path19.

Module SH_Proof <: STRAIGHTLINE_HOARE_TRIPLE_PROOF.

Include cprogs.interpreter.eval.ret_path19.

Theorem proof: functional_correctness_statement.
Proof.
  cbv delta [functional_correctness_statement].
  intros. unfold expr_rep. Intros e; subst.
  destruct_expr e.
  forward. forward. forward.
  forward_call (st, m, arg, m, arg, st).
  unfold expr_rep. Exists e1. cancel.
  Intros ret. forward.
  destruct_bop op; discriminate.
Qed.

End SH_Proof.
