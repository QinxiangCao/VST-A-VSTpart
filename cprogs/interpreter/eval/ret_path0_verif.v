Require Import utils.VSTALib.

Require Import cprogs.interpreter.program.
Require Import cprogs.interpreter.definitions.
Require Import cprogs.interpreter.annotation.
Require cprogs.interpreter.eval.ret_path0.

Module SH_Proof <: STRAIGHTLINE_HOARE_TRIPLE_PROOF.

Include cprogs.interpreter.eval.ret_path0.

Theorem proof: functional_correctness_statement.
Proof.
  cbv delta [functional_correctness_statement].
  intros. unfold expr_rep. Intros e; subst.
  destruct_expr e.
  forward. forward.
  Exists (Vint (IntRepr v)) (E_Const v).
  simpl expr_rep'. entailer!.
Qed.

End SH_Proof.
