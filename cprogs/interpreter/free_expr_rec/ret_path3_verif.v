Require Import utils.VSTALib.

Require Import cprogs.interpreter.program.
Require Import cprogs.interpreter.definitions.
Require Import cprogs.interpreter.annotation.
Require cprogs.interpreter.free_expr_rec.ret_path3.

Module SH_Proof <: STRAIGHTLINE_HOARE_TRIPLE_PROOF.

Include cprogs.interpreter.free_expr_rec.ret_path3.

Theorem proof: functional_correctness_statement.
Proof.
  cbv delta [functional_correctness_statement].
  intros. unfold expr_rep. Intros e.
  destruct_expr e.
  forward.
  forward_call e'.
  forward_call arg.
  unfold expr_rep. Exists e. cancel.
  forward.
Qed.

End SH_Proof.
