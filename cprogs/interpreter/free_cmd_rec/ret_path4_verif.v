Require Import utils.VSTALib.

Require Import cprogs.interpreter.program.
Require Import cprogs.interpreter.definitions.
Require Import cprogs.interpreter.annotation.
Require cprogs.interpreter.free_cmd_rec.ret_path4.

Module SH_Proof <: STRAIGHTLINE_HOARE_TRIPLE_PROOF.

Include cprogs.interpreter.free_cmd_rec.ret_path4.

Theorem proof: functional_correctness_statement.
Proof.
  cbv delta [functional_correctness_statement].
  intros. unfold cmd_rep. Intros c.
  destruct_cmd c.
  forward. forward.
  forward_call c'.
  forward_call arg.
  { unfold expr_rep. Exists cond. cancel. }
  forward_call sub.
  { unfold cmd_rep. Exists c. cancel. }
  forward.
Qed.

End SH_Proof.
