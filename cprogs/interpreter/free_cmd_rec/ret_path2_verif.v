Require Import utils.VSTALib.

Require Import cprogs.interpreter.program.
Require Import cprogs.interpreter.definitions.
Require Import cprogs.interpreter.annotation.
Require cprogs.interpreter.free_cmd_rec.ret_path2.

Module SH_Proof <: STRAIGHTLINE_HOARE_TRIPLE_PROOF.

Include cprogs.interpreter.free_cmd_rec.ret_path2.

Theorem proof: functional_correctness_statement.
Proof.
  cbv delta [functional_correctness_statement].
  intros. unfold cmd_rep. Intros c.
  destruct_cmd c.
  forward.
  forward.
  forward_call c'.
  forward_call sub.
  { unfold cmd_rep. Exists c1. cancel. }
  forward_call sub0.
  { unfold cmd_rep. Exists c2. cancel. }
  forward.
Qed.

End SH_Proof.
