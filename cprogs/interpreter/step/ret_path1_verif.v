Require Import utils.VSTALib.

Require Import cprogs.interpreter.program.
Require Import cprogs.interpreter.definitions.
Require Import cprogs.interpreter.annotation.
Require cprogs.interpreter.step.ret_path1.

Module SH_Proof <: STRAIGHTLINE_HOARE_TRIPLE_PROOF.

Include cprogs.interpreter.step.ret_path1.

Theorem proof: functional_correctness_statement.
Proof.
  cbv delta [functional_correctness_statement].
  intros. unfold prog_rep. Intros pr. subst.
  destruct pr; simpl prog_rep'.
  - Intros foc ectx.
    forward. forward.
    subst foc. sep_apply cmd_rep'_local_facts.
    Intros. destruct Pnullval.
  - Intros ectx cp link.
    forward. forward. forward.
    forward. forward. forward. forward.
    forward_call ectx.
    forward. unfold prog_rep_or_end.
    Exists (Some (P_Foc h l)). simpl prog_rep_or_end'.
    Exists cp link. cancel.
Qed.

End SH_Proof.
