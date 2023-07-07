Require Import utils.VSTALib.

Require Import cprogs.interpreter.program.
Require Import cprogs.interpreter.definitions.
Require Import cprogs.interpreter.annotation.
Require cprogs.interpreter.step.ret_path7.

Module SH_Proof <: STRAIGHTLINE_HOARE_TRIPLE_PROOF.

Include cprogs.interpreter.step.ret_path7.

Theorem proof: functional_correctness_statement.
Proof.
  cbv delta [functional_correctness_statement].
  intros. unfold prog_rep. Intros pr. subst.
  destruct pr; simpl prog_rep'.
  - Intros foc ectx.
    forward. forward. forward.
    destruct_cmd c.
    forward.
    forward_call (st, m, arg, m, arg, st).
    unfold expr_rep. Exists cond. cancel.
    Intros ret. forward. forward. forward.
    forward. forward.
    forward_call sub0.
    unfold cmd_rep. Exists c2. cancel.
    forward_call arg.
    forward_call foc.
    forward.
    unfold prog_rep_or_end.
    Exists (Some (P_Foc c1 l)).
    simpl prog_rep_or_end'. Exists sub ectx.
    cancel.
  - Intros ectx cp link.
    forward. forward.
    discriminate H.
Qed.

End SH_Proof.
