Require Import utils.VSTALib.

Require Import cprogs.interpreter.program.
Require Import cprogs.interpreter.definitions.
Require Import cprogs.interpreter.annotation.
Require cprogs.interpreter.step.ret_path0.

Module SH_Proof <: STRAIGHTLINE_HOARE_TRIPLE_PROOF.

Include cprogs.interpreter.step.ret_path0.

Theorem proof: functional_correctness_statement.
Proof.
  cbv delta [functional_correctness_statement].
  intros. unfold prog_rep. Intros pr. subst.
  destruct pr; simpl prog_rep'.
  - Intros foc ectx.
    forward. forward.
    forward.
    destruct_cmd c.
    forward.
    forward_call (st, m, arg, m, arg, st).
    unfold expr_rep. Exists cond. cancel.
    Intros ret. forward.
    forward. forward.
    forward_call (sub, sub).
    unfold cmd_rep. Exists c. cancel.
    Intros ret2. forward. forward. forward.
    forward_call.
    { unfold cmd_rep at 1 3, cont_list_rep, expr_rep. Intros c1 e.
      Exists (C_While e c1) l.
      simpl cmd_rep'. Exists arg sub.
      cancel. }
    Intros ret3. forward. forward. forward.
    unfold prog_rep_or_end, cmd_rep, cont_list_rep.
    Intros l2 c2.
    Exists (Some (P_Foc c2 l2)).
    simpl prog_rep_or_end'. Exists ret2 ret3.
    cancel.
  - Intros ectx cp link.
    forward. forward.
    discriminate H.
Qed.

End SH_Proof.
