Require Import utils.VSTALib.

Require Import cprogs.interpreter.program.
Require Import cprogs.interpreter.definitions.
Require Import cprogs.interpreter.annotation.
Require cprogs.interpreter.step.ret_path6.

Module SH_Proof <: STRAIGHTLINE_HOARE_TRIPLE_PROOF.

Include cprogs.interpreter.step.ret_path6.

Theorem proof: functional_correctness_statement.
Proof.
  cbv delta [functional_correctness_statement].
  intros. unfold prog_rep. Intros pr. subst.
  destruct pr; simpl prog_rep'.
  - Intros foc ectx.
    forward. forward. forward.
    destruct_cmd c.
    forward. forward. forward. forward.
    forward_call. unfold cmd_rep, cont_list_rep.
    Exists c2 l. cancel.
    Intros ret. forward.
    forward_call foc.
    forward.
    unfold prog_rep_or_end, cont_list_rep. Intros l0.
    Exists (Some (P_Foc c1 l0)).
    simpl prog_rep_or_end'. Exists sub ret. entailer!.
  - Intros ectx cp link.
    forward. forward.
    discriminate H.
Qed.

End SH_Proof.
