Require Import utils.VSTALib.

Require Import cprogs.interpreter.program.
Require Import cprogs.interpreter.definitions.
Require Import cprogs.interpreter.annotation.
Require cprogs.interpreter.step.ret_path2.

Module SH_Proof <: STRAIGHTLINE_HOARE_TRIPLE_PROOF.

Include cprogs.interpreter.step.ret_path2.

Theorem proof: functional_correctness_statement.
Proof.
  cbv delta [functional_correctness_statement].
  intros. unfold prog_rep. Intros pr. subst.
  destruct pr; simpl prog_rep'.
  - Intros foc ectx.
    forward. forward. forward.
    destruct_cmd c.
    forward.
    forward_call foc.
    forward. unfold prog_rep_or_end.
    destruct l; simpl cont_list_rep'.
    + Exists (None : option res_prog).
      simpl prog_rep_or_end'. entailer!.
    + Intros cp link.
      Exists (Some (P_Ectx c l)).
      simpl prog_rep_or_end'. Exists ectx cp link.
      entailer!.
  - Intros ectx cp link.
    forward. forward.
    discriminate H.
Qed.

End SH_Proof.
