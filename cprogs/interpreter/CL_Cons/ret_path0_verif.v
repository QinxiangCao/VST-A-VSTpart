Require Import utils.VSTALib.

Require Import cprogs.interpreter.program.
Require Import cprogs.interpreter.definitions.
Require Import cprogs.interpreter.annotation.
Require cprogs.interpreter.CL_Cons.ret_path0.

Module SH_Proof <: STRAIGHTLINE_HOARE_TRIPLE_PROOF.

Include cprogs.interpreter.CL_Cons.ret_path0.

Theorem proof: functional_correctness_statement.
Proof.
  cbv delta [functional_correctness_statement].
  intros.
  forward_call. cancel.
  Intros v.
  forward. forward. forward. forward.
  Exists v.
  sep_apply store_cont_list_rep.
  entailer!.
Qed.

End SH_Proof.