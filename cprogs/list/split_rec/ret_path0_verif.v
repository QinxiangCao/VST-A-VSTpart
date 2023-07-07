Require Import utils.VSTALib.

Require Import cprogs.list.program.
Require Import cprogs.list.definitions.
Require Import cprogs.list.annotation.
Require cprogs.list.split_rec.ret_path0.

Module SH_Proof <: STRAIGHTLINE_HOARE_TRIPLE_PROOF.

Include cprogs.list.split_rec.ret_path0.

Theorem proof: functional_correctness_statement.
Proof.
  cbv delta [functional_correctness_statement].
  intros.
  Intros.
  subst p' q' x'.
  forward.
  sep_apply listrep_is_null.
  Intros.
  subst l.
  forward.
  Exists l1 l2 p0 q0.
  entailer!.
  constructor.
Qed.

End SH_Proof.
