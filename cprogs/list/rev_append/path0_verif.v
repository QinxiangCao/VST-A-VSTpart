Require Import utils.VSTALib.

Require Import cprogs.list.program.
Require Import cprogs.list.definitions.
Require Import cprogs.list.annotation.
Require cprogs.list.rev_append.path0.

Module SH_Proof <: STRAIGHTLINE_HOARE_TRIPLE_PROOF.

Include cprogs.list.rev_append.path0.

Theorem proof: functional_correctness_statement.
Proof.
  cbv delta [functional_correctness_statement].
  intros.
  forward_if; [forward; apply TT_right |].
  forward.
  sep_apply listrep_is_not_null.
  Intros a l1b q.
  forward. forward.
  Exists a (@nil Z) l1b p' p' q q'.
  entailer!.
  unfold lseg.
  entailer!.
Qed.

End SH_Proof.
