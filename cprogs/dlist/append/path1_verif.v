Require Import utils.VSTALib.

Require Import cprogs.dlist.program.
Require Import cprogs.dlist.definitions.
Require Import cprogs.dlist.annotation.
Require cprogs.dlist.append.path1.

Module SH_Proof <: STRAIGHTLINE_HOARE_TRIPLE_PROOF.

Include cprogs.dlist.append.path1.

Theorem proof: functional_correctness_statement.
Proof.
  cbv delta [functional_correctness_statement].
  intros.
  Intros l4 l5 a b t x y u.
  forward.
  forward.
  sep_apply listrep_pre_is_not_null.
  Intros c l6 q.
  forward.
  Exists (l4 ++ [a]) l6 c t u x y q.
  entailer!.
  - rewrite <- H0.
    rewrite <- app_assoc. reflexivity.
  - sep_apply singleton_lseg_pre.
    rewrite sepcon_comm.
    sep_apply lseg_pre_lseg_pre.
    entailer!.
Qed.

End SH_Proof.
