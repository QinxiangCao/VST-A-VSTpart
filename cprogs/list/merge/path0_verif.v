Require Import utils.VSTALib.

Require Import cprogs.list.program.
Require Import cprogs.list.definitions.
Require Import cprogs.list.annotation.
Require cprogs.list.merge.path0.

Module SH_Proof <: STRAIGHTLINE_HOARE_TRIPLE_PROOF.

Include cprogs.list.merge.path0.

Theorem proof: functional_correctness_statement.
Proof.
  cbv delta [functional_correctness_statement].
  intros.
  forward_call tt.
  { entailer!. }
  Intros ret.
  destruct ret as [p2 pret].
  simpl fst; simpl snd.
  forward.
  forward.
  Exists s1 s2 (@nil Z) p2 pret x' y' pret.
  entailer!.
  + unfold merge_steps; reflexivity.
  + unfold lbseg.
    entailer!.
Qed.

End SH_Proof.

