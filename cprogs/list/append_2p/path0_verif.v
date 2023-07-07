Require Import utils.VSTALib.

Require Import cprogs.list.program.
Require Import cprogs.list.definitions.
Require Import cprogs.list.annotation.
Require cprogs.list.append_2p.path0.

Module SH_Proof <: STRAIGHTLINE_HOARE_TRIPLE_PROOF.

Include cprogs.list.append_2p.path0.

Theorem proof: functional_correctness_statement.
Proof.
  cbv delta [functional_correctness_statement].
  intros.
  forward_call tt.
  { entailer!. }
  Intros ret.
  destruct ret as [t' t].
  simpl fst; simpl snd.
  forward.
  forward.
  forward.
  Exists (@nil Z) s1 x' t y' t.
  unfold lbseg.
  entailer!.
Qed.

End SH_Proof.

