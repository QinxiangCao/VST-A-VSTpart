Require Import utils.VSTALib.

Require Import cprogs.list.program.
Require Import cprogs.list.definitions.
Require Import cprogs.list.annotation.
Require cprogs.list.append_2p.path1.

Module SH_Proof <: STRAIGHTLINE_HOARE_TRIPLE_PROOF.

Include cprogs.list.append_2p.path1.
  
Theorem proof: functional_correctness_statement.
Proof.
  cbv delta [functional_correctness_statement].
  intros.
  Intros s1a s1b u t y px.
  change val in u.
  subst s1.
  forward.
  forward.
  forward.
  sep_apply listrep_is_not_null.
  Intros b s1c q.
  subst s1b.
  forward.
  unfold_data_at (store_list_cell u b q).
  Exists (s1a ++ b :: nil) s1c q (field_address (Tstruct _list noattr) [StructField _tail] u) y px.
  entailer!.
  + rewrite <- app_assoc.
    reflexivity.
  + sep_apply lbseg_store.
    entailer!.
Qed.

End SH_Proof.
