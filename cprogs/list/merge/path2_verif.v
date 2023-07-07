Require Import utils.VSTALib.

Require Import cprogs.list.program.
Require Import cprogs.list.definitions.
Require Import cprogs.list.annotation.
Require cprogs.list.merge.path2.

Module SH_Proof <: STRAIGHTLINE_HOARE_TRIPLE_PROOF.

Include cprogs.list.merge.path2.

Theorem proof: functional_correctness_statement.
Proof.
  cbv delta [functional_correctness_statement].
  intros.
  Intros l1 l2 l3 u t x y pret.
  change val in u.
  forward. forward.
  sep_apply (listrep_is_not_null l1).
  Intros a1 l1' x'.
  subst l1.
  sep_apply (listrep_is_not_null l2).
  Intros a2 l2' y'.
  subst l2.
  simpl in H0, H1.
  forward. forward. forward.
  forward. forward. forward.
  Exists (a1 :: l1') l2' (l3 ++ [a2])
         y'
         (field_address (Tstruct _list noattr) [StructField _tail] y)
         x y' pret.
  entailer!.
  + split.
    - unfold merge_steps.
      transitivity_n1 (a1 :: l1', a2 :: l2', l3).
      * tauto.
      * constructor.
        lia.
    - tauto.
  + unfold_data_at (store_list_cell y a2 y').
    sep_apply lbseg_store.
    unfold listrep; fold listrep.
    Exists x'.
    entailer!.
Qed.

End SH_Proof.
