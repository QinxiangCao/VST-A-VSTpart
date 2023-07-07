Require Import utils.VSTALib.

Require Import cprogs.list.program.
Require Import cprogs.list.definitions.
Require Import cprogs.list.annotation.
Require cprogs.list.merge_alter_proof.path1.

Module SH_Proof <: STRAIGHTLINE_HOARE_TRIPLE_PROOF.

Include cprogs.list.merge_alter_proof.path1.

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
  simpl in H0, H2.
  forward. forward. forward.
  forward. forward. forward.
  Exists l1' (a2 :: l2') (l3 ++ [a1])
         x'
         (field_address (Tstruct _list noattr) [StructField _tail] x)
         x' y pret.
  entailer!.
  + split; [| split; [| split] ].
    - rewrite H.
      simpl.
      rewrite <- !app_assoc.
      reflexivity.
    - rewrite <- app_assoc.
      apply increasing_app_cons.
      * apply increasing_app_cons_inv1 in H3.
        tauto.
      * split; [lia |].
        apply increasing_app_cons_inv2 in H1.
        tauto.
    - tauto.
    - rewrite <- app_assoc.
      tauto.
  + unfold_data_at (store_list_cell x a1 x').
    sep_apply lbseg_store.
    unfold listrep; fold listrep.
    Exists y'.
    entailer!.
Qed.

End SH_Proof.
