Require Import AClight.proofauto.
Require Import cprogs.unionfind_prog.
Require Import cprogs.unionfind_def.
Require Import cprogs.unionfind_annot.

Definition Gprog : funspecs := ltac:(with_library prog [mallocN_spec; find_spec]).

Lemma false_Cne_eq: forall x y, typed_false tint (force_val (sem_cmp_pp Cne (pointer_val_val x) (pointer_val_val y))) -> x = y.
Proof.
  intros. hnf in H. destruct x, y; inversion H; auto. simpl in H. clear H1. unfold sem_cmp_pp in H. simpl in H. destruct (eq_block b b0).
  - destruct (Ptrofs.eq i i0) eqn:? .    
    + pose proof (Ptrofs.eq_spec i i0). rewrite Heqb1 in H0. subst; auto.
    + simpl in H. inversion H.
  - simpl in H. inversion H.
Qed.

Lemma true_Cne_neq: forall x y, typed_true tint (force_val (sem_cmp_pp Cne (pointer_val_val x) (pointer_val_val y))) -> x <> y.
Proof.
  intros. hnf in H. destruct x, y; inversion H; [|intro; inversion H0..]. simpl in H. clear H1. unfold sem_cmp_pp in H. simpl in H. destruct (eq_block b b0).
  - destruct (Ptrofs.eq i i0) eqn:? .    
    + simpl in H. inversion H.
    + subst b0. pose proof (Ptrofs.eq_spec i i0). rewrite Heqb1 in H0. intro; apply H0. inversion H1. reflexivity.
  - intro. inversion H0. auto.
Qed.

Lemma graph_local_facts: forall sh x (g: Graph), vvalid g x -> whole_graph sh g |-- valid_pointer (pointer_val_val x).
Proof.
  intros. eapply derives_trans; [apply (@vertices_at_ramif_1_stable _ _ _ _ SGBA_VST _ _ (SGA_VST sh) g (vvalid g) x (vgamma g x)); auto |].
  simpl vertex_at at 1. unfold binode. entailer!.
Qed.

Opaque pointer_val_val.

Lemma body_find: semax_body Vprog Gprog f_find find_spec.
Proof.
  start_function f_find_hint.
  forwardD.
  { destruct (vgamma g x) as [r p] eqn:?H.
    Exists r p. entailer!.
    eapply valid_parent; eauto.
  }
  forwardD.
  forwardD.
  forwardD.
  {
    forwardD.
  }
  {
    simplify_ramif.
    apply (@vertices_at_ramif_1_stable _ _ _ _ SGBA_VST _ _ (SGA_VST sh) g (vvalid g) x (r, pa)); auto.
  }
  forwardD.
  { apply denote_tc_test_eq_split; apply graph_local_facts; auto. }
  forwardD.
  forwardD.
  forwardD.
  { do 2 EExists. entailer!. 2 : ecancel. auto. }
  forwardD.
  forwardD.
  forwardD.
  forwardD.
  {
    forwardD.
  }
  {
    simplify_ramif.
    clear H3 H4.
    rename H1 into H_PARENT_Valid, H2 into H1, H5 into H2, H6 into H3.
    + pose proof (true_Cne_neq _ _ H1). 
      assert ((vgamma g' x) = (r, pa)) by (apply (findS_preserves_vgamma g); auto).
      assert (weak_valid g' root) by (right; destruct H3; apply reachable_foot_valid in H3; auto).
      assert (vvalid g' x) by (destruct H2 as [_ [[? _] _]]; rewrite <- H2; apply H).
      assert (~ reachable g' root x) by (destruct H3; apply (vgamma_not_reachable' _ _ r pa); auto).
      assert (root <> null). {
        destruct H3. apply reachable_foot_valid in H3. intro. subst root. apply (valid_not_null g' null H3). simpl. auto. }
      eapply derives_trans.
      apply (@graph_gen_redirect_parent_ramify _ (sSGG_VST sh)); eauto.
      apply sepcon_derives; [apply derives_refl|].
      apply wand_derives; [apply derives_refl|].
      Exists (Graph_gen_redirect_parent g' x root H6 H7 H8).
      apply andp_right; [|apply derives_refl]. apply prop_right. split.
      * apply (graph_gen_redirect_parent_findS g g' x r r pa root _ _ _); auto.
      * simpl. apply (uf_root_gen_dst_same g' (liGraph g') x x root); auto.
        -- apply (uf_root_edge _ (liGraph g') _ pa); auto. apply (vgamma_not_dst g' x r pa); auto.
        -- apply reachable_refl; auto. }
  forwardD.
  forwardD.
  forwardD.
  { simpl findS. simpl uf_root. Intros vret g' root g''.
    Exists g''. Exists root.
    entailer!.
  }
  { Exists g x. entailer!.
    assert (typed_false tint (force_val (sem_cmp_pp Cne (pointer_val_val pa) (pointer_val_val x)))). {
      rewrite H2. reflexivity.
    }
    apply false_Cne_eq in H5. subst pa. split; split; [|split| |]; auto.
    + reflexivity.
    + apply (uf_equiv_refl _  (liGraph g)).
    + repeat intro; auto.
    + apply uf_root_vgamma with (n := r); auto.
  }
  forwardD.
  forwardD.
  forwardD.
  forwardD.
  { Exists g''. Exists rt. entailer!. }
Qed.
