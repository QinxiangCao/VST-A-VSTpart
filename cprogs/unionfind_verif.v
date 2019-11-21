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

Import AClight.revert.
Import AClight.localization.
Print PROPx.
Inductive generalize_EX_wand: (environ -> mpred) -> (environ -> mpred) -> (environ -> mpred) -> Prop :=
| generalize_EX_wand_done: forall Pr LP LQ SP SQ,
    generalize_EX_wand (PROPx Pr (LOCALx LP (SEPx SP)))
                       (PROPx Pr (LOCALx LQ (SEPx SQ)))
                       (!! (fold_right and True Pr) -->
                           (PROPx nil (LOCALx LP (SEPx SP))) -*
                           (PROPx nil (LOCALx LQ (SEPx SQ))))
| generalize_EX_wand_step': forall A (P Q R: A -> environ -> mpred),
    (forall a, generalize_EX_wand (P a) (Q a) (R a)) ->
    generalize_EX_wand (exp P) (exp Q) (allp R).

Lemma generalize_EX_wand_step: forall A (P Q R: A -> environ -> mpred),
  (forall a, exists R', generalize_EX_wand (P a) (Q a) R' /\ R' = R a) ->
  generalize_EX_wand (exp P) (exp Q) (allp R).
Proof.
  intros.
  apply generalize_EX_wand_step'.
  intros.
  destruct (H a) as [? [? ?]].
  subst.
  auto.
Qed.

Lemma generalize_EX_wand_spec: forall P Q R,
  generalize_EX_wand P Q R -> R |-- P -* Q.
Proof.
  intros.
  induction H.
  + unfold PROPx.
    simpl fold_right.
    apply wand_sepcon_adjoint.
    normalize.
    unfold TT.
    rewrite prop_imp by auto.
    apply wand_sepcon_adjoint.
    auto.
  + apply wand_sepcon_adjoint.
    Intros y.
    Exists y.
    apply wand_sepcon_adjoint.
    apply allp_left with y.
    apply H0.
Qed.

Ltac generalize_EX_wand_rec_tac :=
  first
    [ simple apply generalize_EX_wand_step;
      let a := fresh "a" in
      intro a;
      eexists;
      split;
      [ generalize_EX_wand_rec_tac
      | match goal with
        | |- ?t = _ => super_pattern t a; reflexivity
        end
      ]
    | simple apply generalize_EX_wand_done
    ].

Ltac generalize_EX_wand_tac :=
  eapply generalize_EX_wand_spec;
  generalize_EX_wand_rec_tac.

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
    instantiate (1 := FF).
    rewrite orp_FF.
(*
Check sepcon_EnvironBox_weaken.

eapply sepcon_EnvironBox_weaken.

generalize_EX_wand_tac.
rewrite !allp_uncurry'.

  match goal with
  | |- _ |-- _ * EnvironBox _ (allp ?Frame) =>
    let a := fresh "a" in
    let F := fresh "F" in
      eapply @sepcon_EnvironBox_weaken; 
      [ apply @allp_derives; intro a;
        match goal with
        | |- _ |-- 
             (PROPx _ (LOCALx ?QL' (SEPx ?RL')) -*
              PROPx _ (LOCALx ?QG' (SEPx ?RG'))) =>
            try super_pattern Pure a;
            try super_pattern QL' a;
            try super_pattern QG' a;
            try super_pattern RL' a;
            try super_pattern RG' a
        end;
        match goal with
        | |- _ |-- ?Right => super_pattern Right a; apply derives_refl
        end
      |]
  end.
Locate canonical_ram_reduce1.
  
eapply canonical_ram_reduce1;
    [ super_solve_split
    | solve_LOCALx_entailer_tac
    | intro; solve_LOCALx_entailer_tac
    | intro; solve_LOCALx_entailer_tac
    | ].



Ltac simplify_ramif :=
  eapply sepcon_EnvironBox_weaken; [canonical_ram_reduce0 | cbv beta];
  
  match goal with
  | |- _ |-- _ * EnvironBox _ (allp ?Frame) =>
    let a := fresh "a" in
    let F := fresh "F" in
      eapply @sepcon_EnvironBox_weaken; 
      [ apply @allp_derives; intro a;
        match goal with
        | |- _ |-- !! ?Pure -->
             (PROPx _ (LOCALx ?QL' (SEPx ?RL')) -*
              PROPx _ (LOCALx ?QG' (SEPx ?RG'))) =>
            try super_pattern Pure a;
            try super_pattern QL' a;
            try super_pattern QG' a;
            try super_pattern RL' a;
            try super_pattern RG' a
        end;
        match goal with
        | |- _ |-- ?Right => super_pattern Right a; apply derives_refl
        end
      |]
  end;

  eapply canonical_ram_reduce1;
    [ super_solve_split
    | solve_LOCALx_entailer_tac
    | intro; solve_LOCALx_entailer_tac
    | intro; solve_LOCALx_entailer_tac
    | ];

  match goal with
  | |- _ |-- _ * ModBox _ (allp ?Frame) =>
    let a := fresh "a" in
    let F := fresh "F" in
      eapply @sepcon_EnvironBox_weaken; 
      [ apply @allp_derives; intro a;
        match goal with
        | |- _ |-- !! ?Pure --> (SEPx ?RL' -* SEPx ?RG') =>
            try super_pattern Pure a;
            try super_pattern RL' a;
            try super_pattern RG' a
        end;
        match goal with
        | |- _ |-- ?Right => super_pattern Right a; apply derives_refl
        end
      |]
  end;

  eapply canonical_ram_reduce2;
  unfold fold_right_sepcon_emp;

  try
   (let a := fresh "a" in
    eapply @sepcon_weaken; 
    [ apply @allp_derives; intro a;
      match goal with
      | |- ?Left |-- !! True --> ?F =>
          let ll := fresh "l" in
          set (ll := Left); rewrite (@prop_imp mpred _ True F I); subst ll;
          super_pattern F a; apply derives_refl
      end
    |]);

  try apply remove_allp_RamUnit.
    *)
  admit. (* entailment with ModBox *) }
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
  forwardD.
  admit. (* entailment with ModBox *)
  forwardD.
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
Admitted.
(* 
  intro.
  remember (vgamma g x) as rpa eqn:?H. destruct rpa as [r pa].
  Import VST.floyd.freezer.
  (* p = x -> parent; *)
  localize [data_at sh node_type (vgamma2cdata (vgamma g x)) (pointer_val_val x)]. rewrite <- H0. simpl vgamma2cdata.
  forward. 1: entailer!; destruct pa; simpl; auto.
  unlocalize [whole_graph sh g].
  1: rewrite <- H0; simpl vgamma2cdata; apply (@vertices_at_ramif_1_stable _ _ _ _ SGBA_VST _ _ (SGA_VST sh) g (vvalid g) x (r, pa)); auto.
  assert (H_PARENT_Valid: vvalid g pa) by (eapply valid_parent; eauto).
  (* if (p != x) { *)
  forward_if
    (EX g'': Graph, EX rt : pointer_val,
     PROP (findS g x g'' /\ uf_root g'' x rt)
     LOCAL (temp _p (pointer_val_val rt)) (* ; temp _x (pointer_val_val x)) *)
     SEP (whole_graph sh g'')).
  - apply denote_tc_test_eq_split; apply graph_local_facts; auto.
  - (* p0 = find(p); *)
    forward_call (sh, g, pa). Intros vret. destruct vret as [g' root]. simpl fst in *. simpl snd in *.
    Opaque pointer_val_val. forward. Transparent pointer_val_val.
    localize [data_at sh node_type (Vint (Int.repr (Z.of_nat r)), pointer_val_val pa) (pointer_val_val x)].
    forward.
    unlocalize [EX g'' : Graph, !! (findS g x g'' /\ uf_root g'' x root) && vertices_at sh (vvalid g'') g''].
    (* The main ramification entailment. *)
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
        -- apply reachable_refl; auto.
    (* End ramification entailment. *)
    + clear. entailer!. Exists g'' root. entailer!.
  - forward. Exists g x. entailer!. apply false_Cne_eq in H1. subst pa. split; split; [|split| |]; auto.
    + reflexivity.
    + apply (uf_equiv_refl _  (liGraph g)).
    + repeat intro; auto.
    + apply uf_root_vgamma with (n := r); auto.
  - Intros g'' rt. forward. Exists g'' rt. entailer!.
Qed. (* Original: 47.715 secs; VST 2.*: 2.335 secs *) *)
