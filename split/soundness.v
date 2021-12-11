Require Import AClight.AClight.
Require Import VST.floyd.proofauto.
Require Import Split.vst_ext.
Require Import Split.defs.
Require Import Split.rule.
Require Import Split.semantics.
Require Import Split.strong.
Section Soundness.

Context {CS: compspecs} {Espec: OracleKind} (Delta: tycontext).

Definition conj_rule := semax_aux_conj_rule.


(* Axiom bupd_tc_expr_cong: forall a, (|==> |> FF || tc_expr Delta a) 
                                  |-- tc_expr Delta a.

Axiom bupd_bool_type_cong: forall a, 
    (|==> |> FF || !! (bool_type (typeof a) = true))
    |-- !! (bool_type (typeof a) = true). *)


(*--------------------
Aux Lemmas
--------------------*)
Lemma all_empty_path_sem: forall posts a p,
        all_empty_path posts = true ->
        In (Basic_partial a, p) posts -> p = [].
Proof.
  intros.
  induction posts.
  + inv H0.
  + destruct H0. inv H0.
    simpl in H. destruct p;auto. inv H.
    apply IHposts;auto. simpl in H. destruct a0. destruct p1;auto.
    inv H.
Qed.

Lemma all_empty_atom_sem: forall atoms p,
        all_empty_atom atoms = true ->
        In p atoms -> p = [].
Proof.
  intros.
  induction atoms.
  + inv H0.
  + destruct H0. inv H0.
    simpl in H. destruct p;auto. inv H.
    apply IHatoms;auto. simpl in H. destruct a.  auto.
    inv H.
Qed.

Lemma all_basic_sem: forall posts X a p (HX:Non_empty_Type X),
        all_basic posts = true ->
        In (Binded_partial X HX  a, p) posts -> False.
Proof.
  intros.
  induction posts.
  + inv H. inv H0.
  + destruct H0. inv H0.
    simpl in H.  inv H.
    eapply IHposts;auto. simpl in H.
    destruct a0. destruct p0;auto.
    inv H.
Qed.

Lemma split_not_empty: forall stm res, path_split stm res ->
  ~ (pre res = [] /\ normal_atom res = []
     /\ break_atom res = [] /\ continue_atom res = []
     /\ return_atom res = []).
Proof.
  induction 1.
  + (* Non_empty_Type Here *)
    destruct HX as [x ?].  
    inv H. simpl in *. subst.
    intros C; destruct C as [? [? [? [? ?]]]]; subst; simpl in *.
    inv H2. apply H1;auto.
  + intros C; destruct C as [? [? [? [? ?]]]]; subst; simpl in *.
    apply app_eq_nil in H6. destruct H6 as [? ?].
    apply app_eq_nil in H2. destruct H2 as [? ?].
    apply app_eq_nil in H4. destruct H4 as [? ?].
    apply app_eq_nil in H5. destruct H5 as [? ?].
    destruct (classic (normal_atom res1 = [])).
    { apply IHpath_split1;auto. }
    apply atoms_conn_pres_nil in H8. destruct H8;auto.
    apply atoms_conn_atoms_nil in H3. destruct H3;auto.
    apply atoms_conn_atoms_nil in H9. destruct H9;auto.
    apply atoms_conn_atoms_nil in H10. destruct H10;auto.
    apply atoms_conn_returns_nil in H7. destruct H7;auto.
    apply IHpath_split2;auto.
  + intros C.
    inv H;simpl in *;destruct C as [? [? [? [? ?]]]].
    - inv H0.
    - inv H0.
    - inv H.
    - inv H2.
    - inv H1.
    - inv H0.
    - inv H3.
    - inv H0.
  + intros C; destruct C as [? [? [? [? ?]]]]; subst; simpl in *.
    apply app_eq_nil in H1. destruct H1 as [? ?].
    apply app_eq_nil in H2. destruct H2 as [? ?].
    apply app_eq_nil in H3. destruct H3 as [? ?].
    apply app_eq_nil in H4. destruct H4 as [? ?].
    apply app_eq_nil in H5. destruct H5 as [? ?].
    apply add_exp_to_pres_nil in H1.
    apply add_exp_to_pres_nil in H6.
    apply add_exp_to_atoms_nil in H2. apply add_exp_to_atoms_nil in H3.
    apply add_exp_to_atoms_nil in H4. apply add_exp_to_atoms_nil in H8.
    apply add_exp_to_atoms_nil in H7. apply add_exp_to_atoms_nil in H9.
    apply add_exp_to_return_atoms_nil in H5.
    apply add_exp_to_return_atoms_nil in H10.
    rewrite H1, H2, H3, H4, H5 in *.
    apply IHpath_split1;auto.
  + intros C; destruct C as [? [? [? [? ?]]]]; subst; simpl in *. inv H1.
  + intros C; destruct C as [? [? [? [? ?]]]]; subst; simpl in *.
    inv H1.
  + intros C; destruct C as [? [? [? [? ?]]]]; subst; simpl in *.
    clear H7 H6. 
    destruct (pre res1). 
    2: { inv H4. }
    1: { inv H4. destruct H as [E1 | E2].
     ++ destruct E1.  destruct IHpath_split1. repeat split;auto.
        apply app_eq_nil in H5. destruct H5;auto.
        apply app_eq_nil in H8. destruct H8;auto.    
     ++ apply app_eq_nil in H5. destruct H5.
        apply app_eq_nil in H8. destruct H8;auto.
(*         rewrite H in IHpath_split1. rewrite H3 in IHpath_split1.
        destruct IHpath_split1.
        apply app_eq_nil in H5. destruct H5.
        apply atoms_conn_pres_nil in H5.
        apply atoms_conn_pres_nil in H6.
        destruct (pre res2).
        +++ clear H5 H6.  rewrite Econt_atom in IHpath_split2. rewrite E2 in IHpath_split2.
            
            destruct (break_atom res2),(return_atom res2).
            - exfalso. destruct IHpath_split2. auto.
            - apply app_eq_nil in H4. destruct H4. 
              apply app_eq_nil in H5. destruct H5.
              apply atoms_conn_returns_nil in H4;destruct H4;auto.
              apply atoms_conn_returns_nil in H5;destruct H5;auto. discriminate. discriminate.
            - apply app_eq_nil in H2. destruct H2. 
              apply app_eq_nil in H5. destruct H5.
              apply atoms_conn_atoms_nil in H2;destruct H2;auto.
              apply atoms_conn_atoms_nil in H5;destruct H5;auto. discriminate. discriminate.
            - apply app_eq_nil in H4. destruct H4. 
              apply app_eq_nil in H5. destruct H5.
              apply atoms_conn_returns_nil in H4;destruct H4;auto.
              apply atoms_conn_returns_nil in H5;destruct H5;auto. discriminate. discriminate.
       +++ repeat split;auto.
        destruct H5;auto;discriminate.
        destruct H6;auto;discriminate. *)
        }
Qed.


Lemma nocontinue_split_result: forall c, nocontinue (path_to_statement c) = true.
Proof.
  intros.
  induction c.
  + simpl.
    auto.
  + destruct a.
    - simpl. auto.
    - simpl.
      destruct a; auto.
Qed.

Lemma noreturn_split_result: forall c, noreturn (path_to_statement c) = true.
Proof.
  intros.
  induction c.
  + simpl.
    auto.
  + destruct a.
    - simpl. auto.
    - simpl.
      destruct a; auto.
Qed.

(* -------------------------------------------------
    Find intermediate assertion for connected 
    paths/partial paths/atoms
   ------------------------------------------------- *)

Lemma add_return_to_semax_reverse: forall post ret_atom ret_val R,
  add_return_to_semax Delta R (post_conn_return post ret_atom ret_val) ->
  add_post_to_semax Delta (EX Q, Q && 
            !! ( atom_return_to_semax Delta Q R (ret_atom, ret_val))) post.
Proof.
  intros. destruct post as [post path].
  induction post.
  - simpl in H.
    apply semax_aux_seq_inv in H.
    destruct H as [Qret [H1 E2]].
    apply path_to_statement_app_aux in H1.
    apply semax_aux_seq_inv' in H1. unfold overridePost in H1.
    eapply add_post_to_semax_derives with (Q:=
    (EX Q : environ -> mpred,
                       !! semax_aux Delta Q
                            (path_to_statement ret_atom)
                            {|
                            RA_normal := Qret;
                            RA_break := FALSE;
                            RA_continue := FALSE;
                            RA_return := R |} && Q)%assert).
    { Intros Q. Exists Q. apply andp_right.
      apply ENTAIL_refl. apply prop_right. simpl.
      eapply semax_aux_seq. apply H.
      apply E2.
    }
    { eapply semax_aux_noreturn_inv in H1;[apply H1|..];eauto.
      apply noreturn_split_result.
    }
  - intros. intros x. apply H0. apply H.
Qed.
  
Lemma add_post_to_semax_reverse_group:
forall post atoms R, 
  Forall (add_post_to_semax Delta R)
      (map (post_conn_atom post) atoms) -> atoms <> nil ->
  add_post_to_semax Delta (
    EX Q, Q &&
    !!(Forall (atom_to_semax Delta Q R) atoms)
  ) post.
Proof.
  intros. rename H into H0, H0 into H.
  destruct atoms.
  - exfalso. apply H. auto.
  - induction atoms.
    + eapply add_post_to_semax_derives.
      2:{ apply add_post_to_semax_reverse.
          eapply Forall_forall in H0. apply H0. simpl.
          left. reflexivity. }
      { Intros Q. Exists Q. apply andp_right.
        + apply ENTAIL_refl.
        + apply prop_right. auto. }
    + inv H0. inv H4. assert (p::atoms<>[]) as E1. { intros C. inv C. }
      assert (Forall (add_post_to_semax Delta R)
      (map (post_conn_atom post) (p :: atoms))) as E2 by
      (constructor;auto).
      specialize (IHatoms E2 E1).
      apply add_post_to_semax_reverse in H2.
      eapply add_post_to_semax_derives.
      2:{ eapply add_post_to_semax_conj_rule.
          apply H2. apply IHatoms.  
      }
      { Intros Q1. Intros Q2.
        Exists (Q1 && Q2). apply andp_right.
        + apply ENTAIL_refl.
        + apply prop_right. constructor.
          - inv H1.
            eapply atom_to_semax_derives;[..|apply H7].
            { apply andp_left2. apply derives_refl. }
            { apply ENTAIL_refl. }
          - constructor.
            eapply atom_to_semax_derives;[..|apply H0].
            { apply andp_left1. apply derives_refl. }
            { apply ENTAIL_refl. }
            apply Forall_forall. intros.
            eapply atom_to_semax_derives.
            3: { eapply Forall_forall in H1. apply H1. right. auto. }
            { apply andp_left2. apply derives_refl. }
            { apply ENTAIL_refl. }        
      }
Qed.

Lemma add_return_to_semax_reverse_group:
forall post ret_atoms R, 
  Forall (add_return_to_semax Delta R)
  (map (
    fun ret_atom => post_conn_return post (fst ret_atom) (snd ret_atom)) ret_atoms)
   -> ret_atoms <> nil ->
  add_post_to_semax Delta (
    EX Q, Q &&
    !!(Forall (atom_return_to_semax Delta Q R) ret_atoms)
  ) post.
Proof.
  intros. rename H into H0, H0 into H.
  destruct ret_atoms.
  - exfalso. apply H. auto.
  - induction ret_atoms.
    + eapply add_post_to_semax_derives.
      2:{ apply add_return_to_semax_reverse. simpl in H0.
          inv H0. apply H3. }
      { Intros Q. Exists Q. apply andp_right.
        + apply ENTAIL_refl.
        + apply prop_right. constructor. destruct p. auto. constructor. }
    + inv H0. inv H4. assert (p::ret_atoms<>[]) as E1. { intros C. inv C. }
      assert (Forall (add_return_to_semax Delta R)
      (map (fun ret_atom : path * option expr =>
              post_conn_return post (fst ret_atom) (snd ret_atom))
           (p :: ret_atoms))) as E2 by
      (constructor;auto).
      specialize (IHret_atoms E2 E1).
      apply add_return_to_semax_reverse in H2.
      eapply add_post_to_semax_derives.
      2:{ eapply add_post_to_semax_conj_rule.
          apply H2. apply IHret_atoms.  
      }
      { Intros Q1. Intros Q2.
        Exists (Q1 && Q2). apply andp_right.
        + apply ENTAIL_refl.
        + apply prop_right. constructor.
          - inv H1.
            eapply atom_return_to_semax_derives_pre;[..|apply H7].
            { apply andp_left2. apply derives_refl. }
          - constructor. rewrite <- surjective_pairing in H0.
            eapply atom_return_to_semax_derives_pre;[..|apply H0].
            { apply andp_left1. apply derives_refl. }
            apply Forall_forall. intros.
            eapply  atom_return_to_semax_derives_pre.
            2: { eapply Forall_forall in H1. apply H1. right. auto. }
            { apply andp_left2. apply derives_refl. }
      }
Qed.

Lemma path_conn_to_semax_reverse_group1: forall a1 posts pres,
   In (Basic_partial a1, []) posts -> pres <> [] ->
      Forall (path_to_semax Delta)
         (posts_conn_pres posts pres)
      -> add_post_to_semax Delta (EX Q: assert, Q && !!
                             Forall (add_pre_to_semax Delta Q) pres) (Basic_partial a1, []).
Proof.
  intros.
  destruct pres.
  - exfalso. apply H0. auto.
  - induction pres.
    { simpl in H1. rewrite app_nil_r in H1.
      pose proof proj1 (Forall_forall _ _) H1.
      eapply semax_aux_conseq;[..|apply semax_aux_skip];
        unfold normal_ret_assert.
      + apply ENTAIL_refl.
      + unfold RA_normal, normal_ret_assert. Exists a1. apply andp_right.
        solve_andp. apply prop_right. constructor;[|constructor].
        eapply path_conn_to_semax_reverse_simple. apply H2.
        apply in_split in H. destruct H as [posts1 [posts2 H]].
        rewrite H. rewrite posts_conn_pre_app. apply in_or_app. right.
        destruct p as [p2 a2]. destruct p2;simpl;auto.
      + unfold RA_break. apply andp_left2. apply andp_left2.
        apply FF_left.
      + repeat apply andp_left2. apply FF_left.
      + intros. repeat apply andp_left2.  apply FF_left. }
    { assert (p::pres<>[]) by (intros C;inversion C).
      specialize (IHpres H2).
      assert (Forall (path_to_semax Delta) (posts_conn_pres posts (p :: pres))).
      { apply Forall_forall. intros. apply (proj1 (Forall_forall _ _) H1).
        apply in_app_or in H3. apply in_or_app. destruct H3;auto. right.
        apply in_or_app. auto. }
      specialize (IHpres H3).
      assert (add_post_to_semax Delta
             (EX Q : assert, Q && !! Forall (add_pre_to_semax Delta Q) [a])
             (Basic_partial a1, [])).
      { eapply semax_aux_conseq;[..|apply semax_aux_skip];
        unfold normal_ret_assert.
        + apply derives_aux_refl.
        + unfold RA_normal, normal_ret_assert. Exists a1. apply andp_right.
          solve_andp. apply prop_right. constructor;[|constructor].
          eapply path_conn_to_semax_reverse_simple.
          apply (proj1 (Forall_forall _ _) H1). apply in_or_app. right.
          apply in_or_app. left.
          apply in_split in H. destruct H as [posts1 [posts2 H]].
          rewrite H. rewrite posts_conn_pre_app. apply in_or_app. right.
          destruct a as [p2 a2]. destruct p2;simpl;auto.
        + unfold RA_break. repeat apply andp_left2.  apply FF_left.
        + repeat apply andp_left2.  apply FF_left.
        + intros. repeat apply andp_left2.  apply FF_left.
      }
      eapply add_post_to_semax_derives.
      2:{ eapply add_post_to_semax_conj_rule.
          apply H4. apply IHpres.  
      }
      { Intros Q1. Intros Q2.
        Exists (Q1 && Q2). apply andp_right.
        + solve_andp.
        + apply prop_right. constructor.
          - inv H6.
            eapply add_pre_to_semax_derives;[..|apply H9].
            { solve_andp. }
          - constructor.
            { inv H5. eapply add_pre_to_semax_derives_weak;[..|apply H9].
              { apply andp_left1. apply derives_refl. } }
            { inv H6. apply Forall_forall. intros.
              apply (proj1 (Forall_forall _ _) H10) in H6.
              eapply add_pre_to_semax_derives_weak;[..|apply H6].
              { apply andp_left2. apply derives_refl. } }
      }
    }    
Qed.
  


Lemma path_conn_to_semax_reverse_group2: forall a1 p1 posts pres,
   In (Basic_partial a1, p1) posts -> pres <> nil -> all_basic pres = true  ->
      Forall (path_to_semax Delta)
         (posts_conn_pres posts pres)
      -> (add_post_to_semax Delta) (EX Q: assert, Q && !!
                             Forall (add_pre_to_semax Delta Q) pres) (Basic_partial a1, p1).
Proof.
  intros.
  destruct pres.
  - exfalso. apply H0. auto.
  - destruct p as [a2 p2]. induction pres.
    { simpl in H1. destruct a2; try inversion H1. simpl in H2.
      rewrite app_nil_r in H2.
      pose proof proj1 (Forall_forall _ _) H2.
      specialize (H3 (post_conn_bind_pre (Basic_partial a, p2) p1 a1)).
      simpl in H3.
      assert ( In (Basic_assert a1 a, p1 ++ p2)
                  (posts_conn_pre posts (Basic_partial a, p2))).
      { apply in_split in H. destruct H as [posts1 [posts2 H]].
        rewrite H. rewrite posts_conn_pre_app. apply in_or_app. right.
        destruct p1.
        - simpl. left;auto.
        - simpl. left;auto.
      }
      apply H3 in H4.
      apply path_to_statement_app_aux in H4.
      apply semax_aux_seq_inv' in H4. simpl in H4.
      eapply semax_aux_post_simple;[..|apply H4];intros;
        try apply derives_refl.
      simpl. intros. Intros Q. Exists Q.
      apply andp_right;[apply derives_refl|apply prop_right].
      constructor;[|constructor]. auto.
    }
    {
      assert (E1: (a2,p2)::pres <> []). { intros C. inv C. }
      assert (E2: all_basic ((a2,p2)::pres)=true).
      { simpl in H1. destruct a2;simpl.
        + destruct a as [a3 p3]. destruct a3;auto. inv H1.
        + inv H1.
      }
      assert (E3: Forall (path_to_semax Delta) (posts_conn_pres posts ((a2,p2)::pres))).
      { apply Forall_forall. intros.
        apply (proj1 (Forall_forall _ _) H2).
        apply in_app_or in H3. apply in_or_app. destruct H3;auto.
        right. apply in_or_app. right. auto. }
      specialize (IHpres E1 E2 E3);clear E1 E2 E3.
      destruct a as [a3 p3].
      destruct a3.
      2: { destruct a2;try inv H1. }
      assert (E1: (path_to_semax Delta) (post_conn_bind_pre (Basic_partial a,p3) p1 a1)).
      {
        apply in_split in H. destruct H as [posts1 [posts2 H]].
        rewrite H in H2.
        apply (proj1 (Forall_forall _ _) H2).
        simpl. apply in_or_app. right. apply in_or_app. left.
        rewrite posts_conn_pre_app. apply in_or_app. right.
        simpl. destruct p1;simpl;auto.
      }
      simpl in E1.
      assert (E2: (add_post_to_semax Delta) (EX Q:assert, Q &&
                        !! (add_pre_to_semax Delta Q)(Basic_partial a, p3))
                                    (Basic_partial a1,p1)).
      { apply path_to_statement_app_aux in E1.
        apply semax_aux_seq_inv' in E1. simpl in E1.
        eapply semax_aux_post_simple;[..|apply E1];intros;
          try apply derives_refl.
        simpl. intros. Intros Q. Exists Q.
        apply andp_right;[apply derives_refl|]. apply prop_right.
        auto.
      }
      eapply add_post_to_semax_derives.
      2:{ eapply add_post_to_semax_conj_rule.
          apply E2. apply IHpres.  
      }
      { Intros Q1. Intros Q2.
        Exists (Q1 && Q2). apply andp_right.
        + solve_andp.
        + apply prop_right. constructor.
          - inv H4.
            eapply add_pre_to_semax_derives;[..|apply H7].
            { apply andp_left2. solve_andp. }
          - constructor.
            { eapply add_pre_to_semax_derives;[..|apply H3].
               { solve_andp. }
            }
            { inv H4. apply Forall_forall. intros.
              apply (proj1 (Forall_forall _ _) H8) in H4.
              eapply add_pre_to_semax_derives;[..|apply H4].
              { solve_andp. }
            }
      }
    }    
Qed.

Lemma path_conn_to_semax_reverse_group2': forall a1 p1 posts pres,
   In (Basic_partial a1, p1) posts -> 
   all_basic pres = true  ->
   Forall (path_to_semax Delta)
         (posts_conn_pres posts pres) ->
   pres <> nil -> 
      add_post_to_semax Delta (EX Q: assert, Q && !!
                             Forall ((add_pre_to_semax Delta) Q) pres) (Basic_partial a1, p1).
Proof.
  intros.
  eapply path_conn_to_semax_reverse_group2;[apply H|..];auto.
Qed.

Lemma path_conn_to_semax_reverse_group3: forall a1 p1 posts pres,
    In (Basic_partial a1, p1) posts -> pres <> nil ->
    (all_basic pres = false -> all_empty_path posts = true) ->
     Forall (path_to_semax Delta)
         (posts_conn_pres posts pres)
      -> add_post_to_semax Delta (EX Q: assert, Q && !!
                             Forall (add_pre_to_semax Delta Q) pres) (Basic_partial a1, p1).
Proof.
  intros.
  destruct (all_basic pres) eqn:Eb.
  - pose proof (path_conn_to_semax_reverse_group2 _ _ _ _ H H0 Eb). auto.
  - specialize (H1 eq_refl). pose proof all_empty_path_sem _ _ _ H1 H. subst.
    eapply path_conn_to_semax_reverse_group1;auto. apply H. auto.
Qed. 

Lemma path_conn_to_semax_reverse:forall p2 a2 (post:partial_path_statement) ,
path_to_semax Delta (bind_post_conn_pre post p2 a2)-> 
add_post_to_semax Delta (EX Q: assert, Q && !! (add_pre_to_semax Delta Q) (Basic_partial a2,p2)) (post).
Proof.
  intros.
  destruct post as [a1 p1].
  induction a1.
  - apply path_to_statement_app_aux in H. apply semax_aux_seq_inv in H. destruct H as [Q [H1 H2]].
    unfold overridePost in H1. eapply semax_aux_conseq;[..|apply H1]. 
    + apply derives_aux_refl.
    + unfold RA_normal.
    1:{ Exists Q. apply andp_right. solve_andp. apply prop_right. apply H2. }
    + unfold RA_break. apply derives_aux_refl.
    + unfold RA_continue. apply derives_aux_refl.
    + intros. unfold RA_return. apply derives_aux_refl.
  - simpl in H. intros x. 
    specialize (H x). apply H0 in H. auto.
Qed.

Lemma path_conn_to_semax_reverse_group4: forall post posts pres,
  pres <> []-> In (post) posts ->
   all_basic pres = true -> Forall (path_to_semax Delta) (posts_conn_pres posts pres)
      -> add_post_to_semax Delta (EX Q: assert, Q && !!
                             Forall (add_pre_to_semax Delta Q) pres) (post).
Proof.
  intros.
  destruct pres.
  - exfalso. apply H. auto.
  - induction pres.
  + unfold posts_conn_pres in H2. rewrite flat_map_concat_map in H2.
    simpl in H2. rewrite app_nil_r in H2. apply in_split in H0.
    destruct H0 as [l1 [l2 H0]]. subst posts.
    rewrite posts_conn_pre_app in H2. apply Forall_app in H2.
    destruct H2 as [H2 H3]. destruct p as [a2 p2].
    destruct a2. 2:{ inv H1. } rewrite posts_conn_basic_pre_cons in H3.
    eapply add_post_to_semax_derives.
    2:{ apply path_conn_to_semax_reverse. inv H3. apply H5. }
    Intros Q. Exists Q. apply andp_right; try solve_andp.
    apply prop_right. constructor;auto.
  + destruct p as [a1 p1], a as [a2 p2]. destruct a1, a2; inv H1.
    apply in_split in H0. destruct H0 as [l1 [l2 H0]].
    eapply add_post_to_semax_derives. 
    2:{ apply add_post_to_semax_conj_rule. 
    ++ apply IHpres.
       - intros c. inv c. 
       - simpl. auto.
       - apply Forall_forall. intros. eapply Forall_forall in H2. apply H2.
         unfold posts_conn_pres in *. rewrite flat_map_concat_map in H1.
         simpl in H3. rewrite flat_map_concat_map. simpl.
         apply in_app_or in H1. destruct H1.
         + apply in_or_app. auto.
         + apply in_or_app. right. apply in_or_app. auto.
    ++ apply path_conn_to_semax_reverse. eapply Forall_forall in H2.
      apply H2. apply in_or_app. right. apply in_or_app. left.
      rewrite H0. rewrite posts_conn_pre_app. apply in_or_app. right.
      rewrite posts_conn_basic_pre_cons. left. reflexivity. }
  { Intros Q1 Q2. Exists (Q1 && Q2). apply andp_right.
    - solve_andp.
    - apply prop_right. apply Forall_forall. intros. 
      destruct H5.
      + eapply add_pre_to_semax_derives with (P:=Q1).
        solve_andp.
        eapply Forall_forall in H1. apply H1.
        left. exact H5.
      + destruct H5. eapply add_pre_to_semax_derives with (P:=Q2).
        solve_andp.
        rewrite H5 in H3. exact H3.
        eapply add_pre_to_semax_derives with (P:=Q1).
        solve_andp.
        eapply Forall_forall in H1. apply H1. right. auto. }
Qed.

Lemma path_conn_to_semax_reverse_group4': forall post posts pres,
  In (post) posts ->
   all_basic pres = true -> Forall (path_to_semax Delta) (posts_conn_pres posts pres) -> 
    pres <> []-> add_post_to_semax Delta (EX Q: assert, Q && !!
                             Forall (add_pre_to_semax Delta Q) pres) (post).
Proof.
  intros. eapply path_conn_to_semax_reverse_group4;
  [apply H2|apply H|..];auto.
Qed.

Lemma path_conn_to_semax_reverse_group: forall x posts pres,
    In x posts ->
    (all_basic posts = true /\
     (all_basic pres = false -> all_empty_path posts = true)) ->
     Forall (path_to_semax Delta)
            (posts_conn_pres posts pres)
            ->
    pres <> nil 
      -> add_post_to_semax Delta (EX Q: assert, Q && !!
                             Forall (add_pre_to_semax Delta Q) pres) x.
Proof.
  intros. destruct H0.
  destruct x as [a1 p1]. destruct a1.
  - eapply path_conn_to_semax_reverse_group3;[apply H|..];auto.
  - exfalso. eapply all_basic_sem. apply H0. apply H.
Qed. 

Lemma path_conn_to_semax_reverse_group': forall x pres posts atoms,
    In x posts->
    ((all_basic pres = true) \/
    ( (all_basic(posts) = true)/\
      (all_empty_path posts = true)/\
      (all_empty_atom atoms = true)
    )) ->
    Forall (path_to_semax Delta) (posts_conn_pres posts pres) ->
    pres <>nil->
    add_post_to_semax Delta (EX Q: assert, Q && !!
                             Forall (add_pre_to_semax Delta Q) pres) x.
Proof.
  intros. destruct H0. destruct x as [a1 p1]. (* destruct a1. *)
  2:{ eapply path_conn_to_semax_reverse_group;auto.
      - apply H.
      - destruct H0;auto. split;auto.
        intros. apply H3.
      - auto. }
  1:{ eapply path_conn_to_semax_reverse_group4;auto.
      apply H. auto.
      }  
Qed.


Lemma atom_conn_pres_to_semax_reverse_group1: forall  atoms pres P,
   In [] atoms -> pres <> [] ->
      Forall (add_pre_to_semax Delta P)
         (atoms_conn_pres atoms pres)
      -> atom_to_semax Delta P (EX Q: assert, Q && !!
                             Forall (add_pre_to_semax Delta Q) pres) [].
Proof.
  intros. destruct pres.
  - exfalso. apply H0. auto.
  - induction pres.
    { eapply semax_aux_post_simple;[..|apply semax_aux_skip];
        intros;try apply FF_left; unfold RA_normal, normal_ret_assert.
      Exists P. apply andp_right;[apply derives_refl|apply prop_right].
      constructor;auto.
      eapply Forall_forall in H1. apply H1.
      apply in_split in H. destruct H as [atoms1 [atoms2 H]].
      rewrite H.
      simpl.
      rewrite atoms_conn_pres_app1.
      apply in_or_app. right.
      simpl. left. unfold atom_conn_pre. destruct p.
      simpl. auto. }
    { assert (p::pres<>[]) by (intros C;inversion C).
      specialize (IHpres H2).
      assert (Forall (add_pre_to_semax Delta P) (atoms_conn_pres atoms (p :: pres))).
      { apply Forall_forall. intros. apply (proj1 (Forall_forall _ _) H1).
        replace (p::pres) with ([p]++pres) in H3 by reflexivity.
        rewrite atoms_conn_pres_app2 in H3.
        apply in_app_or in H3.
        replace (p::a::pres) with([p]++[a]++pres) by reflexivity.
        rewrite atoms_conn_pres_app2. apply in_or_app.
        destruct H3;auto. right.
        apply atoms_conn_pres_app2.
        apply in_or_app. auto. }
      specialize (IHpres H3).
      assert (atom_to_semax Delta
               P (EX Q : assert, Q && !! Forall (add_pre_to_semax Delta Q) [a])
             []).
      { eapply semax_aux_post_simple;[..|apply semax_aux_skip];
          unfold normal_ret_assert;intros;try apply FF_left;unfold RA_normal.
        Exists P. apply andp_right.
        apply derives_refl. apply prop_right. constructor;[|constructor].
        apply (proj1 (Forall_forall _ _) H1).
        apply in_split in H. destruct H as [atoms1 [atoms2 H]]. subst atoms.
        rewrite atoms_conn_pres_app1. apply in_or_app. right.
        simpl. unfold atom_conn_pre. destruct a. auto.
      }
      eapply atom_to_semax_derives.
      1:{ apply derives_refl. }
      2:{ eapply atom_to_semax_conj_rule.
          apply H4. apply IHpres.  
      }
      { Intros Q1. Intros Q2.
        Exists (Q1 && Q2). apply andp_right.
        + solve_andp.
        + apply prop_right. constructor.
          - inv H6.
            eapply add_pre_to_semax_derives;[..|apply H9].
            { solve_andp. }
          - constructor.
            { inv H5. eapply add_pre_to_semax_derives;[..|apply H9].
              { solve_andp. }
            }
            { inv H6. apply Forall_forall. intros.
              apply (proj1 (Forall_forall _ _) H10) in H6.
              eapply add_pre_to_semax_derives;[..|apply H6].
              { solve_andp. } }
      }
    }
Qed.

Lemma atom_conn_pres_to_semax_reverse_group2: forall P p pres atoms,
   In p atoms -> pres <> nil -> all_basic pres = true  ->
      Forall (add_pre_to_semax Delta P)
         (atoms_conn_pres atoms pres)
      -> atom_to_semax Delta P (EX Q: assert, Q && !!
                             Forall (add_pre_to_semax Delta Q) pres) p.
Proof.
  intros.
  destruct pres.
  - exfalso. apply H0. auto.
  -  induction pres.
    { destruct p0 as [a2 p2].
      simpl in H1. destruct a2; try inversion H1.
      pose proof proj1 (Forall_forall _ _) H2.
      specialize (H3 (atom_conn_pre p (Basic_partial a, p2))).
      assert ( In (atom_conn_pre p (Basic_partial a, p2))
         (atoms_conn_pres atoms [(Basic_partial a, p2)])).
      { apply in_split in H. destruct H as [atoms1 [atoms2 H]].
        rewrite H. rewrite atoms_conn_pres_app1. apply in_or_app. right.
        simpl. auto.
      }
      apply H3 in H4. clear H3.
      apply path_to_statement_app_aux in H4.
      apply semax_aux_seq_inv' in H4. simpl in H4.
      eapply semax_aux_post_simple;[..|apply H4];intros;
        try apply derives_refl.
      simpl. intros. Intros Q. Exists Q.
      apply andp_right;[apply derives_refl|apply prop_right].
      constructor;[|constructor].
      auto.
    }
    {
      assert (E1: p0::pres <> []). { intros C. inv C. }
      assert (E2: all_basic (p0::pres)=true).
      { destruct a as [a1 p1].
        destruct p0 as [a2 p2].
        destruct a1,a2;simpl;inv H1;auto.
      }
      assert (E3:Forall (add_pre_to_semax Delta P) (atoms_conn_pres atoms (p0 :: pres))).
      { apply Forall_forall. intros.
        apply (proj1 (Forall_forall _ _) H2).
        replace (p0::pres) with ([p0]++pres) in H3 by reflexivity.
        rewrite atoms_conn_pres_app2 in H3.
        apply in_app_or in H3.
        replace (p0::a::pres) with([p0]++[a]++pres) by reflexivity.
        rewrite atoms_conn_pres_app2. apply in_or_app.
        destruct H3;auto. right.
        apply atoms_conn_pres_app2.
        apply in_or_app. auto.  }
      specialize (IHpres E1 E2 E3);clear E1 E2 E3.
      destruct a as [a3 p3].
      destruct a3.
      2: { destruct p0 as [a2 p2]. destruct a2;try inv H1. }
      assert (E1: add_pre_to_semax Delta P (atom_conn_pre p (Basic_partial a,p3))).
      {
        apply in_split in H. destruct H as [posts1 [posts2 H]].
        rewrite H in H2.
        apply (proj1 (Forall_forall _ _) H2).
        simpl.  rewrite atoms_conn_pres_app1. apply in_or_app.
        right. apply in_or_app. left.
        simpl. auto.
      }
      simpl in E1.
      assert (E2: atom_to_semax Delta P (EX Q:assert, Q &&
                        !! (add_pre_to_semax Delta Q)(Basic_partial a, p3)
                                    ) p).
      { apply path_to_statement_app_aux in E1.
        apply semax_aux_seq_inv' in E1. simpl in E1.
        eapply semax_aux_post_simple;[..|apply E1];intros;
          try apply derives_refl.
        simpl. intros. Intros Q. Exists Q.
        apply andp_right;[apply derives_refl|]. apply prop_right.
        auto.
      }
      eapply atom_to_semax_derives.
      1:{ apply derives_refl. }
      2:{ eapply atom_to_semax_conj_rule.
          apply E2. apply IHpres.  
      }
      { Intros Q1. Intros Q2.
        Exists (Q1 && Q2). apply andp_right.
        + solve_andp.
        + apply prop_right. constructor.
          - inv H4.
            eapply add_pre_to_semax_derives;[..|apply H7].
            { solve_andp. }
          - constructor.
            { eapply add_pre_to_semax_derives;[..|apply H3].
            { solve_andp. } }
            { inv H4. apply Forall_forall. intros.
              apply (proj1 (Forall_forall _ _) H8) in H4.
              eapply add_pre_to_semax_derives;[..|apply H4].
              { solve_andp. } }
      }
    }    
Qed.

Lemma atom_conn_pres_to_semax_reverse_group2': forall P p pres atoms,
   In p atoms -> all_basic pres = true  ->
      Forall (add_pre_to_semax Delta P)
         (atoms_conn_pres atoms pres) ->
      pres <> nil
      -> atom_to_semax Delta P (EX Q: assert, Q && !!
                             Forall (add_pre_to_semax Delta Q) pres) p.
Proof. intros.
  eapply atom_conn_pres_to_semax_reverse_group2.
  apply H. auto. auto. auto.
Qed.

Lemma atom_conn_pres_to_semax_reverse_group3: forall P p atoms pres,
    In p atoms ->
    (all_basic pres = false -> all_empty_atom atoms = true) ->
     Forall (add_pre_to_semax Delta P)
            (atoms_conn_pres atoms pres) ->
      pres <> nil 
      -> atom_to_semax Delta P (EX Q: assert, Q && !!
                             Forall (add_pre_to_semax Delta Q) pres) p.
Proof.
  intros.
  destruct (all_basic pres) eqn:Eb.
  - pose proof (atom_conn_pres_to_semax_reverse_group2 P _ _ _ H H2 Eb). auto.
  - specialize (H0 eq_refl). pose proof all_empty_atom_sem _ _ H0 H. subst.
    eapply atom_conn_pres_to_semax_reverse_group1;auto. apply H. auto.
Qed.

Lemma atom_conn_pres_to_semax_reverse_group3': forall P p atoms pres,
    In p atoms ->
    ((all_basic pres = true)   \/ (all_empty_atom atoms = true)) ->
    Forall (add_pre_to_semax Delta P) (atoms_conn_pres atoms pres) ->
      pres <> nil -> 
    atom_to_semax Delta P (EX Q: assert, Q && !! Forall (add_pre_to_semax Delta Q) pres) p.
Proof.
  intros. destruct H0.
  - (*all_basic pres = true*)
    eapply atom_conn_pres_to_semax_reverse_group2';auto. 
    apply H. apply H1. 
  - (*all_empty_atom atoms = true *)
    eapply atom_conn_pres_to_semax_reverse_group3;auto.
    apply H. intros;auto. apply H1.
 Qed. 

Lemma add_return_to_atom_semax_reverse: forall atom ret_atom ret_val P R,
  atom_return_to_semax Delta P R ( atom ++ ret_atom, ret_val) ->
  atom_to_semax Delta P (EX Q, Q && !!
                 ( atom_return_to_semax Delta Q R (ret_atom, ret_val))) atom.
Proof.
  intros.
  apply semax_aux_seq_inv in H.
  destruct H as [Q_ret [H1 H2]].
  apply path_to_statement_app_aux in H1.
  apply semax_aux_seq_inv' in H1. unfold overridePost in H1.
  eapply atom_to_semax_derives with (Q1:=
    (EX Q : environ -> mpred,
                       !! semax_aux Delta Q
                            (path_to_statement ret_atom)
                            {|
                            RA_normal := Q_ret;
                            RA_break := FALSE;
                            RA_continue := FALSE;
                            RA_return := R |} && Q)%assert).
  { apply derives_refl. }
  { Intros Q. Exists Q. apply andp_right.
    solve_andp. apply prop_right. 
    eapply semax_aux_seq. apply H.
    apply H2.   }
  { eapply semax_aux_noreturn_inv in H1;[apply H1|..].
    + apply noreturn_split_result.
    + reflexivity.
    + reflexivity.
    + reflexivity.
  }
Qed.



Lemma add_return_to_atom_semax_group: forall atom atoms ret_atoms P R,
  Forall (atom_return_to_semax Delta P R)
         (atoms_conn_returns atoms ret_atoms) ->
  In atom atoms ->
   ret_atoms <> nil ->
  atom_to_semax Delta P (
    EX Q, Q &&
    !!(Forall (atom_return_to_semax Delta Q R) ret_atoms)
  ) atom.
Proof.
  intros. rename H1 into H, H into H0, H0 into H1.
  destruct ret_atoms.
  - exfalso. apply H. auto.
  - induction ret_atoms.
    + destruct r as [p v]. eapply atom_to_semax_derives.
      1:{ apply derives_refl. }
      2:{ apply add_return_to_atom_semax_reverse.
          eapply Forall_forall in H0. apply H0.
          apply in_split in H1. destruct H1 as [atoms1 [atoms2 H1]].
          rewrite H1. simpl. rewrite atoms_conn_returns_app1.
          apply in_or_app. right. simpl. left. reflexivity. }
      Intros Q. Exists Q. apply andp_right. apply andp_left2. apply derives_refl.
      apply prop_right. constructor;[|constructor]. auto.
    + eapply atom_to_semax_derives.
      1:{ apply derives_refl. }
      2:{ eapply atom_to_semax_conj_rule.
          { apply IHret_atoms.
            2:{ intros C. inv C. }
            eapply Forall_forall. intros.
              eapply Forall_forall in H0. eapply H0.
              replace (r::a::ret_atoms) with ([r]++[a]++ret_atoms) by reflexivity.
              rewrite atoms_conn_returns_app2.
              replace (r::ret_atoms) with ([r]++ret_atoms) in H2 by reflexivity.
              rewrite atoms_conn_returns_app2 in H2. apply in_app_or in H2.
              destruct  H2.
              { apply in_or_app. left. auto. }
              { apply in_or_app. right. rewrite atoms_conn_returns_app2.
                apply in_or_app. auto. }
          }
          { pose proof (proj1 (Forall_forall _ _) H0 (atom ++ fst a, snd a)).
            assert ( In (atom ++ fst a, snd a) (atoms_conn_returns atoms (r :: a :: ret_atoms))).
            { replace (r::a::ret_atoms) with ([r]++[a]++ret_atoms) by reflexivity.
              rewrite atoms_conn_returns_app2. apply in_or_app. right.
              rewrite atoms_conn_returns_app2. apply in_or_app. left.
              apply in_split in H1. destruct H1 as [atoms1 [atoms2 H1]].
              rewrite H1. rewrite atoms_conn_returns_app1.
              apply in_or_app. right. simpl. left. auto. }
            specialize ( H2 H3).
            apply add_return_to_atom_semax_reverse in H2.
            apply H2.
          }
      }
      { Intros Q1. Intros Q2. Exists (andp Q1 Q2).
        apply andp_right. apply andp_left2;apply derives_refl.
        apply prop_right. eapply Forall_forall.
        intros. inv H4;[|inv H5].
        + eapply atom_return_to_semax_derives.
          { apply andp_left1. apply derives_refl. }
          { intros. solve_andp. }
          { eapply Forall_forall in H2. apply H2. simpl. auto. }
        + eapply atom_return_to_semax_derives.
          { apply andp_left2. apply derives_refl. }
          { intros. solve_andp. }
          { destruct x. apply H3. }
        +  eapply atom_return_to_semax_derives.
          { apply andp_left1. apply derives_refl. }
          { intros. solve_andp. }
          { eapply Forall_forall in H2. apply H2. simpl. auto. }
      }  
Qed.

  
Lemma atom_conn_atom_to_semax_reverse: forall atom1 atom2 P R,
  atom_to_semax Delta P R (atom1 ++  atom2) ->
  atom_to_semax Delta P (EX Q, Q && !!
                 ( atom_to_semax Delta Q R atom2)) atom1.
Proof.
  intros. apply path_to_statement_app_aux in H.
  apply semax_aux_seq_inv' in H. unfold overridePost in H.
  eapply atom_to_semax_derives with (Q1:=
   (EX Q : environ -> mpred,
                       !! semax_aux Delta Q 
                            (path_to_statement atom2)
                            {|
                            RA_normal := R;
                            RA_break := FALSE;
                            RA_continue := FALSE;
                            RA_return := fun _ : option val => FALSE |} && Q)%assert).
  { apply derives_refl. }
  { Intros Q. Exists Q. apply andp_right.
    apply ENTAIL_refl. apply prop_right. 
    auto. }
  { auto. }
Qed.


Lemma atoms_conn_atoms_app1: forall atoms1 atoms2 rets,
    atoms_conn_atoms (atoms1 ++ atoms2) rets =
    atoms_conn_atoms atoms1 rets ++ atoms_conn_atoms atoms2 rets.
Proof.
  intros.
  induction atoms1.
  - rewrite app_nil_l. simpl. reflexivity.
  - rewrite <- app_comm_cons.
    simpl.
    rewrite IHatoms1.
    rewrite app_assoc.
    reflexivity.
Qed.

Lemma atoms_conn_atoms_app2: forall atoms rets1 rets2 x,
    In x (atoms_conn_atoms atoms (rets1++rets2)) <->
    In x (atoms_conn_atoms atoms rets1 ++ atoms_conn_atoms atoms rets2).
Proof.
  intros.
  induction atoms.
  - rewrite app_nil_l. simpl. reflexivity.
  - split;intro.
    + apply in_or_app. simpl in H.  apply in_app_or in H.
      destruct H.
      { rewrite map_app in H. apply in_app_or in H. destruct H.
        - left. apply in_or_app. auto.
        - right. apply in_or_app. auto.
      }
      { apply IHatoms in H. apply in_app_or in H. destruct H.
        - left. apply in_or_app. auto.
        - right. apply in_or_app. auto.
      }
    + apply in_or_app. apply in_app_or in H. destruct H.
      { rewrite map_app. apply in_app_or in H. destruct H.
        - left. apply in_or_app. auto.
        - right. apply IHatoms. apply in_or_app. auto.
      }
      {  rewrite map_app. apply in_app_or in H. destruct H.
        - left. apply in_or_app. auto.
        - right. apply IHatoms. apply in_or_app. auto.
      }
Qed.



Lemma atom_conn_atom_to_semax_reverse_group: forall atom atoms1 atoms2 P R,
    Forall (atom_to_semax Delta P R)
         (atoms_conn_atoms atoms1 atoms2) ->
    In atom atoms1 ->
    atoms2 <> nil ->
  atom_to_semax Delta P (
    EX Q, Q &&
    !!(Forall (atom_to_semax Delta Q R) atoms2)
  ) atom.
Proof.
  intros. rename H1 into H, H into H0, H0 into H1.
  destruct atoms2.
  - exfalso. apply H. auto.
  - induction atoms2.
    + eapply atom_to_semax_derives.
      1:{ apply derives_refl. }
      2:{ apply atom_conn_atom_to_semax_reverse.
          eapply Forall_forall in H0. apply H0.
          apply in_split in H1. destruct H1 as [atoms'1 [atoms'2 H1]].
          rewrite H1. unfold atoms_conn_atoms. rewrite flat_map_concat_map.
          rewrite map_app. simpl. rewrite concat_app. rewrite concat_cons.
          apply in_or_app. right. simpl. left. reflexivity. }
      Intros Q. Exists Q. apply andp_right. apply andp_left2. apply derives_refl.
      apply prop_right. constructor;[|constructor]. auto.
    + eapply atom_to_semax_derives.
      1:{ apply derives_refl. }
      2:{ eapply atom_to_semax_conj_rule.
          { apply IHatoms2.
            2:{ intros C. inv C. }
            eapply Forall_forall. intros.
              eapply Forall_forall in H0. eapply H0.
              replace (p::a::atoms2) with ([p]++[a]++atoms2) by reflexivity.
              rewrite atoms_conn_atoms_app2.
              replace (p::atoms2) with ([p]++atoms2) in H2 by reflexivity.
              rewrite atoms_conn_atoms_app2 in H2. apply in_app_or in H2.
              destruct  H2.
              { apply in_or_app. left. auto. }
              { apply in_or_app. right. rewrite atoms_conn_atoms_app2.
                apply in_or_app. auto. }
          }
          { pose proof (proj1 (Forall_forall _ _) H0 (atom++a)).
            assert ( In (atom ++ a) (atoms_conn_atoms atoms1 (p :: a :: atoms2))).
            { replace (p::a::atoms2) with ([p]++[a]++atoms2) by reflexivity.
              rewrite atoms_conn_atoms_app2. apply in_or_app. right.
              rewrite atoms_conn_atoms_app2. apply in_or_app. left.
              apply in_split in H1. destruct H1 as [atoms'1 [atoms'2 H1]].
              rewrite H1. rewrite atoms_conn_atoms_app1.
              apply in_or_app. right. simpl. left. auto. }
            specialize ( H2 H3).
            apply atom_conn_atom_to_semax_reverse in H2.
            apply H2.
          }
      }
      { Intros Q1. Intros Q2. Exists (andp Q1 Q2).
        apply andp_right. apply andp_left2;apply derives_refl.
        apply prop_right. eapply Forall_forall.
        intros. inv H4;[|inv H5].
        + eapply atom_to_semax_derives.
          { apply andp_left1. apply derives_refl. }
          { intros. apply ENTAIL_refl. }
          { eapply Forall_forall in H2. apply H2. simpl. auto. }
        + eapply atom_to_semax_derives.
          { apply andp_left2. apply derives_refl. }
          { intros. apply ENTAIL_refl. }
          {  apply H3. }
        +  eapply atom_to_semax_derives.
          { apply andp_left1. apply derives_refl. }
          { intros. apply ENTAIL_refl. }
          { eapply Forall_forall in H2. apply H2. simpl. auto. }
      }  
Qed.

(*-------------------------
Tactics for combining proofs 
for individual path/partial_paths
-------------------------*)
Ltac merge_Q Q1 Q2:=
  Intros Q1; Intros Q2; Exists (andp Q1 Q2); apply andp_right;
  [ apply derives_refl|
    apply prop_right; repeat split;auto].

Ltac merge_Q1 Q:=
  Intros Q; Exists Q; apply andp_right;
    [apply derives_refl|
     apply prop_right; repeat split;auto].

Ltac merge_Q3 Q1 Q2 Q3:=
  Intros Q1; Intros Q2; Intros Q3; Exists (Q1 && (Q2 && Q3)); apply andp_right;
  [ apply derives_refl|
    apply prop_right; repeat split;auto].

Ltac merge_Q4 Q1 Q2 Q3 Q4:=
  Intros Q1; Intros Q2; Intros Q3; Intros Q4;
  Exists (Q1 && (Q2 && (Q3 && Q4))); apply andp_right;
  [ apply derives_refl|
    apply prop_right; repeat split;auto].

Ltac merge_Q5 Q1 Q2 Q3 Q4 Q5:=
  Intros Q1; Intros Q2; Intros Q3; Intros Q4; Intros Q5;
  Exists (Q1 && (Q2 && (Q3 && (Q4 && Q5)))); apply andp_right;
  [ apply derives_refl|
    apply prop_right; repeat split;auto].

Ltac solve_split:=
match goal with
| E: Forall (atom_return_to_semax Delta _ ?R) ?ret_atoms 
  |- Forall (atom_return_to_semax Delta ?Q ?R) ?ret_atoms => 
    eapply atom_return_to_semax_derives_pre_group;[|apply E];solve_andp
| E: Forall (atom_to_semax Delta _ ?R) ?ret_atoms 
    |- Forall (atom_to_semax Delta ?Q ?R) ?ret_atoms => 
      eapply atom_to_semax_derives_pre_group;[|apply E];solve_andp
| E: Forall (add_pre_to_semax Delta _) ?pres 
  |- Forall (add_pre_to_semax Delta _) ?pres => 
    eapply add_pre_to_semax_derives_group;[|apply E];solve_andp
end.


Lemma remove_entail: forall P Q,
  P |-- Q ->
  ENTAIL Delta, P |-- Q.
Proof.
  intros. apply andp_left2. auto.
Qed.


Ltac combine_aux_post_auto:=
  match goal with
    | E1: add_post_to_semax Delta _ _ ,
      E2: add_post_to_semax Delta _ _ ,
      E3: add_post_to_semax Delta _ _ ,
      E4: add_post_to_semax Delta _ _ ,
      E5: add_post_to_semax Delta _ _ |-
      add_post_to_semax Delta _ _ =>
      let Q1 := fresh "Q" in
      let Q2 := fresh "Q" in
      let Q3 := fresh "Q" in
      let Q4 := fresh "Q" in
      let Q5 := fresh "Q" in
      eapply add_post_to_semax_derives;
      [|eapply add_post_to_semax_conj_rule;
         [apply E1|
          eapply add_post_to_semax_conj_rule;
          [apply E2|
           eapply add_post_to_semax_conj_rule;
           [apply E3|
            eapply add_post_to_semax_conj_rule;
            [apply E4|apply E5]]]]];
      try (apply remove_entail);
      merge_Q5 Q1 Q2 Q3 Q4 Q5; solve_split
    | E1: add_post_to_semax Delta _ _ ,
      E2: add_post_to_semax Delta _ _ ,
      E3: add_post_to_semax Delta _ _ ,
      E4: add_post_to_semax Delta _ _  |-
      add_post_to_semax Delta _ _ =>
      let Q1 := fresh "Q" in
      let Q2 := fresh "Q" in
      let Q3 := fresh "Q" in
      let Q4 := fresh "Q" in
      eapply add_post_to_semax_derives;
      [|eapply add_post_to_semax_conj_rule;
         [apply E1|
          eapply add_post_to_semax_conj_rule;
          [apply E2|
           eapply add_post_to_semax_conj_rule;
           [apply E3|apply E4]]]];
           try (apply remove_entail);
           merge_Q4 Q1 Q2 Q3 Q4; solve_split
    | E1: add_post_to_semax Delta _ _ ,
      E2: add_post_to_semax Delta _ _ ,
      E3: add_post_to_semax Delta _ _ |-
      add_post_to_semax Delta _ _ =>
      let Q1 := fresh "Q" in
      let Q2 := fresh "Q" in
      let Q3 := fresh "Q" in
      eapply add_post_to_semax_derives;
      [|eapply add_post_to_semax_conj_rule;
         [apply E1|
         eapply add_post_to_semax_conj_rule;[apply E2|apply E3]]];
         try (apply remove_entail);
         merge_Q3 Q1 Q2 Q3; solve_split
    | E1: add_post_to_semax Delta _ _ ,
      E2: add_post_to_semax Delta _ _ |-
      add_post_to_semax Delta _ _ =>
      let Q1 := fresh "Q" in
      let Q2 := fresh "Q" in
      eapply add_post_to_semax_derives;
        [|eapply add_post_to_semax_conj_rule;[apply E1|apply E2]];
        try (apply remove_entail);
      merge_Q Q1 Q2; solve_split
    | E1: add_post_to_semax Delta _ _ |-
      add_post_to_semax Delta _ _ =>
      let Q1 := fresh "Q" in
      eapply add_post_to_semax_derives;
      [|apply E1];try (apply remove_entail);
      merge_Q1 Q1
    | _ => idtac
   end.


Ltac combine_aux_atom_auto:=
  match goal with
    | E1: atom_to_semax Delta _ _ _ ,
      E2: atom_to_semax Delta _ _ _ ,
      E3: atom_to_semax Delta _ _ _ ,
      E4: atom_to_semax Delta _ _ _ ,
      E5: atom_to_semax Delta _ _ _ |-
      atom_to_semax Delta _ _ _ =>
      let Q1 := fresh "Q" in
      let Q2 := fresh "Q" in
      let Q3 := fresh "Q" in
      let Q4 := fresh "Q" in
      let Q5 := fresh "Q" in
      eapply atom_to_semax_derives_post;
      [|eapply atom_to_semax_conj_rule;
         [apply E1|
          eapply atom_to_semax_conj_rule;
          [apply E2|
           eapply atom_to_semax_conj_rule;
           [apply E3|
            eapply atom_to_semax_conj_rule;
            [apply E4|apply E5]]]]];
            try (apply remove_entail);
      merge_Q5 Q1 Q2 Q3 Q4 Q5; solve_split
    | E1: atom_to_semax Delta _ _ _ ,
      E2: atom_to_semax Delta _ _ _ ,
      E3: atom_to_semax Delta _ _ _ ,
      E4: atom_to_semax Delta _ _ _  |-
      atom_to_semax Delta _ _ _ =>
      let Q1 := fresh "Q" in
      let Q2 := fresh "Q" in
      let Q3 := fresh "Q" in
      let Q4 := fresh "Q" in
      eapply atom_to_semax_derives_post;
      [|eapply atom_to_semax_conj_rule;
         [apply E1|
          eapply atom_to_semax_conj_rule;
          [apply E2|
           eapply atom_to_semax_conj_rule;
           [apply E3|apply E4]]]];try (apply remove_entail);
      merge_Q4 Q1 Q2 Q3 Q4; solve_split
    | E1: atom_to_semax Delta _ _ _ ,
      E2: atom_to_semax Delta _ _ _ ,
      E3: atom_to_semax Delta _ _ _ |-
      atom_to_semax Delta _ _ _ =>
      let Q1 := fresh "Q" in
      let Q2 := fresh "Q" in
      let Q3 := fresh "Q" in
      eapply atom_to_semax_derives_post;
      [|eapply atom_to_semax_conj_rule;
         [apply E1|
         eapply atom_to_semax_conj_rule;[apply E2|apply E3]]];
         try (apply remove_entail);
      merge_Q3 Q1 Q2 Q3; solve_split
    | E1: atom_to_semax Delta _ _ _ ,
      E2: atom_to_semax Delta _ _ _ |-
      atom_to_semax Delta _ _ _ =>
      let Q1 := fresh "Q" in
      let Q2 := fresh "Q" in
      eapply atom_to_semax_derives_post;
        [|eapply atom_to_semax_conj_rule;[apply E1|apply E2]];
        try (apply remove_entail);
        merge_Q Q1 Q2; solve_split
    | E1: atom_to_semax Delta _ _ _ |-
      atom_to_semax Delta _ _ _ =>
      let Q1 := fresh "Q" in
      eapply atom_to_semax_derives_post;
      try (apply remove_entail);
      [|apply E1];merge_Q1 Q1
    | _ => idtac
   end. 



(*-------------------------
Combined proof using tactics
-------------------------*)
Lemma soundness_seq_inv_aux1:  forall l1 l2 l3 l4 l5 R1 R2 R3 R4 x,
  ~ (l1 = [] /\ l2 = [] /\ l3 = [] /\ l4 = [] /\ l5 = []) ->
  (l1 <> [] -> add_post_to_semax Delta (EX Q : assert, Q &&
                                           !! Forall (atom_to_semax Delta Q R1) l1) x) ->
  (l2 <> [] -> add_post_to_semax Delta (EX Q : assert, Q &&
                                           !! Forall (atom_to_semax Delta Q R2) l2) x) ->
  (l3 <> [] -> add_post_to_semax Delta (EX Q : assert, Q &&
                                           !! Forall (atom_to_semax Delta Q R3) l3) x) ->
  (l4 <> [] -> add_post_to_semax Delta (EX Q : assert, Q &&
                                    !! Forall (atom_return_to_semax Delta Q R4) l4) x) ->
   (l5 <> [] -> add_post_to_semax Delta (EX Q : assert, Q &&
                                         !! Forall (add_pre_to_semax Delta Q) l5) x) ->
    add_post_to_semax Delta
      (EX Q: assert,
             Q &&
             !! (Forall (atom_to_semax Delta Q R1) l1 /\
                 Forall (atom_to_semax Delta Q R2) l2 /\
                 Forall (atom_to_semax Delta Q R3) l3 /\
                 Forall (atom_return_to_semax Delta Q R4) l4 /\
                 Forall (add_pre_to_semax Delta Q) l5)) x.
Proof.
  intros.
  destruct l1,l2,l3,l4,l5;
  try specialize (H0 nil_cons);
    try specialize (H1 nil_cons);
      try specialize (H2 nil_cons);
        try specialize (H3 nil_cons);
        try specialize (H4 nil_cons);
        [exfalso; apply H; repeat split;auto|..];
        combine_aux_post_auto.
Qed.



Lemma soundness_seq_inv_aux2:  forall l1 l2 l3 l4 l5 R1 R2 R3 R4 P x ,
  ~ (l1 = [] /\ l2 = [] /\ l3 = [] /\ l4 = [] /\ l5 = []) ->
  (l1 <> [] -> atom_to_semax Delta P  (EX Q : assert, Q &&
                                           !! Forall (atom_to_semax Delta Q R1) l1) x) ->
  (l2 <> [] -> atom_to_semax Delta P (EX Q : assert, Q &&
                                           !! Forall (atom_to_semax Delta Q R2) l2) x) ->
  (l3 <> [] -> atom_to_semax Delta P (EX Q : assert, Q &&
                                           !! Forall (atom_to_semax Delta Q R3) l3) x) ->
  (l4 <> [] -> atom_to_semax Delta P (EX Q : assert, Q &&
                                    !! Forall (atom_return_to_semax Delta Q R4) l4) x) ->
   (l5 <> [] ->atom_to_semax Delta P (EX Q : assert, Q &&
                                         !! Forall (add_pre_to_semax Delta Q) l5) x) ->
    atom_to_semax Delta P
      (EX Q: assert,
             Q &&
             !! (Forall (atom_to_semax Delta Q R1) l1 /\
                 Forall (atom_to_semax Delta Q R2) l2 /\
                 Forall (atom_to_semax Delta Q R3) l3 /\
                 Forall (atom_return_to_semax Delta Q R4) l4 /\
                 Forall (add_pre_to_semax Delta Q) l5)) x.
Proof.
  intros.
  destruct l1,l2,l3,l4,l5;
  try specialize (H0 nil_cons);
    try specialize (H1 nil_cons);
      try specialize (H2 nil_cons);
        try specialize (H3 nil_cons);
        try specialize (H4 nil_cons);
        [exfalso; apply H; repeat split;auto|..];
        combine_aux_atom_auto.
Qed. 

Lemma soundness_seq_inv_aux3:  forall l1 l2 l3 l4 l5 R1 R2 R3 R4 P x ,
  ~ (l1 = [] /\ l2 = [] /\ l3 = [] /\ l4 = [] /\ l5 = []) ->
  (l1 <> [] -> atom_to_semax Delta P  (EX Q : assert, Q &&
                                           !! Forall (atom_to_semax Delta Q R1) l1) x) ->
  (l2 <> [] -> atom_to_semax Delta P (EX Q : assert, Q &&
                                           !! Forall (atom_to_semax Delta Q R2) l2) x) ->
  (l3 <> [] -> atom_to_semax Delta P (EX Q : assert, Q &&
                                           !! Forall (atom_to_semax Delta Q R3) l3) x) ->
  (l4 <> [] -> atom_to_semax Delta P (EX Q : assert, Q &&
                                    !! Forall (atom_return_to_semax Delta Q R4) l4) x) ->
   (l5 <> [] ->atom_to_semax Delta P (EX Q : assert, Q &&
                                         !! Forall (add_pre_to_semax Delta Q) l5) x) ->
    atom_to_semax Delta P
      (EX Q: assert,
             Q &&
             !! (Forall (atom_to_semax Delta Q R1) l1 /\
                 Forall (atom_to_semax Delta Q R2) l2 /\
                 Forall (atom_to_semax Delta Q R3) l3 /\
                 Forall (atom_return_to_semax Delta Q R4) l4 /\
                 Forall (add_pre_to_semax Delta Q) l5)) x.
Proof.
  intros.
  destruct l1,l2,l3,l4,l5;
  try specialize (H0 nil_cons);
    try specialize (H1 nil_cons);
      try specialize (H2 nil_cons);
        try specialize (H3 nil_cons);
        try specialize (H4 nil_cons);
        [exfalso; apply H; repeat split;auto|..];
        combine_aux_atom_auto.
Qed. 

Lemma soundness_null_aux1_1:  forall l1 l2 l3 l4 R1 R2 x,
  ~ (l1 = [] /\ l2 = [] /\ l3 = [] /\ l4 = [] ) ->
   (l1 <> [] -> add_post_to_semax Delta (EX Q : assert, Q &&
                                    !! Forall (add_pre_to_semax Delta Q) l1) x) ->
   (l2 <> [] -> add_post_to_semax Delta (EX Q : assert, Q &&
                                    !! Forall (add_pre_to_semax Delta Q) l2) x) ->
  (l3 <> [] -> add_post_to_semax Delta (EX Q : assert, Q &&
                                    !! Forall (atom_to_semax Delta Q R1) l3) x) ->
  (l4 <> [] -> add_post_to_semax Delta (EX Q : assert, Q &&
                                    !! Forall (atom_return_to_semax Delta Q R2) l4) x) ->
    add_post_to_semax Delta
      (EX Q: assert,
             Q &&
             !! (Forall (add_pre_to_semax Delta Q) l1 /\
                 Forall (add_pre_to_semax Delta Q) l2 /\
                 Forall (atom_return_to_semax Delta Q R2) l4/\
                 Forall (atom_to_semax Delta Q R1) l3 
                )
       ) x.
Proof.
  intros.
  destruct l1,l2,l3,l4;
  try specialize (H0 nil_cons);
    try specialize (H1 nil_cons);
      try specialize (H2 nil_cons);
        try specialize (H3 nil_cons);
        [exfalso; apply H; repeat split;auto|..];
        combine_aux_post_auto.
Qed.

Lemma soundness_null_aux1_2:  forall l5 l6 R1 R2 x,
  ~ (l5 = [] /\ l6 = []  ) ->
  (l5 <> [] -> add_post_to_semax Delta (EX Q : assert, Q &&
                                    !! Forall (atom_to_semax Delta Q R1) l5) x) ->
  (l6 <> [] -> add_post_to_semax Delta (EX Q : assert, Q &&
                                    !! Forall (atom_return_to_semax Delta Q R2) l6) x) ->
    add_post_to_semax Delta
      (EX Q: assert,
             Q &&
             !! (
              Forall (atom_to_semax Delta Q R1) l5 /\
              Forall (atom_return_to_semax Delta Q R2) l6
                )
       ) x.
Proof.
  intros.
  destruct l5,l6;
  try specialize (H0 nil_cons);
    try specialize (H1 nil_cons);
        [exfalso; apply H; repeat split;auto|..];
        combine_aux_post_auto.
Qed.

Lemma soundness_null_aux1 : forall l1 l2 l3 l4 l5 l6 R1 R2 R3 R4 x,
 ~ (l1 = [] /\ l2 = [] /\ l3 = [] /\ l4 = [] /\ l5 = [] /\ l6 = [] ) ->
   (l1 <> [] -> add_post_to_semax Delta (EX Q : assert, Q &&
                                    !! Forall (add_pre_to_semax Delta Q) l1) x) ->
   (l2 <> [] -> add_post_to_semax Delta (EX Q : assert, Q &&
                                    !! Forall (add_pre_to_semax Delta Q) l2) x) ->
  (l3 <> [] -> add_post_to_semax Delta (EX Q : assert, Q &&
                                    !! Forall (atom_to_semax Delta Q R1) l3) x) ->
  (l4 <> [] -> add_post_to_semax Delta (EX Q : assert, Q &&
                                    !! Forall (atom_return_to_semax Delta Q R2) l4) x) ->
  (l5 <> [] -> add_post_to_semax Delta (EX Q : assert, Q &&
                                    !! Forall (atom_to_semax Delta Q R3) l5) x) ->
  (l6 <> [] -> add_post_to_semax Delta (EX Q : assert, Q &&
                                    !! Forall (atom_return_to_semax Delta Q R4) l6) x) ->
    add_post_to_semax Delta
      (EX Q: assert,
             Q &&
             !! (Forall (add_pre_to_semax Delta Q) l1 /\
                 Forall (add_pre_to_semax Delta Q) l2 /\
                 Forall (atom_return_to_semax Delta Q R2) l4/\
                 Forall (atom_to_semax Delta Q R1) l3 /\
                 Forall (atom_to_semax Delta Q R3) l5 /\
                 Forall (atom_return_to_semax Delta Q R4) l6
                )
       ) x.
Proof.
  intros.
  pose proof soundness_null_aux1_1 as T1.
  pose proof soundness_null_aux1_2 as T2.
  assert (~ (l1 = [] /\ l2 = [] /\ l3 = [] /\ l4 = [] /\ l5 = [] /\ l6 = [] ) ->
        ((~((l1 = [] /\ l2 = [] /\ l3 = [] /\ l4 = [] ))) \/ (~(l5 = []/\l6 = [] )))
        ) .
  { intros HP. apply Classical_Prop.not_and_or. intro.  apply H. repeat econstructor;auto;apply H6. }
  apply H6 in H. clear H6.        
    assert (Ept1 :(l1 = [] /\ l2 = [] /\ l3 = [] /\ l4 = []) \/ ~ (l1 = [] /\ l2 = [] /\ l3 = [] /\ l4 = [])). 
  { apply Classical_Prop.classic. }
  assert (Ept2: (l5 = [] /\ l6 = [] ) \/ ~ (l5 = []  /\ l6 = [] ) ).
  { apply Classical_Prop.classic. }
  destruct Ept1,Ept2.
  - exfalso. inv H;apply H8;auto.
  - apply T2 with(R1:= R3)(R2:= R4)(x:=x) in H7;eauto.
    destruct H6 as (S1&S2&S3&S4). subst. 
    eapply add_post_to_semax_derives. 2:{ apply H7. } Intros Q. Exists Q. 
    apply andp_right. 
    solve_andp. apply prop_right. repeat split;try apply Forall_nil; auto.
  - apply T1 with(R1:= R1)(R2:=R2)(x:=x) in H6;eauto.
    destruct H7 as (S1&S2). subst. 
    eapply add_post_to_semax_derives. 2:{ apply H6. } Intros Q. Exists Q. 
    apply andp_right. 
    solve_andp. apply prop_right. repeat split;try apply Forall_nil; auto.
  - apply T2 with(R1:= R3)(R2:= R4)(x:=x) in H7;eauto.   
    apply T1 with(R1:= R1)(R2:= R2)(x:=x) in H6;eauto.
    eapply add_post_to_semax_derives. 2:{ apply add_post_to_semax_conj_rule. apply H6. apply H7. }
     Intros Q1 Q2. Exists (Q1 && Q2). 
      assert ( G : Q1&& Q2 |-- Q1). { apply andp_left1. apply derives_refl. } 
      assert ( G' : Q1&& Q2 |-- Q2). { apply andp_left2. apply derives_refl. } 
    apply andp_right.       
    solve_andp. apply prop_right. repeat split; auto;apply Forall_forall;intros.
 
    apply add_pre_to_semax_derives with (P:=Q1) ;try apply G;rewrite Forall_forall in H8;try solve_andp; apply H8; auto.
    apply add_pre_to_semax_derives with (P:=Q1) ;try apply G;rewrite Forall_forall in H9;try solve_andp; apply H9; auto.
    apply atom_return_to_semax_derives_pre with (P1:=Q1&&Q2)(P2:=Q1);try apply G; rewrite Forall_forall in H10;try solve_andp; try apply H10; auto.
    apply atom_to_semax_derives_pre with (P2:=Q1); try apply G. rewrite Forall_forall in H11;try solve_andp; try apply H11; auto.
    apply atom_to_semax_derives_pre with (P2:=Q2) ;try apply G';rewrite Forall_forall in H12;try solve_andp; try apply H12; auto.
    apply atom_return_to_semax_derives_pre with (P1:=Q1&&Q2)(P2:=Q2);try apply G'; rewrite Forall_forall in H13; try  apply H13; auto.
Qed. 
  

Lemma soundness_null_aux2_1:  forall l1 l2 l3 l4  R1 R2 P x ,
  ~ (l1 = [] /\ l2 = [] /\ l3 = [] /\ l4 = [] ) ->
  
  (l1 <> [] -> atom_to_semax Delta P (EX Q : assert, Q &&
                                           !! Forall (atom_to_semax Delta Q R1) l1) x) ->
  (l2 <> [] -> atom_to_semax Delta P (EX Q : assert, Q &&
                                          !! Forall (atom_return_to_semax Delta Q R2) l2) x) ->
   (l3 <> [] ->atom_to_semax Delta P (EX Q : assert, Q &&
                                         !! Forall (add_pre_to_semax Delta Q) l3) x) ->
  (l4 <> [] ->atom_to_semax Delta P (EX Q : assert, Q &&
                                          !! Forall (add_pre_to_semax Delta Q) l4) x) ->
    atom_to_semax Delta P
      (EX Q: assert,
             Q &&
             !! (
                 Forall (add_pre_to_semax Delta Q ) l3 /\
                 Forall (add_pre_to_semax Delta Q ) l4 /\
                 Forall (atom_return_to_semax Delta Q R2) l2 /\
                 Forall (atom_to_semax Delta Q R1) l1 
                 )) x.
Proof.
  intros.
  destruct l1,l2,l3,l4;
  try specialize (H0 nil_cons);
    try specialize (H1 nil_cons);
      try specialize (H2 nil_cons);
        try specialize (H3 nil_cons);
        try specialize (H4 nil_cons);
        [exfalso; apply H; repeat split;auto|..];
        combine_aux_atom_auto.
Qed. 

Lemma soundness_null_aux2_2:  forall l5 l6 R3 R4 P x ,
  ~ (l5 = [] /\ l6 = [] ) ->
  (l5 <> [] -> atom_to_semax Delta P (EX Q : assert, Q &&
                                           !! Forall (atom_to_semax Delta Q R3) l5) x) ->
  (l6 <> [] -> atom_to_semax Delta P (EX Q : assert, Q &&
                                          !! Forall (atom_return_to_semax Delta Q R4) l6) x) ->

    atom_to_semax Delta P
      (EX Q: assert,
             Q &&
             !! (
                 Forall (atom_to_semax Delta Q R3) l5/\ 
                 Forall (atom_return_to_semax Delta Q R4) l6 
                 
                 )) x.
Proof.
  intros.
  destruct l5,l6;
  try specialize (H0 nil_cons);
    try specialize (H1 nil_cons);
        [exfalso; apply H; repeat split;auto|..];
        combine_aux_atom_auto.
Qed.

Lemma soundness_null_aux2:  forall l1 l2 l3 l4 l5 l6 R1 R2 R3 R4 P x ,
  ~ (l1 = [] /\ l2 = [] /\ l3 = [] /\ l4 = [] /\ l5 = [] /\ l6 = [] ) ->
  
  (l1 <> [] -> atom_to_semax Delta P (EX Q : assert, Q &&
                                           !! Forall (atom_to_semax Delta Q R1) l1) x) ->
  (l2 <> [] -> atom_to_semax Delta P (EX Q : assert, Q &&
                                          !! Forall (atom_return_to_semax Delta Q R2) l2) x) ->
  (l3 <> [] ->atom_to_semax Delta P (EX Q : assert, Q &&
                                         !! Forall (add_pre_to_semax Delta Q) l3) x) ->
  (l4 <> [] ->atom_to_semax Delta P (EX Q : assert, Q &&
                                          !! Forall (add_pre_to_semax Delta Q) l4) x) ->
  (l5 <> [] -> atom_to_semax Delta P (EX Q : assert, Q &&
                                           !! Forall (atom_to_semax Delta Q R3) l5) x) ->
  (l6 <> [] -> atom_to_semax Delta P (EX Q : assert, Q &&
                                          !! Forall (atom_return_to_semax Delta Q R4) l6) x) ->
    atom_to_semax Delta P
      (EX Q: assert,
             Q &&
             !! (
                 Forall (add_pre_to_semax Delta Q ) l3 /\
                 Forall (add_pre_to_semax Delta Q ) l4 /\
                 Forall (atom_return_to_semax Delta Q R2) l2 /\
                 Forall (atom_to_semax Delta Q R1) l1 /\
                 Forall (atom_to_semax Delta Q R3) l5/\ 
                 Forall (atom_return_to_semax Delta Q R4) l6 
                 )) x.
Proof.
intros.
  pose proof soundness_null_aux2_1 as T1.
  pose proof soundness_null_aux2_2 as T2.
  assert (~ (l1 = [] /\ l2 = [] /\ l3 = [] /\ l4 = [] /\ l5 = [] /\ l6 = [] ) ->
        ((~((l1 = [] /\ l2 = [] /\ l3 = [] /\ l4 = [] ))) \/ (~(l5 = []/\l6 = [] )))
        ) .
  { intros HP. apply Classical_Prop.not_and_or. intro.  apply H. repeat econstructor;auto;apply H6. }
  apply H6 in H. clear H6.        
    assert (Ept1 :(l1 = [] /\ l2 = [] /\ l3 = [] /\ l4 = []) \/ ~ (l1 = [] /\ l2 = [] /\ l3 = [] /\ l4 = [])). 
  { apply Classical_Prop.classic. }
  assert (Ept2: (l5 = [] /\ l6 = [] ) \/ ~ (l5 = []  /\ l6 = [] ) ).
  { apply Classical_Prop.classic. }
  destruct Ept1,Ept2.
  - exfalso. inv H;apply H8;auto.
  - apply T2 with(R3:= R3)(R4:= R4)(x:=x)(P:=P) in H7;eauto.
    destruct H6 as (S1&S2&S3&S4). subst. 
    eapply atom_to_semax_derives. apply derives_refl. 2:{ apply H7. } Intros Q. Exists Q. 
    apply andp_right. 
    solve_andp. apply prop_right. repeat split;try apply Forall_nil; auto.
  - apply T1 with(R1:= R1)(R2:=R2)(x:=x)(P:=P) in H6;eauto.
    destruct H7 as (S1&S2). subst. 
    eapply atom_to_semax_derives. apply derives_refl. 2:{ apply H6. } Intros Q. Exists Q. 
    apply andp_right. 
    solve_andp. apply prop_right. repeat split;try apply Forall_nil; auto.
  - apply T2 with(R3:= R3)(R4:= R4)(x:=x)(P:=P) in H7;eauto.   
    apply T1 with(R1:= R1)(R2:= R2)(x:=x)(P:=P) in H6;eauto.
    eapply atom_to_semax_derives. apply derives_refl. 2:{ apply atom_to_semax_conj_rule. apply H6. apply H7. }
     Intros Q1 Q2. Exists (Q1 && Q2). 
      assert ( G : Q1&& Q2 |-- Q1). { apply andp_left1. apply derives_refl. } 
      assert ( G' : Q1&& Q2 |-- Q2). { apply andp_left2. apply derives_refl. } 
    apply andp_right.       
    solve_andp. apply prop_right. repeat split; auto;apply Forall_forall;intros.
    apply add_pre_to_semax_derives with (P0:=Q1) ;try apply G;rewrite Forall_forall in H8;try solve_andp; apply H8; auto.
    apply add_pre_to_semax_derives with (P0:=Q1) ;try apply G;rewrite Forall_forall in H9;try solve_andp; apply H9; auto.
    apply atom_return_to_semax_derives_pre with (P1:=Q1&&Q2)(P2:=Q1);try apply G; rewrite Forall_forall in H10; try apply H10; auto.
    apply atom_to_semax_derives_pre with (P2:=Q1); try apply G. rewrite Forall_forall in H11; try apply H11; auto.
    apply atom_to_semax_derives_pre with (P2:=Q2) ;try apply G';rewrite Forall_forall in H12; try apply H12; auto.
    apply atom_return_to_semax_derives_pre with (P1:=Q1&&Q2)(P2:=Q2);try apply G'; rewrite Forall_forall in H13; try  apply H13; auto.
Qed.  


Lemma soundness_null_aux3_1:  forall l1 l2 l3 l4 R1  x,
  ~ (l1 = [] /\ l2 = [] /\ l3 = [] /\ l4 = []  ) ->
   (l1 <> [] -> add_post_to_semax Delta (EX Q : assert, Q &&
                                    !! Forall (add_pre_to_semax Delta Q) l1) x) ->
   (l2 <> [] -> add_post_to_semax Delta (EX Q : assert, Q &&
                                    !! Forall (add_pre_to_semax Delta Q) l2) x) ->
   (l3 <> [] -> add_post_to_semax Delta (EX Q : assert, Q &&
                                    !! Forall (add_pre_to_semax Delta Q) l3) x) ->
   (l4 <> [] -> add_post_to_semax Delta (EX Q : assert, Q &&
                                    !! Forall (atom_return_to_semax Delta Q R1) l4) x) ->

    add_post_to_semax Delta
      (EX Q: assert,
             Q &&
             !! (Forall (add_pre_to_semax Delta Q) l1 /\
                 Forall (add_pre_to_semax Delta Q) l2 /\
                 Forall (add_pre_to_semax Delta Q) l3 /\
                 Forall (atom_return_to_semax Delta Q R1) l4

                )
       ) x.
Proof.
  intros.
  destruct l1,l2,l3,l4;
  try specialize (H0 nil_cons);
    try specialize (H1 nil_cons);
      try specialize (H2 nil_cons);
        try specialize (H3 nil_cons);
        try specialize (H4 nil_cons);
        [exfalso; apply H; repeat split;auto|..];
        combine_aux_post_auto.
Qed.
 

Lemma soundness_null_aux3_2: forall l5 l6 l7 l8 l9 R2 R3 R4 R5 R6 x,
~ (l5 = []/\l6 = [] /\ l7 = [] /\ l8 = [] /\l9 = [] )->
  (l5 <> [] -> add_post_to_semax Delta (EX Q : assert, Q &&
                                    !! Forall (atom_to_semax Delta Q R2) l5) x) ->
  (l6 <> [] -> add_post_to_semax Delta (EX Q : assert, Q &&
                                    !! Forall (atom_to_semax Delta Q R3) l6) x) ->
  (l7 <> [] -> add_post_to_semax Delta (EX Q : assert, Q &&
                                    !! Forall (atom_to_semax Delta Q R4) l7) x) ->
  (l8 <> [] -> add_post_to_semax Delta (EX Q : assert, Q &&
                                  !! Forall (atom_return_to_semax Delta Q R5) l8) x) ->
  (l9 <> [] -> add_post_to_semax Delta (EX Q : assert, Q &&
                                  !! Forall (atom_return_to_semax Delta Q R6) l9) x) ->
add_post_to_semax Delta
      (EX Q: assert,
             Q &&
             !! (
                 Forall (atom_to_semax Delta Q R2) l5 /\
                 Forall (atom_to_semax Delta Q R3) l6 /\
                 Forall (atom_to_semax Delta Q R4) l7 /\
                 Forall (atom_return_to_semax Delta Q R5) l8/\
                 Forall (atom_return_to_semax Delta Q R6) l9
                )
       ) x.
Proof.
  intros.
  destruct l5,l6,l7,l8,l9;
  try specialize (H0 nil_cons);
    try specialize (H1 nil_cons);
      try specialize (H2 nil_cons);
        try specialize (H3 nil_cons);
        try specialize (H4 nil_cons);
        [exfalso; apply H; repeat split;auto|..];
        combine_aux_post_auto.
Qed.

(* Lemma soundness_null_aux3_3:  forall (A:Type)(l1 l2 l3 l4 l5 l6 l7 l8 l9 :list A),
~(l1 = [] /\ l2 = [] /\ l3 = [] /\ l4 = [] /\l5 = [] /\ l6 = [] /\ l7 = [] /\ l8 = [] /\l9 = [] ) <->
~(l1 = [] /\ l2 = [] /\ l3 = [] /\ l4 = [] /\l5 = []) \/ ~(l6 = [] /\ l7 = [] /\ l8 = [] /\l9 = []).
Proof.
split.
- intros. apply Classical_Prop.not_and_or. intro.  apply H. repeat econstructor;auto;apply H0.
- intros. destruct H;intro;destruct H0 as (S1&S2&S3&S4&S5&S6&S7&S8&S9);subst;apply H;eauto.
Qed.  *)

Lemma soundness_null_aux3:  forall l1 l2 l3 l4 l5 l6 l7 l8 l9 R1 R2 R3 R4 R5 R6 x,
  ~ (l1 = [] /\ l2 = [] /\ l3 = [] /\ l4 = [] /\l5 = [] /\ l6 = [] /\ l7 = [] /\ l8 = [] /\l9 = [] ) ->
   (l1 <> [] -> add_post_to_semax Delta (EX Q : assert, Q &&
                                    !! Forall (add_pre_to_semax Delta Q) l1) x) ->
   (l2 <> [] -> add_post_to_semax Delta (EX Q : assert, Q &&
                                    !! Forall (add_pre_to_semax Delta Q) l2) x) ->
   (l3 <> [] -> add_post_to_semax Delta (EX Q : assert, Q &&
                                    !! Forall (add_pre_to_semax Delta Q) l3) x) ->
   (l4 <> [] -> add_post_to_semax Delta (EX Q : assert, Q &&
                                    !! Forall (atom_return_to_semax Delta Q R1) l4) x) ->
  (l5 <> [] -> add_post_to_semax Delta (EX Q : assert, Q &&
                                    !! Forall (atom_to_semax Delta Q R2) l5) x) ->
  (l6 <> [] -> add_post_to_semax Delta (EX Q : assert, Q &&
                                    !! Forall (atom_to_semax Delta Q R3) l6) x) ->
  (l7 <> [] -> add_post_to_semax Delta (EX Q : assert, Q &&
                                    !! Forall (atom_to_semax Delta Q R4) l7) x) ->
  (l8 <> [] -> add_post_to_semax Delta (EX Q : assert, Q &&
                                  !! Forall (atom_return_to_semax Delta Q R5) l8) x) ->
  (l9 <> [] -> add_post_to_semax Delta (EX Q : assert, Q &&
                                  !! Forall (atom_return_to_semax Delta Q R6) l9) x) ->
    add_post_to_semax Delta
      (EX Q: assert,
             Q &&
             !! (Forall (add_pre_to_semax Delta Q) l1 /\
                 Forall (add_pre_to_semax Delta Q) l2 /\
                 Forall (add_pre_to_semax Delta Q) l3 /\
                 Forall (atom_return_to_semax Delta Q R1) l4/\
                 Forall (atom_to_semax Delta Q R2) l5 /\
                 Forall (atom_to_semax Delta Q R3) l6 /\
                 Forall (atom_to_semax Delta Q R4) l7 /\
                 Forall (atom_return_to_semax Delta Q R5) l8/\
                 Forall (atom_return_to_semax Delta Q R6) l9
                )
       ) x.
Proof.
  intros.
  pose proof soundness_null_aux3_1 as T1.
  pose proof soundness_null_aux3_2 as T2.
  assert (~ (l1 = [] /\ l2 = [] /\ l3 = [] /\ l4 = [] /\ l5 = [] /\ l6 = [] /\ l7 = [] /\ l8 = [] /\ l9 = []) ->
        ((~((l1 = [] /\ l2 = [] /\ l3 = [] /\ l4 = [] ))) \/ (~(l5 = []/\l6 = [] /\ l7 = [] /\ l8 = [] /\ l9 = [])))
        ) .

  {intros HP. apply Classical_Prop.not_and_or. intro.  apply H. repeat econstructor;auto;apply H9. }
  apply H9 in H. clear H9.  
  assert (Ept1 :(l1 = [] /\ l2 = [] /\ l3 = [] /\ l4 = []) \/ ~ (l1 = [] /\ l2 = [] /\ l3 = [] /\ l4 = [])). 
  { apply Classical_Prop.classic. }
  assert (Ept2: (l5 = [] /\ l6 = [] /\ l7 = [] /\ l8 = [] /\ l9 = []) \/ ~ ((l5 = [] /\ l6 = [] /\ l7 = [] /\ l8 = [] /\ l9 = []) )).
  { apply Classical_Prop.classic. }
  destruct Ept1,Ept2.
  - exfalso. inv H;apply H11;auto.
  - apply T2 with(R2:= R2)(R3:= R3)(R4:= R4)(R5:= R5)(R6:= R6)(x:=x) in H10;eauto.
    destruct H9 as (S1&S2&S3&S4). subst. 
    eapply add_post_to_semax_derives. 2:{ apply H10. } Intros Q. Exists Q. 
    apply andp_right. 
    solve_andp. apply prop_right. repeat split;try apply Forall_nil; auto.
  - apply T1 with(R1:= R1)(x:=x) in H9;eauto.
    destruct H10 as (S1&S2&S3&S4&S5). subst. 
    eapply add_post_to_semax_derives. 2:{ apply H9. } Intros Q. Exists Q. 
    apply andp_right. 
    solve_andp. apply prop_right. repeat split;try apply Forall_nil; auto.
  - apply T2 with(R2:= R2)(R3:= R3)(R4:= R4)(R5:= R5)(R6:= R6)(x:=x) in H10;eauto.   
    apply T1 with(R1:= R1)(x:=x) in H9;eauto.
    eapply add_post_to_semax_derives. 2:{ apply add_post_to_semax_conj_rule. apply H9. apply H10. }
     Intros Q1 Q2. Exists (Q1 && Q2). 
      assert ( G : Q1&& Q2 |-- Q1). { apply andp_left1. apply derives_refl. } 
      assert ( G' : Q1&& Q2 |-- Q2). { apply andp_left2. apply derives_refl. } 
    apply andp_right.       
    solve_andp. apply prop_right. repeat split; auto;apply Forall_forall;intros.
 
    apply add_pre_to_semax_derives with (P:=Q1) ;try apply G;rewrite Forall_forall in H11;try solve_andp; apply H11; auto.
    apply add_pre_to_semax_derives with (P:=Q1) ;try apply G;rewrite Forall_forall in H12; try solve_andp;apply H12; auto.
    apply add_pre_to_semax_derives with (P:=Q1) ;try apply G;rewrite Forall_forall in H13;try solve_andp; apply H13; auto.
    apply atom_return_to_semax_derives_pre with (P1:=Q1&&Q2)(P2:=Q1);try apply G; rewrite Forall_forall in H14; try  apply H14; auto.
    apply atom_to_semax_derives_pre with (P2:=Q2) ;try apply G';rewrite Forall_forall in H15; try apply H15; auto.
    apply atom_to_semax_derives_pre with (P2:=Q2) ;try apply G';rewrite Forall_forall in H16; try apply H16; auto.
    apply atom_to_semax_derives_pre with (P2:=Q2) ;try apply G';rewrite Forall_forall in H17; try apply H17; auto.
    apply atom_return_to_semax_derives_pre with (P1:=Q1&&Q2)(P2:=Q2);try apply G'; rewrite Forall_forall in H18; try  apply H18; auto.
    apply atom_return_to_semax_derives_pre with (P1:=Q1&&Q2)(P2:=Q2);try apply G'; rewrite Forall_forall in H19; try  apply H19; auto.

Qed. 
  
Lemma soundness_null_aux4_1:  forall l1 l2 l3 l4  R1 P x ,
  ~ (l1 = [] /\ l2 = [] /\ l3 = [] /\ l4 = [] ) ->
  
  (l1 <> [] -> atom_to_semax Delta P (EX Q : assert, Q &&
                                           !! Forall (add_pre_to_semax Delta Q) l1) x) ->
  (l2 <> [] -> atom_to_semax Delta P (EX Q : assert, Q &&
                                          !! Forall (add_pre_to_semax Delta Q) l2) x) ->
   (l3 <> [] ->atom_to_semax Delta P (EX Q : assert, Q &&
                                         !! Forall (add_pre_to_semax Delta Q) l3) x) ->
  (l4 <> [] ->atom_to_semax Delta P (EX Q : assert, Q &&
                                          !! Forall (atom_return_to_semax Delta Q R1) l4) x) ->
                                           
    atom_to_semax Delta P
      (EX Q: assert,
             Q &&
             !! (Forall (add_pre_to_semax Delta Q) l1 /\
                 Forall (add_pre_to_semax Delta Q) l2 /\
                 Forall (add_pre_to_semax Delta Q) l3 /\
                 Forall (atom_return_to_semax Delta Q R1) l4

                )
       ) x.
Proof.
  intros.
  destruct l1,l2,l3,l4;
  try specialize (H0 nil_cons);
    try specialize (H1 nil_cons);
      try specialize (H2 nil_cons);
        try specialize (H3 nil_cons);
        try specialize (H4 nil_cons);
        [exfalso; apply H; repeat split;auto|..];
        combine_aux_atom_auto.
Qed.

Lemma soundness_null_aux4_2: forall l5 l6 l7 l8 l9 R2 R3 R4 R5 R6 P x,
~ (l5 = []/\l6 = [] /\ l7 = [] /\ l8 = [] /\l9 = [] )->
  (l5 <> [] -> atom_to_semax Delta P (EX Q : assert, Q &&
                                    !! Forall (atom_to_semax Delta Q R2) l5) x) ->
  (l6 <> [] -> atom_to_semax Delta P (EX Q : assert, Q &&
                                    !! Forall (atom_to_semax Delta Q R3) l6) x) ->
  (l7 <> [] -> atom_to_semax Delta P (EX Q : assert, Q &&
                                    !! Forall (atom_to_semax Delta Q R4) l7) x) ->
  (l8 <> [] -> atom_to_semax Delta P (EX Q : assert, Q &&
                                  !! Forall (atom_return_to_semax Delta Q R5) l8) x) ->
  (l9 <> [] -> atom_to_semax Delta P (EX Q : assert, Q &&
                                  !! Forall (atom_return_to_semax Delta Q R6) l9) x) ->
atom_to_semax Delta P
      (EX Q: assert,
             Q &&
             !! (
                 Forall (atom_to_semax Delta Q R2) l5 /\
                 Forall (atom_to_semax Delta Q R3) l6 /\
                 Forall (atom_to_semax Delta Q R4) l7 /\
                 Forall (atom_return_to_semax Delta Q R5) l8/\
                 Forall (atom_return_to_semax Delta Q R6) l9
                )
       ) x.
Proof.
  intros.
  destruct l5,l6,l7,l8,l9;
  try specialize (H0 nil_cons);
    try specialize (H1 nil_cons);
      try specialize (H2 nil_cons);
        try specialize (H3 nil_cons);
        try specialize (H4 nil_cons);
        [exfalso; apply H; repeat split;auto|..];
        combine_aux_atom_auto.
Qed.

Lemma soundness_null_aux4: forall l1 l2 l3 l4 l5 l6 l7 l8 l9 R1 R2 R3 R4 R5 R6 P x,
  ~ (l1 = [] /\ l2 = [] /\ l3 = [] /\ l4 = [] /\l5 = [] /\ l6 = [] /\ l7 = [] /\ l8 = [] /\l9 = [] ) ->
   (l1 <> [] -> atom_to_semax Delta P (EX Q : assert, Q &&
                                    !! Forall (add_pre_to_semax Delta Q) l1) x) ->
   (l2 <> [] -> atom_to_semax Delta P (EX Q : assert, Q &&
                                    !! Forall (add_pre_to_semax Delta Q) l2) x) ->
   (l3 <> [] -> atom_to_semax Delta P (EX Q : assert, Q &&
                                    !! Forall (add_pre_to_semax Delta Q) l3) x) ->
   (l4 <> [] -> atom_to_semax Delta P (EX Q : assert, Q &&
                                    !! Forall (atom_return_to_semax Delta Q R1) l4) x) ->
  (l5 <> [] -> atom_to_semax Delta P (EX Q : assert, Q &&
                                    !! Forall (atom_to_semax Delta Q R2) l5) x) ->
  (l6 <> [] -> atom_to_semax Delta P (EX Q : assert, Q &&
                                    !! Forall (atom_to_semax Delta Q R3) l6) x) ->
  (l7 <> [] -> atom_to_semax Delta P (EX Q : assert, Q &&
                                    !! Forall (atom_to_semax Delta Q R4) l7) x) ->
  (l8 <> [] -> atom_to_semax Delta P (EX Q : assert, Q &&
                                  !! Forall (atom_return_to_semax Delta Q R5) l8) x) ->
  (l9 <> [] -> atom_to_semax Delta P (EX Q : assert, Q &&
                                  !! Forall (atom_return_to_semax Delta Q R6) l9) x) ->
    atom_to_semax Delta P
      (EX Q: assert,
             Q &&
             !! (Forall (add_pre_to_semax Delta Q) l1 /\
                 Forall (add_pre_to_semax Delta Q) l2 /\
                 Forall (add_pre_to_semax Delta Q) l3 /\
                 Forall (atom_return_to_semax Delta Q R1) l4/\
                 Forall (atom_to_semax Delta Q R2) l5 /\
                 Forall (atom_to_semax Delta Q R3) l6 /\
                 Forall (atom_to_semax Delta Q R4) l7 /\
                 Forall (atom_return_to_semax Delta Q R5) l8/\
                 Forall (atom_return_to_semax Delta Q R6) l9
                )
       ) x.
Proof.
intros.
  pose proof soundness_null_aux4_1 as T1.
  pose proof soundness_null_aux4_2 as T2.
  assert (~ (l1 = [] /\ l2 = [] /\ l3 = [] /\ l4 = [] /\ l5 = [] /\ l6 = [] /\ l7 = [] /\ l8 = [] /\ l9 = []) ->
        ((~((l1 = [] /\ l2 = [] /\ l3 = [] /\ l4 = [] ))) \/ (~(l5 = []/\l6 = [] /\ l7 = [] /\ l8 = [] /\ l9 = [])))
        ) .

  {intros HP. apply Classical_Prop.not_and_or. intro.  apply H. repeat econstructor;auto;apply H9. }
  apply H9 in H. clear H9.  
  assert (Ept1 :(l1 = [] /\ l2 = [] /\ l3 = [] /\ l4 = []) \/ ~ (l1 = [] /\ l2 = [] /\ l3 = [] /\ l4 = [])). 
  { apply Classical_Prop.classic. }
  assert (Ept2: (l5 = [] /\ l6 = [] /\ l7 = [] /\ l8 = [] /\ l9 = []) \/ ~ ((l5 = [] /\ l6 = [] /\ l7 = [] /\ l8 = [] /\ l9 = []) )).
  { apply Classical_Prop.classic. }
  destruct Ept1,Ept2.
  - exfalso. inv H;apply H11;auto.
  - apply T2 with(R2:= R2)(R3:= R3)(R4:= R4)(R5:= R5)(R6:= R6)(x:=x)(P:=P) in H10;eauto.
    destruct H9 as (S1&S2&S3&S4); subst.
    eapply atom_to_semax_derives. apply derives_refl. 2:{  apply H10. } Intros Q. Exists Q. 
     apply andp_right. 
    solve_andp. apply prop_right. repeat split;try apply Forall_nil; auto.
  - destruct H10 as (S1&S2&S3&S4&S5);subst.
    apply T1 with (R1:= R1)(P:=P)(x:=x) in H9;eauto. 
    eapply atom_to_semax_derives. apply derives_refl. 2:{ apply H9. } Intros Q. Exists Q. 
    apply andp_right. 
    solve_andp. apply prop_right. repeat split;try apply Forall_nil; auto.
  - apply T2 with(R2:= R2)(R3:= R3)(R4:= R4)(R5:= R5)(R6:= R6)(x:=x)(P:=P) in H10;eauto.   
    apply T1 with(R1:= R1)(x:=x)(P:=P) in H9;eauto.
    eapply atom_to_semax_derives. apply derives_refl. 2:{ apply atom_to_semax_conj_rule. apply H9. apply H10. }
     Intros Q1 Q2. Exists (Q1 && Q2). 
      assert ( G : Q1&& Q2 |-- Q1). { apply andp_left1. apply derives_refl. } 
      assert ( G' : Q1&& Q2 |-- Q2). { apply andp_left2. apply derives_refl. } 
    apply andp_right.       
    solve_andp. apply prop_right. repeat split; auto;apply Forall_forall;intros.
 
    apply add_pre_to_semax_derives with (P0:=Q1) ;try apply G;rewrite Forall_forall in H11;try solve_andp; apply H11; auto.
    apply add_pre_to_semax_derives with (P0:=Q1) ;try apply G;rewrite Forall_forall in H12;try solve_andp; apply H12; auto.
    apply add_pre_to_semax_derives with (P0:=Q1) ;try apply G;rewrite Forall_forall in H13;try solve_andp; apply H13; auto.
    apply atom_return_to_semax_derives_pre with (P1:=Q1&&Q2)(P2:=Q1);try apply G; rewrite Forall_forall in H14; try  apply H14; auto.
    apply atom_to_semax_derives_pre with (P2:=Q2) ;try apply G';rewrite Forall_forall in H15; try apply H15; auto.
    apply atom_to_semax_derives_pre with (P2:=Q2) ;try apply G';rewrite Forall_forall in H16; try apply H16; auto.
    apply atom_to_semax_derives_pre with (P2:=Q2) ;try apply G';rewrite Forall_forall in H17; try apply H17; auto.
    apply atom_return_to_semax_derives_pre with (P1:=Q1&&Q2)(P2:=Q2);try apply G'; rewrite Forall_forall in H18; try  apply H18; auto.
    apply atom_return_to_semax_derives_pre with (P1:=Q1&&Q2)(P2:=Q2);try apply G'; rewrite Forall_forall in H19; try  apply H19; auto.

Qed. 
(*-------------------
Proofs for split_seq soundness
--------------------*)
Lemma atom_to_semax_sem: forall x  R,
 (atom_to_semax Delta 
        (EX Q : assert,
          !! (atom_to_semax Delta Q R x) && Q)) R
      x.
Proof.
  intros.
  apply aux_semax_extract_exists. intros Q.
  apply aux_semax_extract_prop.
  intros. auto.
Qed.

  
Lemma atom_return_to_semax_sem: forall x R,
 (atom_return_to_semax Delta 
        (EX Q : assert,
          !! (atom_return_to_semax Delta Q R x) && Q)) R
      x.
Proof.
  intros. destruct x as [p v].
  apply aux_semax_extract_exists. intros Q.
  apply aux_semax_extract_prop.
  intros. auto.
Qed.

(*-------------------
Proofs for split_if soundness
--------------------*)
Lemma typed_true_or_typed_false: forall a,
  bool_type (typeof a) = true ->
  ENTAIL Delta, (tc_expr Delta a)
  |-- (local (liftx (typed_true (typeof a)) (eval_expr a))) ||
  (local (liftx (typed_false (typeof a)) (eval_expr a))).
Proof.
  intros.
  unfold liftx. simpl. intros x.
  unfold lift. unfold local.
  unfold lift1.
  unfold typed_true, typed_false.
  Intros. unfold tc_environ in H0.
  pose proof typecheck_expr_sound _ _ a H0.
  eapply derives_trans.
  { apply andp_right. apply derives_refl.
    apply H1. }
  apply derives_extract_prop'. intros.
  eapply expr_lemmas.tc_bool_val with (v:= eval_expr a x) in H;auto.
  destruct (strict_bool_val (eval_expr a x) (typeof a)).
  { destruct b.
    - apply orp_right1. apply prop_right. auto.
    - apply orp_right2. apply prop_right. auto.
  }
  destruct H. inv H.
Qed.

Lemma typed_true_or_typed_false': forall a,
  bool_type (typeof a) = true ->
  ENTAIL Delta, (tc_expr Delta (Eunop Onotbool a (Tint I32 Signed noattr)))
  |-- (local (liftx (typed_true (typeof a)) (eval_expr a))) ||
  (local (liftx (typed_false (typeof a)) (eval_expr a))).
Proof.
  intros.
  unfold liftx. simpl. intros x.
  unfold lift. unfold local.
  unfold lift1.
  unfold typed_true, typed_false.
  Intros. unfold tc_environ in H0.
  pose proof typecheck_expr_sound _ _ a H0.
  eapply derives_trans.
  { apply andp_right. apply derives_refl.
    eapply derives_trans;[|apply H1].
    unfold tc_expr. simpl.
    rewrite denote_tc_assert_andp.
    rewrite andp_unfold. apply andp_left2.
    apply derives_refl.
  }
  apply derives_extract_prop'. intros.
  eapply expr_lemmas.tc_bool_val with (v:= eval_expr a x) in H;auto.
  destruct (strict_bool_val (eval_expr a x) (typeof a)).
  { destruct b.
    - apply orp_right1. apply prop_right. auto.
    - apply orp_right2. apply prop_right. auto.
  }
  destruct H. inv H.
Qed.

Lemma add_exp_to_pre_inv_strong: forall P  (a:expr) pre,
      add_pre_to_semax Delta P (add_exp_to_pre a pre) ->
       add_pre_to_semax Delta (P && (local
                                 (@liftx (Tarrow val (LiftEnviron Prop))
                                 (typed_true (typeof a)) (@eval_expr CS a)))
                        && tc_expr Delta (Eunop Onotbool a (Tint I32 Signed noattr))
                        && !! (bool_type (typeof a) = true )
                        )
                         pre .
Proof.
  intros.
  destruct pre as [a2 p2].
  simpl in H. induction a2.
  + rename H into H1. simpl in H1.
    eapply semax_aux_seq_inv in H1.
    destruct H1 as [Q [H1 H2]].
    unfold overridePost in H1.
    apply semax_aux_ifthenelse_inv in H1.
    eapply semax_aux_conseq with (R':={|
        RA_normal := a0;
        RA_break := FALSE;
        RA_continue := FALSE;
        RA_return := fun _ : option val => FALSE |}).
    { eapply derives_trans;[|apply H1]. simpl. intros.
      solve_andp.
    }
    { apply derives_aux_refl. }
    { apply derives_aux_refl. }
    { apply derives_aux_refl. }
    { intros. apply derives_aux_refl. }
    rewrite !andp_assoc.
    apply aux_semax_extract_prop. intros E3.
    rewrite andp_comm.
    rewrite !exp_andp1. apply aux_semax_extract_exists. intros R.
    rewrite andp_assoc.
    apply aux_semax_extract_prop. intros [E1 E2].
    rewrite andp_comm.
    eapply semax_aux_conseq;[..|apply H2].
    { apply semax_aux_skip_inv in E1. unfold RA_normal in E1.
      apply semax_aux_break_inv in E2. unfold RA_break in E2.
      eapply derives_trans.
      { simpl; intros. apply andp_right. apply derives_refl.
        rewrite andp_comm. rewrite andp_assoc. apply andp_left2.
        rewrite andp_comm. apply typed_true_or_typed_false' in E3.
        simpl in E3. specialize (E3 x).
        rewrite <- andp_assoc.  apply andp_left1. apply E3.
      }
      simpl. intros.
      rewrite andp_comm. rewrite distrib_orp_andp.
      simpl in E1,E2. specialize (E1 x). specialize (E2 x).
      apply orp_left.
      { eapply derives_trans;[|apply E1].
        solve_andp. }
      { eapply derives_trans with (Q0:=FALSE x).
        2:{ unfold FALSE. unfold PROPx. simpl.
            apply derives_extract_prop. intros. tauto. }
        eapply derives_trans;[|apply E2]. solve_andp. }
    }
    { apply derives_aux_refl. }
    { apply derives_aux_refl. }
    { apply derives_aux_refl. }
    { intros. apply derives_aux_refl. }
  + intros x. eapply H0.
    auto.
Qed.


Lemma add_exp_to_pre_inv: forall P  (a:expr) pre,
      add_pre_to_semax Delta P (add_exp_to_pre a pre) ->
       add_pre_to_semax Delta (P && (local
                                 (@liftx (Tarrow val (LiftEnviron Prop))
                                 (typed_true (typeof a)) (@eval_expr CS a)))
                        )
                         pre .
Proof.
  intros.
  destruct pre as [a2 p2].
  simpl in H. induction a2.
  + rename H into H1. simpl in H1.
    eapply semax_aux_seq_inv in H1.
    destruct H1 as [Q [H1 H2]].
    unfold overridePost in H1.
    apply semax_aux_ifthenelse_inv in H1.
    eapply semax_aux_conseq with (R':={|
        RA_normal := a0;
        RA_break := FALSE;
        RA_continue := FALSE;
        RA_return := fun _ : option val => FALSE |}).
    { eapply derives_trans;[|apply H1]. simpl. intros.
      solve_andp.
    }
    { apply derives_aux_refl. }
    { apply derives_aux_refl. }
    { apply derives_aux_refl. }
    { intros. apply derives_aux_refl. }
    rewrite !andp_assoc.
    apply aux_semax_extract_prop. intros E3.
    rewrite andp_comm.
    rewrite !exp_andp1. apply aux_semax_extract_exists. intros P'.
    rewrite andp_assoc.
    apply aux_semax_extract_prop. intros [E1 E2].
    rewrite andp_comm.
    eapply semax_aux_conseq;[..|apply H2].
    { apply semax_aux_skip_inv in E1. unfold RA_normal in E1.
      apply semax_aux_break_inv in E2. unfold RA_break in E2.
      eapply derives_trans.
      { simpl; intros. apply andp_right. apply derives_refl.
        rewrite andp_comm. rewrite andp_assoc. apply andp_left2.
        rewrite andp_comm. apply typed_true_or_typed_false' in E3.
        simpl in E3. specialize (E3 x).
        rewrite <- andp_assoc.  apply andp_left1. apply E3.
      }
      simpl. intros.
      rewrite andp_comm. rewrite distrib_orp_andp.
      simpl in E1,E2. specialize (E1 x). specialize (E2 x).
      apply orp_left.
      { eapply derives_trans;[|apply E1].
        rewrite <- andp_comm. rewrite andp_assoc.
        solve_andp. }
        { eapply derives_trans with (Q0:=FALSE x).
          2:{ unfold FALSE. unfold PROPx. simpl.
              apply derives_extract_prop. intros. tauto. }
          eapply derives_trans;[|apply E2]. solve_andp. }
    }
    { apply derives_aux_refl. }
    { apply derives_aux_refl. }
    { apply derives_aux_refl. }
    { intros. apply derives_aux_refl. }
  + intros x. eapply H0. auto.
Qed.


Lemma add_exp_to_pre_inv_false: forall P  (a:expr) pre,
      add_pre_to_semax Delta P (add_exp_to_pre (semax_lemmas.Cnot a) pre) ->
       add_pre_to_semax Delta (P && (local
                                 (@liftx (Tarrow val (LiftEnviron Prop))
                                 (typed_false (typeof a)) (@eval_expr CS a)))
                        )
                         pre .
Proof.
intros.
destruct pre as [a2 p2].
simpl in H. induction a2.
+ rename H into H1. simpl in H1.
  eapply semax_aux_seq_inv in H1.
  destruct H1 as [Q [H1 H2]].
  unfold overridePost in H1.
  apply semax_aux_ifthenelse_inv in H1.
  eapply semax_aux_conseq with (R':={|
      RA_normal := a0;
      RA_break := FALSE;
      RA_continue := FALSE;
      RA_return := fun _ : option val => FALSE |}).
  { eapply derives_trans;[|apply H1]. simpl. intros.
    solve_andp.
  }
  { apply derives_aux_refl. }
  { apply derives_aux_refl. }
  { apply derives_aux_refl. }
  { intros. apply derives_aux_refl. }
  rewrite !andp_assoc.
  apply aux_semax_extract_prop. intros E3.
  rewrite andp_comm.
  rewrite !exp_andp1. apply aux_semax_extract_exists. intros P'.
  rewrite andp_assoc.
  apply aux_semax_extract_prop. intros [E1 E2].
  rewrite andp_comm.
  eapply semax_aux_conseq;[..|apply H2].
  { apply semax_aux_skip_inv in E1. unfold RA_normal in E1.
    apply semax_aux_break_inv in E2. unfold RA_break in E2.
    eapply derives_trans.
    { simpl; intros. apply andp_right. apply derives_refl.
      rewrite andp_comm. rewrite andp_assoc. apply andp_left2.
      rewrite andp_comm. apply typed_true_or_typed_false' in E3.
      simpl in E3. specialize (E3 x).
      rewrite <- andp_assoc.  apply andp_left1. apply E3.
    }
    simpl. intros.
    rewrite andp_comm. rewrite distrib_orp_andp.
    simpl in E1,E2. specialize (E1 x). specialize (E2 x).
    apply orp_left.
    { eapply derives_trans;[|apply E1].
      solve_andp. }
    { eapply derives_trans with (Q0:=FALSE x).
      2:{ unfold FALSE. unfold PROPx. simpl.
          apply derives_extract_prop. intros. tauto. }
      eapply derives_trans;[|apply E2]. solve_andp. }
  }
  { apply derives_aux_refl. }
  { apply derives_aux_refl. }
  { apply derives_aux_refl. }
  { intros. apply derives_aux_refl. }
+ simpl. intros x. apply H0. auto.
Qed.

Lemma add_exp_to_atom_inv: forall P Q (a:expr) atom,
      atom_to_semax Delta P Q ((inl a)::atom) ->
       atom_to_semax Delta (P && (local
                                 (@liftx (Tarrow val (LiftEnviron Prop))
                                 (typed_true (typeof a)) (@eval_expr CS a)))
                        ) Q atom.
Proof.
  intros. rename H into H0.
  simpl in H0. 
  eapply semax_aux_seq_inv in H0.
  destruct H0 as [R [H1 H2]].
  unfold overridePost in H1.
  apply semax_aux_ifthenelse_inv in H1.
  eapply semax_aux_conseq with (R':={|
        RA_normal := Q;
        RA_break := FALSE;
        RA_continue := FALSE;
        RA_return := fun _ : option val => FALSE |}).
    { eapply derives_trans;[|apply H1]. simpl. intros.
      repeat apply andp_right.
      + apply andp_left1. apply derives_refl.
      + apply andp_left2. apply andp_left1. apply derives_refl.
      + apply andp_left2. apply andp_left2. apply andp_left1. apply derives_refl.
    }
    { apply derives_aux_refl. }
    { apply derives_aux_refl. }
    { apply derives_aux_refl. }
    { intros. apply derives_aux_refl. }
    rewrite !andp_assoc.
    apply aux_semax_extract_prop. intros E3.
    rewrite andp_comm.
    rewrite !exp_andp1. apply aux_semax_extract_exists. intros P'.
    rewrite andp_assoc.
    apply aux_semax_extract_prop. intros [E1 E2].
    rewrite andp_comm.
    eapply semax_aux_conseq;[..|apply H2].
    { apply semax_aux_skip_inv in E1. unfold RA_normal in E1.
      apply semax_aux_break_inv in E2. unfold RA_break in E2.
      eapply derives_trans.
      { simpl; intros. apply andp_right. apply derives_refl.
        rewrite andp_comm. rewrite andp_assoc. apply andp_left2.
        rewrite andp_comm. apply typed_true_or_typed_false' in E3.
        simpl in E3. specialize (E3 x).
        rewrite <- andp_assoc.  apply andp_left1. apply E3.
      }
      simpl. intros.
      rewrite andp_comm. rewrite distrib_orp_andp.
      simpl in E1,E2. specialize (E1 x). specialize (E2 x).
      apply orp_left.
      { eapply derives_trans;[|apply E1].
        solve_andp. }
      { eapply derives_trans with (Q0:=FALSE x).
        2:{ unfold FALSE. unfold PROPx. simpl.
            apply derives_extract_prop. intros. tauto. }
        eapply derives_trans;[|apply E2]. solve_andp. }
    }
    { apply derives_aux_refl. }
    { apply derives_aux_refl. }
    { apply derives_aux_refl. }
    { intros. apply derives_aux_refl. }
Qed.

Lemma add_exp_to_atom_inv_false: forall P Q (a:expr) atom,
      atom_to_semax Delta P Q ((inl (semax_lemmas.Cnot a))::atom) ->
       atom_to_semax Delta (P && (local
                                 (@liftx (Tarrow val (LiftEnviron Prop))
                                 (typed_false (typeof a)) (@eval_expr CS a)))
                        ) Q atom.
Proof.
  intros. rename H into H0.
  simpl in H0. 
  eapply semax_aux_seq_inv in H0.
  destruct H0 as [R [H1 H2]].
  unfold overridePost in H1.
  apply semax_aux_ifthenelse_inv in H1.
  eapply semax_aux_conseq with (R':={|
        RA_normal := Q;
        RA_break := FALSE;
        RA_continue := FALSE;
        RA_return := fun _ : option val => FALSE |}).
    { eapply derives_trans;[|apply H1]. simpl. intros.
      repeat apply andp_right.
      + apply andp_left1. apply derives_refl.
      + apply andp_left2. apply andp_left1. apply derives_refl.
      + apply andp_left2. apply andp_left2. apply andp_left1. apply derives_refl.
    }
    { apply derives_aux_refl. }
    { apply derives_aux_refl. }
    { apply derives_aux_refl. }
    { intros. apply derives_aux_refl. }
      rewrite !andp_assoc.
      apply aux_semax_extract_prop. intros E3.
      rewrite andp_comm.
      rewrite !exp_andp1. apply aux_semax_extract_exists. intros P'.
      rewrite andp_assoc.
      apply aux_semax_extract_prop. intros [E1 E2].
      rewrite andp_comm.
      eapply semax_aux_conseq;[..|apply H2].
      { apply semax_aux_skip_inv in E1. unfold RA_normal in E1.
        apply semax_aux_break_inv in E2. unfold RA_break in E2.
        eapply derives_trans.
        { simpl; intros. apply andp_right. apply derives_refl.
          rewrite andp_comm. rewrite andp_assoc. apply andp_left2.
          rewrite andp_comm. apply typed_true_or_typed_false' in E3.
          simpl in E3. specialize (E3 x).
          rewrite <- andp_assoc.  apply andp_left1. apply E3.
        }
        simpl. intros.
        rewrite andp_comm. rewrite distrib_orp_andp.
        simpl in E1,E2. specialize (E1 x). specialize (E2 x).
        apply orp_left.
        { eapply derives_trans;[|apply E1].
          solve_andp. }
        { eapply derives_trans with (Q0:=FALSE x).
          2:{ unfold FALSE. unfold PROPx. simpl.
              apply derives_extract_prop. intros. tauto. }
          eapply derives_trans;[|apply E2]. solve_andp. }
    }
    { apply derives_aux_refl. }
    { apply derives_aux_refl. }
    { apply derives_aux_refl. }
    { intros. apply derives_aux_refl. }
Qed.

Lemma add_exp_to_atom_inv': forall P Q (a:expr) atom,
      atom_to_semax Delta P Q ((inl a)::atom) ->
       atom_to_semax Delta (P && (local
                                 (@liftx (Tarrow val (LiftEnviron Prop))
                                 (typed_true (typeof a)) (@eval_expr CS a)))
                        && (!! (bool_type (typeof a) = true))
                        ) Q atom.
Proof.
  intros. rename H into H0. 
  eapply semax_aux_seq_inv in H0.
  destruct H0 as [R [H1 H2]].
  unfold overridePost in H1.
  apply semax_aux_ifthenelse_inv in H1.
  eapply semax_aux_conseq with (R':={|
        RA_normal := Q;
        RA_break := FALSE;
        RA_continue := FALSE;
        RA_return := fun _ : option val => FALSE |}).
    { eapply derives_trans;[|apply H1]. simpl. intros.
      repeat apply andp_right.
      + apply andp_left1. apply derives_refl.
      + apply andp_left2. apply andp_left1. apply derives_refl.
      + apply andp_left2. apply andp_left2. apply andp_left1.
        apply andp_left1. apply derives_refl.
    }
    { apply derives_aux_refl. }
    { apply derives_aux_refl. }
    { apply derives_aux_refl. }
    { intros. apply derives_aux_refl. }
    rewrite !andp_assoc.
  apply aux_semax_extract_prop. intros E3.
  rewrite andp_comm.
  rewrite !exp_andp1. apply aux_semax_extract_exists. intros P'.
  rewrite andp_assoc.
  apply aux_semax_extract_prop. intros [E1 E2].
  rewrite andp_comm.
  eapply semax_aux_conseq;[..|apply H2].
  { apply semax_aux_skip_inv in E1. unfold RA_normal in E1.
    apply semax_aux_break_inv in E2. unfold RA_break in E2.
    eapply derives_trans.
    { simpl; intros. apply andp_right. apply derives_refl.
      rewrite andp_comm. rewrite andp_assoc. apply andp_left2.
      rewrite andp_comm. apply typed_true_or_typed_false' in E3.
      simpl in E3. specialize (E3 x).
      rewrite <- andp_assoc.  apply andp_left1. apply E3.
    }
    simpl. intros.
    rewrite andp_comm. rewrite distrib_orp_andp.
    simpl in E1,E2. specialize (E1 x). specialize (E2 x).
    apply orp_left.
    { eapply derives_trans;[|apply E1].
      solve_andp. }
    { eapply derives_trans with (Q0:=FALSE x).
      2:{ unfold FALSE. unfold PROPx. simpl.
          apply derives_extract_prop. intros. tauto. }
      eapply derives_trans;[|apply E2]. solve_andp. }
  }
    { apply derives_aux_refl. }
    { apply derives_aux_refl. }
    { apply derives_aux_refl. }
    { intros. apply derives_aux_refl. }
Qed.

Lemma add_exp_to_return_atom_inv: forall P Q (a:expr) atom,
      atom_return_to_semax Delta P Q (add_exp_to_return_atom a atom) ->
      atom_return_to_semax Delta (P && (local
                                 (@liftx (Tarrow val (LiftEnviron Prop))
                                 (typed_true (typeof a)) (@eval_expr CS a)))
                        ) Q atom.
Proof.
  intros. destruct atom as [atom ret_val].
  rename H into H1.
  eapply semax_aux_seq_inv in H1.
  destruct H1 as [R' [H1 H0]].
  eapply semax_aux_seq_inv in H1.
  destruct H1 as [R [H1 H2]].
  unfold overridePost in H1.
  apply semax_aux_ifthenelse_inv in H1.
  eapply semax_aux_seq;[..|apply H0].
  unfold_der.
  (* eapply semax_aux_noreturn_inv with (Post:={|
    RA_normal := R';RA_break:=FALSE;RA_continue:=FALSE;RA_return:=(fun _ => FALSE)
  |});try reflexivity.
  { apply noreturn_split_result. } *)
  eapply semax_aux_conseq with (R'0:={|
        RA_normal := R';
        RA_break := FALSE;
        RA_continue := FALSE;
        RA_return := Q |}).
    { eapply derives_trans;[|apply H1]. simpl. intros.
      repeat apply andp_right.
      + apply andp_left1. apply derives_refl.
      + apply andp_left2. apply andp_left1. apply derives_refl.
      + apply andp_left2. apply andp_left2. apply andp_left1.
        apply derives_refl.
    }
    { apply derives_aux_refl. }
    { apply derives_aux_refl. }
    { apply derives_aux_refl. }
    { intros. apply derives_aux_refl. }
    rewrite !andp_assoc.
    apply aux_semax_extract_prop. intros E3.
    rewrite andp_comm.
    rewrite !exp_andp1. apply aux_semax_extract_exists. intros P'.
    rewrite andp_assoc.
    apply aux_semax_extract_prop. intros [E1 E2].
    rewrite andp_comm.
    eapply semax_aux_conseq;[..|apply H2].
    { apply semax_aux_skip_inv in E1. unfold RA_normal in E1.
      apply semax_aux_break_inv in E2. unfold RA_break in E2.
      eapply derives_trans.
      { simpl; intros. apply andp_right. apply derives_refl.
        rewrite andp_comm. rewrite andp_assoc. apply andp_left2.
        rewrite andp_comm. apply typed_true_or_typed_false' in E3.
        simpl in E3. specialize (E3 x).
        rewrite <- andp_assoc.  apply andp_left1. apply E3.
      }
      simpl. intros.
      rewrite andp_comm. rewrite distrib_orp_andp.
      simpl in E1,E2. specialize (E1 x). specialize (E2 x).
      apply orp_left.
      { eapply derives_trans;[|apply E1].
        solve_andp. }
      { eapply derives_trans with (Q0:=FALSE x).
        2:{ unfold FALSE. unfold PROPx. simpl.
            apply derives_extract_prop. intros. tauto. }
        eapply derives_trans;[|apply E2]. solve_andp. }
    }
    { apply derives_aux_refl. }
    { apply derives_aux_refl. }
    { apply derives_aux_refl. }
    { intros. apply derives_aux_refl. }
Qed.

Lemma add_exp_to_return_atom_inv_false: forall P Q (a:expr) atom,
      atom_return_to_semax Delta P Q (add_exp_to_return_atom (semax_lemmas.Cnot a) atom) ->
      atom_return_to_semax Delta (P && (local
                                 (@liftx (Tarrow val (LiftEnviron Prop))
                                 (typed_false (typeof a)) (@eval_expr CS a)))
                        ) Q atom.
Proof.
  intros. destruct atom as [atom ret_val].
  rename H into H1.
  eapply semax_aux_seq_inv in H1.
  destruct H1 as [R' [H1 H0]].
  eapply semax_aux_seq_inv in H1.
  destruct H1 as [R [H1 H2]].
  unfold overridePost in H1.
  apply semax_aux_ifthenelse_inv in H1.
  eapply semax_aux_seq;[..|apply H0].
  unfold_der.
  (* eapply semax_aux_noreturn_inv with (Post:={|
    RA_normal := R';RA_break:=FALSE;RA_continue:=FALSE;RA_return:=Q)
  |});try reflexivity.
  { apply noreturn_split_result. } *)
  eapply semax_aux_conseq with (R'0:={|
        RA_normal := R';
        RA_break := FALSE;
        RA_continue := FALSE;
        RA_return := Q |}).
    { eapply derives_trans;[|apply H1]. simpl. intros.
      repeat apply andp_right.
      + apply andp_left1. apply derives_refl.
      + apply andp_left2. apply andp_left1. apply derives_refl.
      + apply andp_left2. apply andp_left2. apply andp_left1.
        apply derives_refl.
    }
    { apply derives_aux_refl. }
    { apply derives_aux_refl. }
    { apply derives_aux_refl. }
    { intros. apply derives_aux_refl. }
    rewrite !andp_assoc.
    apply aux_semax_extract_prop. intros E3.
    rewrite andp_comm.
    rewrite !exp_andp1. apply aux_semax_extract_exists. intros P'.
    rewrite andp_assoc.
    apply aux_semax_extract_prop. intros [E1 E2].
    rewrite andp_comm.
    eapply semax_aux_conseq;[..|apply H2].
    { apply semax_aux_skip_inv in E1. unfold RA_normal in E1.
      apply semax_aux_break_inv in E2. unfold RA_break in E2.
      eapply derives_trans.
      { simpl; intros. apply andp_right. apply derives_refl.
        rewrite andp_comm. rewrite andp_assoc. apply andp_left2.
        rewrite andp_comm. apply typed_true_or_typed_false' in E3.
        simpl in E3. specialize (E3 x).
        rewrite <- andp_assoc.  apply andp_left1. apply E3.
      }
      simpl. intros.
      rewrite andp_comm. rewrite distrib_orp_andp.
      simpl in E1,E2. specialize (E1 x). specialize (E2 x).
      apply orp_left.
      { eapply derives_trans;[|apply E1].
        solve_andp. }
      { eapply derives_trans with (Q0:=FALSE x).
        2:{ unfold FALSE. unfold PROPx. simpl.
            apply derives_extract_prop. intros. tauto. }
        eapply derives_trans;[|apply E2]. solve_andp. }
    }
    { apply derives_aux_refl. }
    { apply derives_aux_refl. }
    { apply derives_aux_refl. }
    { intros. apply derives_aux_refl. }
Qed.


Lemma add_exp_to_pres_list_in: forall x pres a, In x pres -> In (add_exp_to_pre a x) (add_exp_to_pres a pres).
Proof.
  intros.
  induction pres.
  - inv H.
  - destruct H;subst.
    + left. auto.
    + right. auto.
Qed.

Lemma add_exp_to_atoms_list_in: forall a x atoms,
 In x atoms ->
 In (inl a :: x) (add_exp_to_atoms a atoms).
Proof.
  intros.
  induction atoms.
  - inv H.
  - destruct H;subst.
    + left. auto.
    + right. auto.
Qed.

Lemma add_exp_to_return_atoms_list_in: forall a x atoms,
In x atoms ->
In (add_exp_to_return_atom a x) (add_exp_to_return_atoms a atoms).
Proof.
intros.
induction atoms.
- inv H.
- destruct H;subst.
  + left. unfold add_exp_to_return_atom. destruct x. auto.
  + right. auto.
Qed.

Lemma add_exp_to_pre_tc: forall P a pre', 
  add_pre_to_semax Delta P (add_exp_to_pre a pre') ->
  exists (c1' c2' : Clight.statement) (Q' : ret_assert),
    semax_aux Delta P (Clight.Sifthenelse a c1' c2') Q'.
Proof.
  intros. destruct pre'. induction p.
  - rename H into H1. apply semax_aux_seq_inv in H1. destruct H1 as [Q' [? ?]].
     exists Clight.Sskip, Clight.Sbreak, (overridePost Q'
             {| RA_normal := a0;
                RA_break := FALSE;
                RA_continue := FALSE;
                RA_return := fun _ : option val => FALSE |}).
    apply H.
  - pose proof HA. destruct H1 as [x _]. auto.
    specialize (H0 x). simpl in H. specialize (H x). apply H0. apply H.
Qed.

Lemma add_exp_to_atom_tc: forall P Q a normal_atom',
  atom_to_semax Delta P Q (inl a :: normal_atom') ->
  exists (c1' c2' : Clight.statement) (Q' : ret_assert),
    semax_aux Delta P (Clight.Sifthenelse a c1' c2') Q'.
Proof.
  intros. rename H into H0.
  apply semax_aux_seq_inv in H0. destruct H0 as [Q' [? ?]].
  exists Clight.Sskip, Clight.Sbreak, (overridePost Q'
          {| RA_normal := Q;
             RA_break := FALSE;
             RA_continue := FALSE;
             RA_return := fun _ : option val => FALSE |}).
  apply H.
Qed.

Lemma add_exp_to_return_atom_tc: forall P Q a return_atom',
atom_return_to_semax Delta P Q (add_exp_to_return_atom a return_atom') ->
exists (c1' c2' : Clight.statement) (Q' : ret_assert),
  semax_aux Delta P (Clight.Sifthenelse a c1' c2') Q'.
Proof.
  intros. destruct return_atom'. rename H into H1.
  apply semax_aux_seq_inv in H1. destruct H1 as [Q'' [? ?]].
  apply semax_aux_seq_inv in H. destruct H as [Q' [? ?]].  
  exists Clight.Sskip, Clight.Sbreak, (overridePost Q'
          (overridePost Q''
          {| RA_normal := FALSE;
             RA_break := FALSE;
             RA_continue := FALSE;
             RA_return := Q |})).
  apply H.
Qed.



(*-------------------
Proofs for split_loop soundness
--------------------*)
(** Aux lemmas for single invariant loop soundness *)
Lemma split_not_empty_incr: forall stm res,
 continue_atom res = [] ->
 path_split stm res ->
  ~ (pre res = [] /\ normal_atom res = []
     /\ break_atom res = []  /\ return_atom res = []).
Proof.
  intros. apply split_not_empty in H0.
  intros C. apply H0. tauto.
Qed.

Lemma path_to_semax_given_sem: forall X (HX:Non_empty_Type X) ass' p,
  path_to_semax Delta (Given_assert X HX ass', p) ->
  forall x:X, path_to_semax Delta (ass' x, p).
Proof.
  intros. revert x. auto.
Qed.

Lemma split_loop_inv1_conn_pre1_inv: forall inv pres1,
  Forall (path_to_semax Delta)
       (posts_conn_pres [(Basic_partial inv, [])] pres1)
  -> Forall (add_pre_to_semax Delta inv) pres1.
Proof.
  intros.
  induction pres1.
  + constructor.
  + constructor.
    - destruct a. apply Forall_app in H.
      destruct H as [H1 _]. induction p.
      * inv H1. auto.
      * intros x. apply H.
        inv H1. eapply path_to_semax_given_sem in H3.
        simpl.
        destruct (p x) eqn:E;(constructor;[rewrite <- E; apply H3| constructor]).
    - simpl in H. apply Forall_app in H. apply proj2 in H.
      auto.
Qed.

Lemma split_loop_inv1_conn_atom1_inv: forall inv Q atoms,
  Forall (add_post_to_semax Delta Q)
       (posts_conn_atoms [(Basic_partial inv, [])] atoms)
  -> Forall (atom_to_semax Delta inv Q) atoms.
Proof.
  intros.
  apply Forall_forall. intros.
  assert (E: In  (Basic_partial inv, x) 
    (posts_conn_atoms [(Basic_partial inv, [])] atoms)).
  { apply in_split in H0. destruct H0 as [l1 [l2 H0]].
    rewrite H0. unfold posts_conn_atoms.
    rewrite flat_map_concat_map. simpl.
    rewrite map_app. rewrite app_nil_r.
    apply in_or_app. right. left. simpl.
    auto.  }
  eapply Forall_forall in H. 2:{ apply E. }
  auto.
Qed.

Lemma split_loop_inv1_conn_return1_inv: forall inv Q atoms,
  Forall (add_return_to_semax Delta Q)
       (posts_conn_returns [(Basic_partial inv, [])] atoms)
  -> Forall (atom_return_to_semax Delta inv Q) atoms.
Proof.
  intros.
  apply Forall_forall. intros.
  destruct x as [p v].
  assert (E: In  (Basic_partial inv, p, v) 
    (posts_conn_returns [(Basic_partial inv, [])] atoms)).
  { apply in_split in H0. destruct H0 as [l1 [l2 H0]].
    rewrite H0. unfold posts_conn_returns.
    rewrite flat_map_concat_map. simpl.
    rewrite map_app. rewrite app_nil_r.
    apply in_or_app. right. left. simpl.
    auto.  }
  eapply Forall_forall in H. 2:{ apply E. }
  auto.
Qed.


Lemma atoms_conn_inv_basic: forall atoms inv,
  all_basic ((atoms_conn_pres atoms [(Basic_partial inv, [])])) = true.
Proof.
  intros.
  induction atoms.
  - reflexivity.
  - simpl. auto.
Qed. 


Lemma add_post_to_semax_reverse_group2:
forall post posts atoms R, 
  In post posts ->
  Forall (add_post_to_semax Delta R)
      (posts_conn_atoms posts atoms) -> atoms <> nil ->
  add_post_to_semax Delta (
    EX Q, Q &&
    !!(Forall (atom_to_semax Delta Q R) atoms)
  ) post.
Proof.
  intros.
  apply (add_post_to_semax_reverse_group post atoms R);auto.
  apply Forall_forall. intros. eapply Forall_forall in H0. apply H0.
  apply in_split in H. destruct H as [posts1 [posts2 H]].
  rewrite H in *. unfold posts_conn_atoms.
  rewrite flat_map_concat_map. rewrite map_app. simpl.
  rewrite concat_app. apply in_or_app. right.
  rewrite concat_cons. apply in_or_app. left. auto.
Qed.

Lemma add_return_to_semax_reverse_group2:
forall post posts atoms R, 
  In post posts ->
  Forall (add_return_to_semax Delta R)
      (posts_conn_returns posts atoms) -> atoms <> nil ->
  add_post_to_semax Delta (
    EX Q, Q &&
    !!(Forall (atom_return_to_semax Delta Q R) atoms)
  ) post.
Proof.
  intros.
  apply (add_return_to_semax_reverse_group post atoms R);auto.
  apply Forall_forall. intros. eapply Forall_forall in H0. apply H0.
  apply in_split in H. destruct H as [posts1 [posts2 H]].
  rewrite H in *. unfold posts_conn_returns.
  rewrite flat_map_concat_map. rewrite map_app. simpl.
  rewrite concat_app. apply in_or_app. right.
  rewrite concat_cons. apply in_or_app. left. auto.
Qed.


Lemma posts_inv_semax_sem: forall atoms inv post,
  (add_post_to_semax Delta (EX Q : assert, Q &&
  !! Forall (add_pre_to_semax Delta Q)
      (atoms_conn_pres atoms [(Basic_partial inv, [])])) post) -> 
  add_post_to_semax Delta (EX Q : assert, Q && 
    !! (Forall (atom_to_semax Delta Q inv) atoms)) post.
Proof.
  intros. eapply add_post_to_semax_derives;[|apply H].
  Intros Q. Exists Q. 
  apply andp_left2. apply andp_right;[apply derives_refl|].
  apply prop_right. eapply Forall_forall. intros.
  eapply Forall_forall with (x:= (Basic_partial inv, x)) in H0.
  - auto.
  - apply in_split in H1. destruct H1 as [l1 [l2 H1]].
    rewrite H1.
    unfold atoms_conn_pres. rewrite flat_map_concat_map.
    rewrite map_app. rewrite concat_app. simpl.
    apply in_or_app. right. left. rewrite app_nil_r. auto.
Qed.

Lemma atoms_inv_semax_sem: forall inv1 inv2 atoms atom,
atom_to_semax Delta inv1
  (EX Q : assert, Q &&
  !! Forall (add_pre_to_semax Delta Q)
        (atoms_conn_pres atoms [(Basic_partial inv2, [])])) atom
-> atom_to_semax Delta inv1
(EX Q : assert, Q &&
!! Forall (atom_to_semax Delta Q inv2) atoms) atom.
Proof.
  intros. eapply atom_to_semax_derives_post;[|apply H].
  Intros Q. Exists Q. 
  apply andp_left2. apply andp_right;[apply derives_refl|].
  apply prop_right. eapply Forall_forall. intros.
  eapply Forall_forall with (x:= (Basic_partial inv2, x)) in H0.
  - auto.
  - apply in_split in H1. destruct H1 as [l1 [l2 H1]].
    rewrite H1.
    unfold atoms_conn_pres. rewrite flat_map_concat_map.
    rewrite map_app. rewrite concat_app. simpl.
    apply in_or_app. right. left. rewrite app_nil_r. auto.
Qed.

Lemma atoms_conn_inv_not_nil: forall atoms inv, 
  atoms <> nil ->
  atoms_conn_pres atoms [(Basic_partial inv, [])] <> [].
Proof.
  intros. destruct atoms. exfalso; apply H; auto.
  simpl. intros C. inv C.
Qed.

Lemma split_loop_normal_post1_conn_wp_inv: forall 
  inv Qr Qn normal_posts1
  pres2 normal_atoms2 break_atoms2 return_atoms2
  (Ebasic2: all_basic pres2 = true),
  ~ (pres2 = [] /\ normal_atoms2 = []
     /\ break_atoms2 = []  /\ return_atoms2 = []) ->
    Forall (path_to_semax Delta)
        (posts_conn_pres normal_posts1 pres2) ->
    Forall (path_to_semax Delta)
      (posts_conn_pres normal_posts1
        (atoms_conn_pres normal_atoms2 [(Basic_partial inv, [])])) ->
    Forall (add_post_to_semax Delta Qn)
        (posts_conn_atoms normal_posts1 break_atoms2) ->
    Forall (add_return_to_semax Delta Qr)
        (posts_conn_returns normal_posts1 return_atoms2) ->
    Forall
      (add_post_to_semax Delta
        (EX Q' : assert, Q' &&
          !! (Forall (add_pre_to_semax Delta Q') pres2 /\
              Forall (atom_to_semax Delta Q' inv) normal_atoms2 /\
              Forall (atom_return_to_semax Delta Q' Qr) return_atoms2 /\
              Forall (atom_to_semax Delta Q' Qn) break_atoms2)))
        normal_posts1.
Proof.
  intros. eapply Forall_forall.
  intros.
  pose proof path_conn_to_semax_reverse_group4' _ _ _ H4 Ebasic2 H0.
  pose proof path_conn_to_semax_reverse_group4' _ _ _ H4 (atoms_conn_inv_basic _ _) H1.
  pose proof add_post_to_semax_reverse_group2 _ _ _ _ H4 H2.
  pose proof add_return_to_semax_reverse_group2 _ _ _ _ H4 H3.
  pose proof atoms_conn_inv_not_nil normal_atoms2 inv.
  pose proof imp_trans H9 H6; clear H9 H6.
  pose proof posts_inv_semax_sem normal_atoms2 inv x.
  pose proof imp_trans H10 H6; clear H10 H6.
  destruct pres2,break_atoms2,return_atoms2,normal_atoms2;
  try specialize (H5 nil_cons);
    try specialize (H7 nil_cons);
      try specialize (H8 nil_cons);
        try specialize (H9 nil_cons);
        [exfalso; apply H; repeat split;auto|..];
        combine_aux_post_auto.
Qed.



Lemma split_loop_continue_post1_conn_wp_inv: forall 
  inv Qr Qn continue_posts1
  pres2 normal_atoms2 break_atoms2 return_atoms2
  (Ebasic2: all_basic pres2 = true),
  ~ (pres2 = [] /\ normal_atoms2 = []
     /\ break_atoms2 = []  /\ return_atoms2 = []) ->
  Forall (path_to_semax Delta)
    (posts_conn_pres continue_posts1
      (atoms_conn_pres normal_atoms2 [(Basic_partial inv, [])])) ->
  Forall (path_to_semax Delta)
    (posts_conn_pres continue_posts1 pres2) ->
  Forall (add_post_to_semax Delta Qn)
    (posts_conn_atoms continue_posts1 break_atoms2) ->
  Forall (add_return_to_semax Delta Qr)
    (posts_conn_returns continue_posts1 return_atoms2) ->
  Forall
    (add_post_to_semax Delta
      (EX Q' : assert, Q' &&
        !! (Forall (add_pre_to_semax Delta Q') pres2 /\
            Forall (atom_to_semax Delta Q' inv) normal_atoms2 /\
            Forall (atom_return_to_semax Delta Q' Qr) return_atoms2 /\
            Forall (atom_to_semax Delta Q' Qn) break_atoms2)))
    continue_posts1.
Proof.
  intros.
  eapply split_loop_normal_post1_conn_wp_inv;auto.
Qed.


Lemma split_loop_normal_atoms1_conn_wp_inv: forall 
  inv Qr Qn normal_atoms1
  pres2 normal_atoms2 break_atoms2 return_atoms2
  (Ebasic2: all_basic pres2 = true),
  ~ (pres2 = [] /\ normal_atoms2 = []
     /\ break_atoms2 = []  /\ return_atoms2 = []) ->
  Forall (path_to_semax Delta)
    (posts_conn_pres [(Basic_partial inv, [])]
        (atoms_conn_pres normal_atoms1 pres2)) ->
  Forall (path_to_semax Delta)
    (posts_conn_pres [(Basic_partial inv, [])]
      (atoms_conn_pres normal_atoms1
        (atoms_conn_pres normal_atoms2 [(Basic_partial inv, [])]))) ->
  Forall (add_return_to_semax Delta Qr)
    (posts_conn_returns [(Basic_partial inv, nil)]
      (atoms_conn_returns normal_atoms1 return_atoms2)) ->
  Forall (add_post_to_semax Delta Qn)
    (posts_conn_atoms [(Basic_partial inv, nil)]
      (atoms_conn_atoms normal_atoms1 break_atoms2)) ->
  Forall
    (atom_to_semax Delta inv
      (EX Q' : assert, Q' &&
        !! (Forall (add_pre_to_semax Delta Q') pres2 /\
            Forall (atom_to_semax Delta Q' inv) normal_atoms2 /\
            Forall (atom_return_to_semax Delta Q' Qr) return_atoms2 /\
            Forall (atom_to_semax Delta Q' Qn) break_atoms2)))
    normal_atoms1.
Proof.
  intros. eapply Forall_forall.
  intros.
  apply split_loop_inv1_conn_pre1_inv in H0.
  apply split_loop_inv1_conn_pre1_inv in H1.
  apply split_loop_inv1_conn_atom1_inv in H3.
  apply split_loop_inv1_conn_return1_inv in H2.
  pose proof atom_conn_pres_to_semax_reverse_group2' _ _ _ _ H4 Ebasic2 H0.
  pose proof atom_conn_pres_to_semax_reverse_group2' _ _ _ _ H4 (atoms_conn_inv_basic _ _) H1.
  pose proof atoms_conn_inv_not_nil normal_atoms2 inv.
  pose proof imp_trans H7 H6;clear H7 H6.
  pose proof atoms_inv_semax_sem inv inv normal_atoms2 x.
  pose proof imp_trans H8 H6;clear H8 H6.
  pose proof add_return_to_atom_semax_group _ _ _ _ _ H2 H4.
  pose proof atom_conn_atom_to_semax_reverse_group _ _ _ _ _ H3 H4.
  destruct pres2,break_atoms2,return_atoms2,normal_atoms2;
  try specialize (H5 nil_cons);
    try specialize (H7 nil_cons);
      try specialize (H6 nil_cons);
        try specialize (H8 nil_cons);
        [exfalso; apply H; repeat split;auto|..];
        combine_aux_atom_auto.
Qed.

Lemma split_loop_inv1_conn_break_atoms1_inv: forall Qn inv break_atoms1,
  Forall (add_post_to_semax Delta Qn)
	  (posts_conn_atoms [(Basic_partial inv, nil)] break_atoms1)
  -> Forall (atom_to_semax Delta inv Qn) break_atoms1.
Proof.
  intros. apply Forall_forall. intros.
  eapply Forall_forall in H.
  2:{ apply in_split in H0. destruct H0 as [l1 [l2 H0]].
      subst break_atoms1. unfold posts_conn_atoms.
      rewrite flat_map_concat_map. simpl.
      rewrite map_app. rewrite app_nil_r. apply in_or_app.
      right. left. reflexivity. }
  { auto. }
Qed.


Lemma split_loop_continue_atoms1_conn_wp_inv: forall 
  inv Qr Qn continue_atoms1
  pres2 normal_atoms2 break_atoms2 return_atoms2
  (Ebasic2: all_basic pres2 = true),
  ~ (pres2 = [] /\ normal_atoms2 = []
     /\ break_atoms2 = []  /\ return_atoms2 = []) ->
  Forall (path_to_semax Delta)
    (posts_conn_pres [(Basic_partial inv, [])]
      (atoms_conn_pres continue_atoms1
        (atoms_conn_pres normal_atoms2 [(Basic_partial inv, [])]))) ->
  Forall (path_to_semax Delta)
    (posts_conn_pres [(Basic_partial inv, [])]
      (atoms_conn_pres continue_atoms1 pres2)) ->
  Forall (add_post_to_semax Delta Qn)
    (posts_conn_atoms [(Basic_partial inv, [])]
      (atoms_conn_atoms continue_atoms1 break_atoms2)) ->
  Forall (add_return_to_semax Delta Qr)
    (posts_conn_returns [(Basic_partial inv, nil)]
      (atoms_conn_returns continue_atoms1 return_atoms2)) ->
  Forall
    (atom_to_semax Delta inv
      (EX Q' : assert, Q' &&
        !! (Forall (add_pre_to_semax Delta Q') pres2 /\
            Forall (atom_to_semax Delta Q' inv) normal_atoms2 /\
            Forall (atom_return_to_semax Delta Q' Qr) return_atoms2 /\
            Forall (atom_to_semax Delta Q' Qn) break_atoms2)))
    continue_atoms1.
Proof.
  intros.
  eapply split_loop_normal_atoms1_conn_wp_inv;auto.
Qed.


Lemma split_loop_inv1_conn_return_atoms1_inv: forall inv Qr return_atoms1,
  Forall (add_return_to_semax Delta Qr)
	  (posts_conn_returns [(Basic_partial inv, nil)] return_atoms1)
  -> Forall (atom_return_to_semax Delta inv Qr) return_atoms1.
Proof.
  intros. apply Forall_forall. intros. destruct x as [p1 e1].
  eapply Forall_forall in H.
  2:{ apply in_split in H0. destruct H0 as [l1 [l2 H0]].
      subst return_atoms1. unfold posts_conn_returns.
      rewrite flat_map_concat_map. simpl.
      rewrite map_app. rewrite app_nil_r. apply in_or_app.
      right. left. reflexivity. }
  { auto. }
Qed.


Lemma split_loop_inv1_conn_normal_posts1_inv: forall inv normal_posts2,
Forall (path_to_semax Delta)
	(posts_conn_pres normal_posts2 [(Basic_partial inv, [])]) ->
Forall (add_post_to_semax Delta inv) normal_posts2.
Proof.
  intros. apply Forall_forall. intros.
  destruct x as [a2 p2].
  eapply Forall_forall in H.
  2:{ apply in_split in H0. destruct H0 as [l1 [l2 H0]].
      subst normal_posts2. unfold posts_conn_pres.
      rewrite flat_map_concat_map. simpl.
      rewrite posts_conn_pre_app.
      rewrite app_nil_r. apply in_or_app.
      right. rewrite posts_conn_basic_pre_cons.
      left. reflexivity. }
  { simpl in H. rewrite app_nil_r in H. 
    clear H0. induction a2.
    - auto.
    - intros x. apply H0. auto. }
Qed.

Ltac in_split_result S1 :=
  apply Forall_forall; intros; eapply Forall_forall in S1;[apply S1|];
  repeat (apply in_or_app;auto;right).


Lemma pack_assert_into_posts_app: forall  x inv posts,
  In x posts->
  In (bind_post_conn_pre x [] inv) 
     (posts_conn_pres posts [(Basic_partial inv, [])]).
Proof.
  induction posts.
  - auto.
  - intros. destruct H.
    + subst. unfold posts_conn_pres.
      rewrite flat_map_concat_map. destruct x as [a1 p1].
      simpl. destruct a1; destruct p1;simpl;auto.
    + unfold posts_conn_pres.
      rewrite flat_map_concat_map. apply IHposts in H.
      destruct a as [a1 p1].
      simpl. destruct a1; destruct p1;simpl;auto.
Qed. 

Lemma pack_assert_into_post_sem: forall inv post,
  path_to_semax Delta 
  (bind_post_conn_pre post [] inv) ->
  (add_post_to_semax Delta inv) post.
Proof.
  intros. destruct post as [a1 p].
  induction a1.
  - simpl in H. rewrite app_nil_r in H. auto. 
  - simpl in *. intros. apply H0. auto.
Qed.

Lemma pack_assert_into_post_group: forall inv posts,
  Forall (path_to_semax Delta) 
        (posts_conn_pres posts [(Basic_partial inv, [])]) ->
  Forall (add_post_to_semax Delta inv) posts.
Proof.
  intros. apply Forall_forall. intros.
  apply pack_assert_into_post_sem.
  eapply Forall_forall in H.
  apply H. apply pack_assert_into_posts_app. auto.
Qed.

Lemma pack_assert_into_atom_sem: forall inv1 atom inv2,
  path_to_semax Delta (post_conn_bind_pre 
    (Basic_partial inv2, []) atom inv1) ->
  (atom_to_semax Delta inv1 inv2) atom.
Proof.
  intros. simpl in H. rewrite app_nil_r in H.
  auto.
Qed.

Lemma pack_assert_into_atom_group: forall inv1 atoms inv2,
  Forall (path_to_semax Delta) (posts_conn_pres [(Basic_partial inv1, [])]
    (atoms_conn_pres atoms [(Basic_partial inv2, [])])) ->
  Forall (atom_to_semax Delta inv1 inv2) atoms.
Proof.
  intros. apply Forall_forall. intros.
  apply pack_assert_into_atom_sem.
  eapply Forall_forall in H.
  apply H. apply in_split in H0. destruct H0 as [l1 [l2 H0]].
  rewrite H0. rewrite atoms_conn_pres_app1.
  unfold posts_conn_pres. rewrite flat_map_concat_map.
  rewrite map_app. rewrite concat_app. apply in_or_app. right.
  left. simpl. reflexivity.
Qed.


Lemma pack_assert_into_atom_half_sem: forall inv1 atom inv2,
  add_post_to_semax Delta inv2 (post_conn_atom
    (Basic_partial inv1, []) atom) ->
  (atom_to_semax Delta inv1 inv2) atom.
Proof.
  intros. simpl in H.
  auto.
Qed.

Lemma pack_assert_into_atom_half_group: forall inv1 atoms inv2,
  Forall (add_post_to_semax Delta inv2) (posts_conn_atoms 
      [(Basic_partial inv1, [])] atoms) ->
  Forall (atom_to_semax Delta inv1 inv2) atoms.
Proof.
  intros. apply Forall_forall. intros.
  apply pack_assert_into_atom_half_sem.
  eapply Forall_forall in H.
  apply H. simpl. rewrite app_nil_r.
  apply in_split in H0. destruct H0 as [l1 [l2 H0]].
  rewrite H0. 
  rewrite map_app. apply in_or_app. right.
  left. simpl. reflexivity.
Qed.
  

Lemma pack_assert_into_ret_atom_half_sem: forall inv1 atom inv2,
  add_return_to_semax Delta inv2 (post_conn_return
    (Basic_partial inv1, []) (fst atom) (snd atom)) ->
  (atom_return_to_semax Delta inv1 inv2) atom.
Proof.
  intros. destruct atom. simpl in H.
  auto.
Qed.


Lemma pack_assert_into_ret_atom_half_group: forall inv1 atoms inv2,
  Forall (add_return_to_semax Delta inv2) (posts_conn_returns 
      [(Basic_partial inv1, [])] atoms) ->
  Forall (atom_return_to_semax Delta inv1 inv2) atoms.
Proof.
  intros. apply Forall_forall. intros.
  apply pack_assert_into_ret_atom_half_sem.
  eapply Forall_forall in H.
  apply H. simpl. rewrite app_nil_r.
  apply in_split in H0. destruct H0 as [l1 [l2 H0]].
  rewrite H0. 
  rewrite map_app. apply in_or_app. right.
  left. simpl. reflexivity.
Qed.

Lemma in_or_concat0 : forall(A : Type) (a b: list A)  x,
In x (concat(app [a] [b])) <-> In x a \/ In x b .
Proof.
intros. induction a;eauto.
- split. 
  + simpl. intros. apply in_app_or in H. inv H;eauto.
  + simpl. intros. inv H;eauto. inv H0. apply in_or_app. left. apply H0.
- split.
  + simpl. intros. destruct H.
   ++ left. left. auto.
   ++ apply in_app_or in H. destruct H;eauto. apply in_app_or in H. inv H;eauto. inv H0.
  + simpl. intros. destruct H.
   ++ destruct H;auto. right. apply in_or_app. left. auto.
   ++ right. apply in_or_app. right. apply in_or_app. auto.   
Qed.

Lemma in_or_concat1 : forall(A : Type) (a b: list (list A))  x,
In x (concat(app a b)) -> In x (concat a) \/ In x (concat b) .
Proof.
intros. induction a;eauto. simpl in H. simpl.
apply in_app_or in H. destruct H.
- left. apply in_app. left. auto.
- apply IHa in H. destruct H. 
 + left. apply in_app. right. auto.
 + right. auto.
 Qed.

(* post = basic + [], pre = binded pre
   then In x ((post + atom) + pre) is invalid
   can't derive In x (post + (atom + pre))

   to avoid this case, we specify that pre should 
   be basic to ensure safety
*)
Lemma conn_assoc_help1:forall pre post atoms x
(Epre: all_basic [pre] = true),
In x 
  (posts_conn_pre (posts_conn_atoms ([post]) (atoms)) (pre)) <->
In x
  (posts_conn_pres [post] (atoms_conn_pres (atoms) [pre])).
Proof.
  intros. induction atoms as [|p2].
  - simpl. tauto.
  - split;intros.
    + destruct post as [a3 p3], pre as [a1 p1].
      destruct a3 as [a3|], a1 as [a1|];simpl in *;
      rewrite !app_nil_r in *.
      * destruct p3 as[|p3 p3'], p2 as [|p2 p2'];
        simpl in *;try rewrite !app_nil_r in *.
        { destruct H;auto. right.
          apply IHatoms;auto. }
        { destruct H;auto. right.
          apply IHatoms;auto. }
        { destruct H;auto. right.
          apply IHatoms;auto. }
        { destruct H;auto.
          { left. subst x.
            replace (p3' ++ p2 :: p2' ++ p1)
              with ((p3' ++ p2 :: p2') ++ p1). auto.
            { rewrite app_comm_cons.
              simpl. rewrite <- app_assoc. simpl. reflexivity. } }
          { right. apply IHatoms. auto. }
        }
      * simpl in H.
        destruct p3 as[|p3 p3'], p2 as [|p2 p2'];simpl in H;simpl.
        { destruct H;auto. right.
          apply IHatoms. auto. }
        { right.
          apply IHatoms. auto. }
        { apply IHatoms. auto. }
        { apply IHatoms. auto. }
      * simpl in H. simpl.
        destruct H.
        { rewrite app_assoc in *. left;auto. }
        { right. apply IHatoms.
          auto. }
      * simpl in H. simpl.
        apply IHatoms. simpl. auto.
    + destruct post as [a3 p3], pre as [a1 p1].
      destruct a3 as [a3|], a1 as [a1|].
      * simpl in H. 
        destruct p3 as[|p3 p3'], p2 as [|p2 p2'];
        simpl in *;rewrite !app_nil_r in *.
        { destruct H;auto. right.
          apply IHatoms. auto. }
        { destruct H;auto. right.
          apply IHatoms. auto. }
        { destruct H;auto. right.
          apply IHatoms. simpl.
          auto. }
        { destruct H;auto.
          { left. subst x.
            replace (p3' ++ p2 :: p2' ++ p1)
              with ((p3' ++ p2 :: p2') ++ p1). auto.
            { rewrite app_comm_cons.
              simpl. rewrite <- app_assoc. simpl. reflexivity. } }
          { right. apply IHatoms. simpl. auto. }
        }
      * simpl in H.
        destruct p3 as[|p3h p3'] eqn:E1, p2 as [|p2h p2'] eqn:E2;
        simpl in *;
        rewrite !app_nil_r in *.
        { destruct H;auto. right.
          apply IHatoms. simpl. auto. }
        { inv Epre. (* special case*) }
        { apply IHatoms. simpl. auto. }
        { apply IHatoms. simpl. auto. }
      * simpl in H. simpl.
        destruct H.
        { rewrite app_assoc in *. left;auto. }
        { right.
          apply IHatoms. simpl. auto. }
      * simpl in H.
        apply IHatoms. simpl.
        auto.
Qed.


Lemma posts_conn_pres_app: forall x posts1 posts2 pres,
    In x (posts_conn_pres (posts1 ++ posts2) pres) <->
    In x (posts_conn_pres posts1 pres ++ posts_conn_pres posts2 pres).
Proof.
  intros.
  induction pres.
  - rewrite app_nil_l. simpl. tauto.
  - simpl. rewrite posts_conn_pre_app.
    split;intro H;repeat (apply in_app_or in H;destruct H);
    apply in_or_app.
    * left. apply in_or_app. auto.
    * right. apply in_or_app. auto.
    * apply IHpres in H. apply in_app_or in H;destruct H.
      { left. apply in_or_app. auto. }
      { right. apply in_or_app. auto. }
    * left. apply in_or_app. auto.
    * right. apply IHpres. apply in_or_app. auto.
    * left. apply in_or_app. auto.
    * right. apply IHpres. apply in_or_app. auto.
Qed.

Lemma conn_assoc_help:forall pre posts atoms x,
all_basic [pre]= true->
In x 
(posts_conn_pre (posts_conn_atoms (posts) (atoms)) (pre)) <->
In x
(posts_conn_pres posts (atoms_conn_pres (atoms) [pre])).
Proof.
  intros. induction posts as [|post posts'].
  - simpl. split;intros;try destruct H0.
    induction atoms;simpl in H0; auto.
  - split;intros.
    + replace (post::posts') with ([post]++posts') by reflexivity.
      apply posts_conn_pres_app. apply in_or_app.
      unfold posts_conn_atoms in H0.
      rewrite flat_map_concat_map in H0. simpl in H0.
      rewrite posts_conn_pre_app in H0.
      apply in_app_or in H0. destruct H0.
      { left.
        apply conn_assoc_help1;auto. simpl. 
        rewrite app_nil_r. auto.
      }
      { right. apply IHposts'.
        unfold posts_conn_atoms. rewrite flat_map_concat_map.
        auto. }
    + replace (post::posts') with ([post]++posts') in H0 by reflexivity.
      apply posts_conn_pres_app in H0. apply in_app_or in H0.
      unfold posts_conn_atoms.
      rewrite flat_map_concat_map. simpl.
      rewrite posts_conn_pre_app.
      apply in_or_app. destruct H0.
      { left.
        apply conn_assoc_help1 in H0;auto. simpl in H0. 
        rewrite app_nil_r in *. auto.
      }
      { right. apply IHposts' in H0.
        unfold posts_conn_atoms in H0.
        rewrite flat_map_concat_map in H0.
        auto. }
Qed.

Lemma posts_conn_pres_proper_help: 
  forall post pres1 pres2,
  (forall y, In y pres1 -> In y pres2) ->
  (forall x ,In x (posts_conn_pres [post] pres1) 
    -> In x (posts_conn_pres [post] pres2)).
Proof.
  intros. revert dependent pres2.
  induction pres1 as [|pre pres1'].
  - intros. simpl in *. destruct H0.
  - intros. unfold posts_conn_pres in H0.
    rewrite flat_map_concat_map in H0.
    rewrite map_cons in H0.
    rewrite concat_cons in H0. apply in_app_or in H0.
    destruct H0.
    + specialize (H pre).
      assert (In pre (pre::pres1')) by (simpl;auto).
      specialize (H H1).
      apply in_split in H. destruct H as [l1 [l2 H]].
      rewrite H. unfold posts_conn_pres.
      rewrite flat_map_concat_map.
      rewrite map_app. rewrite concat_app. apply in_or_app.
      right. rewrite map_cons. rewrite concat_cons.
      apply in_or_app. left. auto.
    + apply IHpres1'.
      { unfold posts_conn_pres. rewrite flat_map_concat_map.
        apply H0. }
      { intros. apply H. right. auto. }
Qed.

Lemma posts_conn_pres_proper: forall posts pres1 pres2,
  (forall y, In y pres1 -> In y pres2) ->
  (forall x ,In x (posts_conn_pres posts pres1) -> In x (posts_conn_pres posts pres2)).
Proof.
  intros. induction posts.
  - unfold posts_conn_pres in H0. exfalso.
    clear dependent pres2.
    induction pres1;simpl in H0;try destruct H0;auto.
- replace (a::posts) with ([a]++posts) in * by reflexivity.
    rewrite !posts_conn_pres_app in *.
    apply in_app_or in H0;
    destruct H0;apply in_or_app;try tauto;left.
    { eapply posts_conn_pres_proper_help in H0.
      apply H0. apply H. }
Qed.

Lemma posts_conn_pres_proper_iff: forall posts pres1 pres2,
  (forall y, In y pres1 <-> In y pres2) ->
  (forall x ,In x (posts_conn_pres posts pres1) <-> In x (posts_conn_pres posts pres2)).
Proof.
  intros. split;intro.
  - eapply posts_conn_pres_proper. 2:{ apply H0. }
    intros. apply H. auto.
  - eapply posts_conn_pres_proper. 2:{ apply H0. }
    intros. apply H. auto.
Qed.

Lemma conn_assoc1:forall pres posts atoms x,
 all_basic pres= true->
 In x 
 (posts_conn_pres (posts_conn_atoms (posts) (atoms)) (pres)) <->
 In x
 (posts_conn_pres posts (atoms_conn_pres (atoms) (pres))).
Proof.
  intros.
  induction pres.
  - simpl. split;intro;try destruct H0.
    induction atoms;simpl in H0;auto.
  - simpl. destruct a as [p2 a2]. destruct p2 as [p2|];try inv H.
    specialize (IHpres H1). split;intro.
    + apply in_app_or in H. destruct H.
      { pose proof (atoms_conn_pres_app2 [(Basic_partial p2, a2)]
                      pres atoms).
        eapply posts_conn_pres_proper_iff in H0. simpl in H0.
        apply H0. unfold posts_conn_pres.
        rewrite flat_map_concat_map. rewrite map_app.
        rewrite concat_app. apply in_or_app. left.
        apply conn_assoc_help in H;[|reflexivity].
        unfold posts_conn_pres in H. rewrite flat_map_concat_map in H.
        auto. }
      { pose proof (atoms_conn_pres_app2 [(Basic_partial p2, a2)]
              pres atoms).
        eapply posts_conn_pres_proper_iff in H0. simpl in H0.
        apply H0. unfold posts_conn_pres.
        rewrite flat_map_concat_map. rewrite map_app.
        rewrite concat_app. apply in_or_app. right.
        rewrite <- flat_map_concat_map.
        apply IHpres. auto.
      }
    + apply in_or_app. 
      pose proof (atoms_conn_pres_app2 [(Basic_partial p2, a2)]
        pres atoms).
      eapply posts_conn_pres_proper_iff 
        with (x:=x) (posts:=posts)in H0. simpl in H0.
      apply H0 in H. clear H0.
      unfold posts_conn_pres in H.
      rewrite flat_map_concat_map in H. rewrite map_app in H.
      rewrite concat_app in H. apply in_app_or in H.
      destruct H.
      { left. apply conn_assoc_help;[reflexivity|].
        unfold posts_conn_pres. rewrite flat_map_concat_map.
        auto. }
      { right. apply IHpres.
        unfold posts_conn_pres.
        rewrite flat_map_concat_map. auto.
      }
Qed.

Lemma all_basic_app: forall pres1 pres2,
  all_basic (pres1 ++ pres2) = true <->
  all_basic pres1 = true /\ all_basic pres2 = true.
Proof.
  intros.
  induction pres1.
  - simpl. tauto.
  - destruct a as [a1 p1];destruct a1.
    + simpl. auto.
    + simpl. split;intros;[discriminate H|].
      destruct H. discriminate H.
Qed.

Lemma all_basic_atoms_conn_pres:forall (atoms:atom_statements) pres,
all_basic (pres) = true ->
all_basic (atoms_conn_pres atoms pres) = true.
Proof.
  intros.
  induction pres.
  - induction atoms;auto.
  - destruct a as [a1 p1];destruct a1;try inv H.
    specialize (IHpres H1).
    induction atoms; auto.
    simpl in *.
    apply all_basic_app in IHpres.
    destruct IHpres as [E1 E2]. rewrite H1 in *. apply all_basic_app.
    split;auto.
Qed.

Theorem soundness: forall 
(P:assert) (Q:ret_assert) (stm: statement) (c_stm: Clight.statement)
(s: split_result),
path_split stm s ->
split_Semax Delta P Q s ->
AClight_to_Clight stm c_stm ->
@semax_aux CS Espec Delta P c_stm Q.
Proof.
  intros. generalize dependent c_stm. 
  generalize dependent P.
  generalize dependent Q.
  induction H.
  + intros. inversion H3.
    apply inj_pair2 in H6. subst.
    pose proof bind_result_add_inv _ _ _ _ _ _ _ H2 H.
    (* Non_empty_Type non empty type is also used here *)
    destruct HX as [? ?].
    apply (H1 x); auto.
  + intros R P Hvalid c_stm Hc. inv Hc.
     eapply semax_aux_seq
      with (Q:=
      EX Q:assert, andp (
        !!
          (Forall (atom_return_to_semax Delta Q (RA_return R)) (return_atom res2)
          /\ Forall (atom_to_semax Delta Q (RA_break R)) (break_atom res2)
          /\ Forall (atom_to_semax Delta Q (RA_continue R)) (continue_atom res2)
          /\ Forall (atom_to_semax Delta Q (RA_normal R)) (normal_atom res2)
          /\ Forall (add_pre_to_semax Delta Q) (pre res2))
        ) Q
      ). 
      
      {
  apply IHpath_split1;[|apply H4].
  destruct Hvalid as [? [? [? [? [? [? [? [? [? ?]]]]]]]]];simpl in *.
  repeat split.
  + apply Forall_app in H2. apply H2.
  + apply Forall_app in H3. apply H3.
  + apply Forall_forall.
    intros.
    eapply add_post_to_semax_derives  with (Q:= EX Q: assert, Q && !!
             (Forall (atom_to_semax _ Q (RA_normal R)) (normal_atom res2) /\
              Forall (atom_to_semax _ Q (RA_break R)) (break_atom res2) /\
          Forall (atom_to_semax _ Q (RA_continue R)) (continue_atom res2) /\
         Forall (atom_return_to_semax _ Q (RA_return R)) (return_atom res2) /\
      Forall (add_pre_to_semax _ Q) (pre res2)
             )).
  
   2:{
      pose proof add_post_to_semax_reverse_group
           x (normal_atom res2) (RA_normal R) as E1.
      assert ( Forall (add_post_to_semax Delta (RA_normal R))
                      (map (post_conn_atom x) (normal_atom res2))) as E1'.
      { apply Forall_forall. intros. eapply Forall_forall in H5.
        apply H5. apply in_or_app. right. unfold posts_conn_atoms.
        apply in_flat_map.
        exists x;auto. }
      specialize (E1 E1');clear E1'.
      pose proof add_post_to_semax_reverse_group
           x (break_atom res2) (RA_break R) as E2.
      assert ( Forall (add_post_to_semax Delta (RA_break R))
                      (map (post_conn_atom x) (break_atom res2))) as E2'.
      { apply Forall_forall. intros. eapply Forall_forall in H7.
        apply H7. apply in_or_app. right.
        apply in_or_app. right. unfold posts_conn_atoms.
        apply in_flat_map.
        exists x;auto. }
      specialize (E2 E2');clear E2'.
      pose proof add_post_to_semax_reverse_group
           x (continue_atom res2) (RA_continue R) as E3.
      assert ( Forall (add_post_to_semax Delta (RA_continue R))
                      (map (post_conn_atom x) (continue_atom res2))) as E3'.
      { apply Forall_forall. intros. eapply Forall_forall in H8.
        apply H8. apply in_or_app. right.
        apply in_or_app. right. unfold posts_conn_atoms.
        apply in_flat_map.
        exists x;auto. }
      specialize (E3 E3');clear E3'.
     pose proof add_return_to_semax_reverse_group
           x (return_atom res2) (RA_return R) as E4.
      assert ( Forall (add_return_to_semax Delta (RA_return R))
         (map
            (fun ret_atom : path * option expr =>
             post_conn_return x (fst ret_atom) (snd ret_atom)) 
            (return_atom res2))) as E4'.
      { apply Forall_forall. intros. eapply Forall_forall in H9.
        apply H9. apply in_or_app. right.
        apply in_or_app. right. unfold posts_conn_returns.
        apply in_flat_map.
        exists x;auto. }
      specialize (E4 E4');clear E4'.
      pose proof path_conn_to_semax_reverse_group'
        x _ _ _ H14 H1 as E5.
      assert (Forall (path_to_semax Delta)
                     (posts_conn_pres (normal_post res1) (pre res2))) as E5'.
      { apply Forall_forall. intros. eapply Forall_forall in H3.
        apply H3. apply in_or_app. right. apply in_or_app. right;auto. }
      specialize (E5 E5');clear E5'.
      pose proof split_not_empty _ _ H0 as E.
      eapply soundness_seq_inv_aux1;auto.
      intros C. apply E. tauto.
    }
    { Intros Q.  destruct R. simpl in *. intros env.
      Exists Q. apply andp_right.
      2:{ apply andp_left2. apply derives_refl. }
      apply prop_right. repeat split;auto. }
  + destruct R. simpl in *.
    apply Forall_app in H7. apply H7.
  + destruct R. simpl in *.
     apply Forall_app in H8. apply H8.
  + destruct R. simpl in *.
    apply Forall_app in H9. apply H9.
  + apply Forall_forall.
    intros.
    eapply atom_to_semax_derives  with (Q1:= EX Q: assert, Q && !!
             (Forall (atom_to_semax _ Q (RA_normal R)) (normal_atom res2) /\
              Forall (atom_to_semax _ Q (RA_break R)) (break_atom res2) /\
          Forall (atom_to_semax _ Q (RA_continue R)) (continue_atom res2) /\
         Forall (atom_return_to_semax _ Q (RA_return R)) (return_atom res2) /\
      Forall (add_pre_to_semax _ Q) (pre res2)
                                       )).
    1:{ apply derives_refl. }
    2:{
      assert(Et: (all_basic (pre res2) = true)   \/ (all_empty_atom (normal_atom res1) = true)).
      { destruct H1 . 
        - left. auto.
        - right. destruct H1. destruct H15. auto. }
      pose proof atom_conn_pres_to_semax_reverse_group3' P
           x _ _ H14 Et as E5. 
      assert (E5': Forall (add_pre_to_semax Delta P)
                          (atoms_conn_pres (normal_atom res1) (pre res2))).
      { apply Forall_forall. intros. eapply Forall_forall in H2.
      apply H2. apply in_or_app. right. auto. }
        specialize (E5 E5');clear E5'.
      pose proof atom_conn_atom_to_semax_reverse_group _ _ _ P _ H10 H14 as E4.
      apply Forall_app in H11.
      pose proof (atom_conn_atom_to_semax_reverse_group
                    _ _ _ P _ (proj2 H11) H14) as E3.
      apply Forall_app in H12.
      pose proof (atom_conn_atom_to_semax_reverse_group
                    _ _ _ P _ (proj2 H12) H14) as E2.
      apply Forall_app in H13.
      pose proof (add_return_to_atom_semax_group _ _ _ P _ (proj2 H13) H14) as E1.
      pose proof split_not_empty _ _ H0 as E.
      eapply soundness_seq_inv_aux2;auto.
      intros C. apply E. tauto.
    }
    { Intros Q.  destruct R. simpl in *. intros env.
      Exists Q. apply andp_right.
      2:{ apply andp_left2. apply derives_refl. }
      apply prop_right. repeat split;auto. }
  + destruct R. simpl in *.
    apply Forall_app in H11. apply H11.
  + destruct R. simpl in *.
    apply Forall_app in H12. apply H12.
  + destruct R. simpl in *.
    apply Forall_app in H13. apply H13.
} (*end of part 1*)
{
  apply IHpath_split2;[|apply H6].
  repeat split;auto;apply Forall_forall;intros.
  - eapply add_pre_to_semax_derives.
    2: { apply add_pre_to_semax_sem. }
    1: { Intros Q. Exists Q.
         apply andp_right.
         + apply prop_right.
           eapply Forall_forall in H9. apply H9. auto.
         + solve_andp.
    }
  -  destruct Hvalid as [? [? [? [? [? [? [? [? [? ?]]]]]]]]].
     simpl in *. eapply Forall_forall in H5.
     apply H5. apply in_or_app. right. apply in_or_app. left. auto.
  - destruct Hvalid as [? [? [? [? [? [? [? [? [? ?]]]]]]]]].
    simpl in *. eapply Forall_forall in H7.
    apply H7. apply in_or_app. left;auto.
  - destruct Hvalid as [? [? [? [? [? [? [? [? [? ?]]]]]]]]].
    simpl in *. eapply Forall_forall in H8.
    apply H8. apply in_or_app. right. apply in_or_app. left;auto.
  - destruct Hvalid as [? [? [? [? [? [? [? [? [? ?]]]]]]]]].
    simpl in *. eapply Forall_forall in H9.
    apply H9. apply in_or_app. right. apply in_or_app. left;auto.
  - destruct Hvalid as [? [? [? [? [? [? [? [? [? ?]]]]]]]]].
    simpl in *. eapply Forall_forall in H10.
    apply H10. apply in_or_app. right. apply in_or_app. left;auto.
  - eapply atom_to_semax_derives.
    3: { apply atom_to_semax_sem. }
    { Intros Q. Exists Q. apply andp_right.
      - apply prop_right. eapply Forall_forall in H8.
        apply H8. auto.
      - apply derives_refl.
    }
    { apply ENTAIL_refl. }
  -  eapply atom_to_semax_derives.
    3: { apply atom_to_semax_sem. }
    { Intros Q. Exists Q. apply andp_right.
      - apply prop_right. eapply Forall_forall in H5.
        apply H5. auto.
      - apply derives_refl.
    }
    { apply ENTAIL_refl. }
  -  eapply atom_to_semax_derives.
    3: { apply atom_to_semax_sem. }
    { Intros Q. Exists Q. apply andp_right.
      - apply prop_right. eapply Forall_forall in H7.
        apply H7. auto.
      - apply derives_refl.
    }
    { apply ENTAIL_refl. }
  - eapply atom_return_to_semax_derives.
    3: { apply atom_return_to_semax_sem. }
    { Intros Q. Exists Q. apply andp_right.
      - apply prop_right. eapply Forall_forall in H3.
        apply H3. auto.
      - apply derives_refl.
    }
    { intros. apply ENTAIL_refl. }
}


  + (* Basic Case *)
    intros. inv H; inv H1; destruct H0 as [? [? [? [? [? [? [? [? [? ?]]]]]]]]];
              destruct Q as [Qn Qb Qc Qr];
              unfold RA_normal, RA_break, RA_continue, RA_return in *;
    simpl in *.
    - inv H5. rename H11 into H5. 
      apply semax_aux_seq_skip in H5.
      eapply semax_aux_post_simple;[..|apply H5].       
      * apply derives_refl.
      * apply derives_extract_PROP'. intros C. destruct C.
      * apply derives_extract_PROP'. intros C. destruct C.
      * intros. apply derives_extract_PROP'. intros C. destruct C.
    - inv H5. rename H11 into H5. 
      apply semax_aux_seq_skip in H5.
      eapply semax_aux_post_simple;[..|apply H5];
        unfold RA_normal, RA_break, RA_continue, RA_return in *.
      * apply derives_refl.
      * apply derives_extract_PROP'. intros C. destruct C.
      * apply derives_extract_PROP'. intros C. destruct C.
      * intros. apply derives_extract_PROP'. intros C. destruct C.
    - inv H1. rename H11 into H9. simpl in H9.
      inv H. rename H11 into H1. simpl in H1.
      econstructor;[..|apply H9].
      * eapply semax_aux_skip_inv in H1. unfold RA_normal in H1.
        eapply derives_trans;[|apply H1]. solve_andp.
      * unfold RA_normal. apply derives_aux_refl.
      * unfold RA_break. 
        apply andp_left2. apply andp_left2.
        apply derives_extract_PROP'. intros C;destruct C.
      * unfold RA_continue.
        apply andp_left2. apply andp_left2.
        apply derives_extract_PROP'. intros C;destruct C.
      * unfold RA_return. intros.
        apply andp_left2. apply andp_left2.
        apply derives_extract_PROP'. intros C;destruct C.
    - inv H7. rename H11 into H7.
      eapply semax_aux_conseq.
      { apply semax_aux_skip_inv in H7.
        eapply derives_trans;[|apply H7]. solve_andp. }
      { apply derives_aux_refl. }
      { apply derives_aux_refl. }
      { apply derives_aux_refl. }
      { intros. apply derives_aux_refl. }
      { unfold RA_normal. 
        replace Qc with (
          RA_continue {| RA_normal := Qn; RA_break := Qb; RA_continue := Qc; RA_return := Qr |}
        ) by reflexivity.
        apply semax_aux_continue. }
    - inv H6. rename H11 into H6.
      eapply semax_aux_conseq.
      { apply semax_aux_skip_inv in H6.
        eapply derives_trans;[|apply H6]. solve_andp. }
      { apply derives_aux_refl. }
      { apply derives_aux_refl. }
      { apply derives_aux_refl. }
      { intros. apply derives_aux_refl. }
      { unfold RA_normal. 
        replace Qb with (
          RA_break {| RA_normal := Qn; RA_break := Qb; RA_continue := Qc; RA_return := Qr |}
        ) by reflexivity.
        apply semax_aux_break. }
    - inv H5. rename H11 into H5.
      eapply semax_aux_conseq;[..|apply semax_aux_skip];unfold normal_ret_assert, RA_normal,
      RA_return,RA_break,RA_continue.
      { apply semax_aux_skip_inv in H5.
        eapply derives_trans;[|apply H5]. solve_andp. }
      { apply derives_aux_refl. }
      { apply andp_left2.
        apply derives_extract_prop'. intros C;destruct C. }
      { apply andp_left2.
        apply derives_extract_prop'. intros C;destruct C. }
      { intros. apply andp_left2.
        apply derives_extract_prop'. intros C;destruct C. }
    - inv H8. rename H11 into H9.
      apply semax_aux_skip_seq in H9.
      eapply semax_aux_conseq;[..|apply H9];unfold normal_ret_assert, RA_normal,
      RA_return,RA_break,RA_continue.
      { apply derives_aux_refl. }
      { apply andp_left2.
        apply derives_extract_PROP. intros C;destruct C. }
      { apply andp_left2.
        apply derives_extract_PROP. intros C;destruct C. }
      { apply andp_left2.
        apply derives_extract_PROP. intros C;destruct C. }
      { intros. apply derives_aux_refl. }
    - inv H5. rename H11 into H5. apply semax_aux_seq_skip in H5.
      eapply semax_aux_conseq;[..|apply H5];unfold normal_ret_assert, RA_normal,
      RA_return,RA_break,RA_continue;try apply derives_aux_refl.
      { apply andp_left2.
        apply derives_extract_PROP. intros C;destruct C. }
      { apply andp_left2.
        apply derives_extract_PROP. intros C;destruct C. }
      { intros. apply andp_left2.
        apply derives_extract_PROP. intros C;destruct C. }
+ intros.
  inv H2.
  eapply semax_aux_conseq with (P':= (!! ((bool_type (typeof a)) = true)) &&
   (tc_expr Delta (Eunop Onotbool a (Tint I32 Signed noattr))) &&
  (
    !! (split_Semax Delta (P && local (liftx (typed_true (typeof a)) (eval_expr a))) Q res1 /\ 
    split_Semax Delta (P && local (liftx (typed_false (typeof a)) (eval_expr a))) Q res2
  ) && P)) (R':= Q); try (intros;apply derives_aux_refl).
  2:{ rewrite andp_assoc.
      apply aux_semax_extract_prop. intros.
      rewrite andp_comm. rewrite andp_assoc. 
      apply aux_semax_extract_prop.
      intros [E1 E2].
      eapply semax_aux_pre'.
      2:{ eapply semax_aux_ifthenelse;auto.
      + apply IHpath_split1. apply E1. auto.
      + apply IHpath_split2. apply E2. auto. }
      repeat apply andp_right;try solve_andp.
      apply prop_right. auto. }
    assert (exists c1' c2' Q', semax_aux Delta P (Clight.Sifthenelse a c1' c2') Q').
    { destruct res1 as [pre1 path1 normal_post1 break_post1
                        continue_post1 return_post1 normal_atom1
                        break_atom1 continue_atom1 return_atom1].
      hnf in H1; simpl in H1; destruct H1 as 
      [S1 [S2 [S3 [S4 [S5 [S6 [S7 [S8 [S9 S10]]]]]]]]].
      apply Forall_app in S1. apply proj1 in S1.
      destruct pre1 as [|pre' pre1].
      2:{ apply Forall_inv in S1. apply add_exp_to_pre_tc in S1. auto. }
      apply Forall_app in S7. apply proj1 in S7.
      destruct normal_atom1 as [|normal_atom' normal_atom1].
      2:{ apply Forall_inv in S7. apply add_exp_to_atom_tc in S7. auto. }
      apply Forall_app in S8. apply proj1 in S8.
      destruct continue_atom1 as [|continue_atom' continue_atom1].
      2:{ apply Forall_inv in S8. apply add_exp_to_atom_tc in S8. auto. }
      apply Forall_app in S9. apply proj1 in S9.
      destruct break_atom1 as [|break_atom' break_atom1].
      2:{ apply Forall_inv in S9. apply add_exp_to_atom_tc in S9. auto. }
      apply Forall_app in S10. apply proj1 in S10.
      destruct return_atom1 as [|return_atom' return_atom1].
      2:{ apply Forall_inv in S10. apply add_exp_to_return_atom_tc in S10. auto. }
      apply split_not_empty in H. exfalso. apply H. auto. }
  destruct H2 as [c1' [c2' [Q' H2]]].
  apply semax_aux_ifthenelse_inv in H2.
  assert (ENTAIL Delta, allp_fun_id Delta && P 
          |-- tc_expr Delta  (Eunop Onotbool a (Tint I32 Signed noattr))) as E1.
  { eapply derives_trans;[apply H2|].
    solve_andp. }
    assert (ENTAIL Delta, allp_fun_id Delta && P 
    |-- !! (bool_type (typeof a) = true)) as E2.
  { simpl. intros env.
    simpl in H2. specialize (H2 env).
    eapply derives_trans;[apply H2|].
    solve_andp. }
  pose proof andp_right _ _ _ E1 E2.
  apply add_andp in H3.
  rewrite H3.
  apply andp_right;[solve_andp|].
  apply andp_right;[|solve_andp].
  apply prop_right.
  hnf in H1. simpl in H1.
  destruct H1 as [S1 [S2 [S3 [S4 [S5 [S6 [S7 [S8 [S9 S10]]]]]]]]].
  repeat split.
  - apply Forall_forall. intros. apply add_exp_to_pre_inv.
    eapply Forall_forall in S1. apply S1.
    apply in_or_app. left.
    apply add_exp_to_pres_list_in. auto.
  - apply Forall_forall. intros.
    eapply Forall_forall in S2. apply S2.
    apply in_or_app. auto.
  - apply Forall_forall. intros.
    eapply Forall_forall in S3. apply S3.
    apply in_or_app. auto.
  - apply Forall_forall. intros. 
    eapply Forall_forall in S4. apply S4.
    apply in_or_app. auto.
  - apply Forall_forall. intros.
    eapply Forall_forall in S5. apply S5.
    apply in_or_app. auto.
  - apply Forall_forall. intros.
    eapply Forall_forall in S6. apply S6.
    apply in_or_app. auto.
  - apply Forall_forall. intros.
    eapply Forall_forall in S7.
    apply add_exp_to_atom_inv. apply S7.
    apply in_or_app. left. apply add_exp_to_atoms_list_in. auto.
  - apply Forall_forall. intros.
    eapply Forall_forall in S8.
    apply add_exp_to_atom_inv. apply S8.
    apply in_or_app. left. apply add_exp_to_atoms_list_in. auto.
  - apply Forall_forall. intros.
    eapply Forall_forall in S9.
    apply add_exp_to_atom_inv. apply S9.
    apply in_or_app. left. apply add_exp_to_atoms_list_in. auto.
  - apply Forall_forall. intros.
    eapply Forall_forall in S10.
    apply add_exp_to_return_atom_inv. apply S10.
    apply in_or_app. left.
    apply add_exp_to_return_atoms_list_in. auto.
  - apply Forall_forall. intros.
    apply add_exp_to_pre_inv_false.
    eapply Forall_forall in S1. apply S1.
    apply in_or_app. right.
    apply add_exp_to_pres_list_in. auto.
  - apply Forall_forall. intros.
    eapply Forall_forall in S2. apply S2.
    apply in_or_app. auto.
  - apply Forall_forall. intros.
    eapply Forall_forall in S3. apply S3.
    apply in_or_app. auto.
  - apply Forall_forall. intros. 
    eapply Forall_forall in S4. apply S4.
    apply in_or_app. auto.
  - apply Forall_forall. intros.
    eapply Forall_forall in S5. apply S5.
    apply in_or_app. auto.
  - apply Forall_forall. intros.
    eapply Forall_forall in S6. apply S6.
    apply in_or_app. auto.
  - apply Forall_forall. intros.
    eapply Forall_forall in S7.
    apply add_exp_to_atom_inv_false. apply S7.
    apply in_or_app. right. apply add_exp_to_atoms_list_in. auto.
  - apply Forall_forall. intros.
    eapply Forall_forall in S8.
    apply add_exp_to_atom_inv_false. apply S8.
    apply in_or_app. right. apply add_exp_to_atoms_list_in. auto.
  - apply Forall_forall. intros.
    eapply Forall_forall in S9.
    apply add_exp_to_atom_inv_false. apply S9.
    apply in_or_app. right. apply add_exp_to_atoms_list_in. auto.
  - apply Forall_forall. intros.
    eapply Forall_forall in S10.
    apply add_exp_to_return_atom_inv_false. apply S10.
    apply in_or_app. right.
    apply add_exp_to_return_atoms_list_in. auto.


+ (** Loop *)
  simpl. rewrite !app_nil_r. intros.
  hnf in H1;simpl in H1. destruct H1 as [S1 [S2 [S3 [_ [_ [S4 [_ [_ [_ _]]]]]]]]].
  inv S1. clear H5. simpl in H4. rename H4 into H3.
  apply semax_aux_skip_inv in H3. unfold RA_normal in H3.
  assert (H3':ENTAIL Delta, (allp_fun_id Delta && P)
  |-- inv1).
  { eapply derives_trans;[|apply H3];solve_andp. }
  eapply semax_aux_conseq with (R':=Q);[apply H3'|..];intros;try apply derives_aux_refl.
  inv H2. eapply semax_aux_loop with (Q':= inv2).
  { apply IHpath_split1;auto. destruct Q as [Qn Qb Qc Qr]. 
    pose proof (split_not_empty_incr _ _ Econt_atom H0) as E.
    repeat split;unfold loop1_ret_assert, loop2_ret_assert, RA_normal, RA_break, RA_continue, RA_return in *.
    - apply split_loop_inv1_conn_pre1_inv. in_split_result S2.
    - in_split_result S2.
    - apply pack_assert_into_post_group. simpl.
      rewrite app_nil_r. in_split_result S2.
    - in_split_result S3.
    - apply pack_assert_into_post_group. simpl.
      rewrite app_nil_r. in_split_result S2.
    - in_split_result S4.
    - apply pack_assert_into_atom_group. in_split_result S2.
    - apply pack_assert_into_atom_half_group. 
      simpl. rewrite app_nil_r. in_split_result S3.
    - apply pack_assert_into_atom_group. in_split_result S2.
    - apply pack_assert_into_ret_atom_half_group.
      simpl. rewrite app_nil_r. in_split_result S4.
  }
  { apply IHpath_split2;auto. destruct Q as [Qn Qb Qc Qr]. 
    repeat split;unfold loop1_ret_assert, loop2_ret_assert, RA_normal, RA_break, RA_continue, RA_return in *.
    - apply split_loop_inv1_conn_pre1_inv. in_split_result S2.
    - in_split_result S2.
    - apply pack_assert_into_post_group. simpl.
      rewrite app_nil_r.  in_split_result S2.
    - in_split_result S3.
    - destruct (continue_post res2);[constructor|]. inv Econt_post.
    - in_split_result S4.
    - apply pack_assert_into_atom_group. in_split_result S2.
    - apply pack_assert_into_atom_half_group. 
      simpl. rewrite app_nil_r. in_split_result S3.
    - destruct (continue_atom res2);[constructor|]. inv Econt_atom.
    - apply pack_assert_into_ret_atom_half_group.
      simpl. rewrite app_nil_r. in_split_result S4.
  }

+ (* one loop invariant.*)
  simpl. rewrite !app_nil_r. intros. 
  hnf in H1;simpl in H1. destruct H1 as [S1 [S2 [S3 [_ [_ [S4 [_ [_ [_ _]]]]]]]]].
  inv S1. clear H5. simpl in H4. rename H4 into H3.
  apply semax_aux_skip_inv in H3. unfold RA_normal in H3.
  assert (H3':ENTAIL Delta, (allp_fun_id Delta && P)
  |-- inv).
  { eapply derives_trans;[|apply H3];solve_andp. }
  eapply semax_aux_conseq with (R':=Q);[apply H3'|..];intros;try apply derives_aux_refl.
  inv H2.  eapply semax_aux_loop with (Q':=
    EX Q':assert, andp Q' (
      !!
        ( Forall (add_pre_to_semax Delta Q') (pre res2) /\
          Forall (atom_to_semax Delta Q' inv) (normal_atom res2) /\
          Forall (atom_return_to_semax Delta Q' (RA_return Q)) (return_atom res2) /\
          Forall (atom_to_semax Delta Q' (RA_normal Q)) (break_atom res2))
      )
  ).
  { apply IHpath_split1;auto. destruct Q as [Qn Qb Qc Qr]. 
    pose proof (split_not_empty_incr _ _ Econt_atom H0) as E.
    repeat split;unfold loop1_ret_assert, loop2_ret_assert, RA_normal, RA_break, RA_continue, RA_return in *.
    - apply split_loop_inv1_conn_pre1_inv. in_split_result S2.
    - in_split_result S2.
    - apply split_loop_normal_post1_conn_wp_inv;auto.
      + in_split_result S2.
      + in_split_result S2.
      + in_split_result S3.
      + in_split_result S4.
    - in_split_result S3.
    - apply split_loop_continue_post1_conn_wp_inv;auto.
      + in_split_result S2.
      + in_split_result S2.
      + in_split_result S3.
      + in_split_result S4.
    - in_split_result S4.
    - apply split_loop_normal_atoms1_conn_wp_inv;auto.
      + in_split_result S2.
      + in_split_result S2.
      + simpl. rewrite app_nil_r. in_split_result S4.
      + simpl. rewrite app_nil_r. in_split_result S3.
    - apply split_loop_inv1_conn_break_atoms1_inv.
      simpl. rewrite app_nil_r. in_split_result S3.
    - apply split_loop_continue_atoms1_conn_wp_inv;auto.
      + in_split_result S2.
      + in_split_result S2.
      + simpl. rewrite app_nil_r. in_split_result S3.
      + simpl. rewrite app_nil_r. in_split_result S4.
    - apply split_loop_inv1_conn_return_atoms1_inv.
      simpl. rewrite app_nil_r. in_split_result S4.
  }
  { apply IHpath_split2;auto. destruct Q as [Qn Qb Qc Qr].
    repeat split;unfold loop1_ret_assert, loop2_ret_assert, RA_normal, RA_break, RA_continue, RA_return in *.
    - eapply Forall_forall. intros. eapply add_pre_to_semax_derives.
      2: { apply add_pre_to_semax_sem. } 
      1: { Intros Q. Exists Q.
           apply andp_right.
            + apply prop_right. 
              eapply Forall_forall in H2. apply H2. auto.
            + solve_andp.
         }
    - in_split_result S2.
    - apply split_loop_inv1_conn_normal_posts1_inv.
      simpl. rewrite app_nil_r. in_split_result S2. 
    - in_split_result S3.
    - rewrite Econt_post. constructor.
    - in_split_result S4.
    - apply Forall_forall. intros. eapply atom_to_semax_derives.
      3: { apply atom_to_semax_sem. }
      2: { apply ENTAIL_refl. }
      1: { Intros Q. Exists Q. apply andp_right;[|apply derives_refl].
           apply prop_right. eapply Forall_forall in H4;[|apply H1]. auto. } 
    - apply Forall_forall. intros. eapply atom_to_semax_derives.
      3: { apply atom_to_semax_sem. }
      2: { apply ENTAIL_refl. }
      1: { Intros Q. Exists Q. apply andp_right;[|apply derives_refl].
          apply prop_right. eapply Forall_forall in H6;[|apply H1]. auto. }
    - rewrite Econt_atom. constructor.
    - apply Forall_forall. intros. eapply atom_return_to_semax_derives.
      3: { apply atom_return_to_semax_sem. }
      2: { intros. apply ENTAIL_refl. }
      1: { Intros Q. Exists Q. apply andp_right;[|apply derives_refl].
          apply prop_right. eapply Forall_forall in H5;[|apply H1]. auto. }
  }
  + (* loop with null loop invariant *)
  { simpl. intros.
    hnf in H4;simpl in H4. destruct H4 as (S1 & S2 & S3 & _ & _ & S4 & S5 & _ & _ & S6).
    (* Print semax_aux_conseq.
    Check semax_aux_conseq. *)
    eapply semax_aux_conseq with (P':= 
     EX Q':assert, andp Q' (
      !!
        ( Forall (add_pre_to_semax Delta Q') (pre res1) /\
          Forall (add_pre_to_semax Delta Q') (atoms_conn_pres (normal_atom res1) (pre res2))  /\
          Forall (add_pre_to_semax Delta Q') (atoms_conn_pres (continue_atom res1) (pre res2)) /\
          Forall (atom_return_to_semax Delta Q' (RA_return Q)) (return_atom res1) /\
          Forall (atom_to_semax Delta Q' (RA_normal Q)) (break_atom res1) /\ 
          Forall (atom_to_semax Delta Q' (RA_normal Q)) (atoms_conn_atoms (normal_atom res1) (break_atom res2)) /\

          Forall (atom_to_semax Delta Q' (RA_normal Q)) (atoms_conn_atoms (continue_atom res1) (break_atom res2)) /\
          Forall (atom_return_to_semax Delta Q' (RA_return Q)) (atoms_conn_returns (normal_atom res1) (return_atom res2)) /\

          Forall (atom_return_to_semax Delta Q' (RA_return Q)) (atoms_conn_returns (continue_atom res1) (return_atom res2))
      )) ); try apply derives_aux_refl. 
    2:{ intros. apply derives_aux_refl. } (* this is trivial*)
    1:{ (* {P} c {inv1} *)
      Exists P. repeat apply andp_right;try solve_andp.
      apply prop_right. 
      repeat split;try in_split_result S1;try in_split_result S2;try in_split_result S3;
        try in_split_result S4;try in_split_result S5;try in_split_result S6.
    }
    inv H5. destruct Q as [Qn Qb Qc Qr].
    eapply semax_aux_loop with (Q':=
    EX Q'':assert, andp Q'' (
      !!
        ( Forall (add_pre_to_semax Delta Q'') (pre res2) /\
          Forall (add_pre_to_semax Delta Q'') (atoms_conn_pres (normal_atom res2) (pre res1))/\
          Forall (atom_return_to_semax Delta Q'' Qr) (return_atom res2) /\
          Forall (atom_to_semax Delta Q'' Qn) (break_atom res2)/\
          Forall (atom_to_semax Delta Q'' (Qn )) (atoms_conn_atoms (normal_atom res2) (break_atom res1)) /\
          Forall (atom_return_to_semax Delta Q'' (Qr)) (atoms_conn_returns (normal_atom res2) (return_atom res1))) 
      )); unfold loop1_ret_assert, loop2_ret_assert, RA_normal, RA_break,
          RA_continue, RA_return in *.
    { (* inv1 c1 inv2 *)
      apply IHpath_split1;auto. 
      repeat split;unfold RA_normal, RA_break,
        RA_continue, RA_return.
      - apply Forall_forall. intros.
        eapply add_pre_to_semax_derives.
        2:{ apply add_pre_to_semax_sem. }
        Intros Q'. Exists Q'. apply andp_right;try solve_andp.
        apply prop_right. eapply Forall_forall in H5.
        apply H5. auto.
      - in_split_result S2.
      - {
        eapply Forall_forall. intros. 
        assert (Enpe :(normal_post res1) <> nil). 
        {destruct (normal_post res1);try discriminate. exfalso. eauto. }
        eapply soundness_null_aux1;eauto.
        + assert ( T1: ~ (pre res2 = [] /\ normal_atom res2 = [] /\ break_atom res2 = [] /\ continue_atom res2 = [] /\ return_atom res2 = [])).
        { apply split_not_empty with stm2. eauto. }
        rewrite Econt_atom in T1. intro T. apply T1. repeat split;try apply T. destruct H;eauto.
         destruct T as (_ & T & _).  apply atoms_conn_pres_nil in T. destruct T;eauto. exfalso;eauto.
        + intros. 
          apply path_conn_to_semax_reverse_group4 with (normal_post res1);eauto.
          in_split_result S2.
       + intros.
         apply path_conn_to_semax_reverse_group4 with (normal_post res1);eauto.
         ++ apply all_basic_atoms_conn_pres;eauto.
         ++ assert (Forall (path_to_semax Delta) (posts_conn_pres (posts_conn_atoms (normal_post res1) (normal_atom res2)) (pre res1))) .
            { in_split_result S2. } 
            pose proof conn_assoc1.
            eapply Forall_forall. intros.
            apply conn_assoc1 in H8;eauto. 
            eapply Forall_forall in H6. apply H6. auto.
       + intros. 
        apply add_post_to_semax_reverse_group2 with (normal_post res1);auto.
        in_split_result S3.
       + intros. 
       apply add_return_to_semax_reverse_group2 with (normal_post res1);auto.
       in_split_result S4.
       + apply add_post_to_semax_reverse_group2 with (normal_post res1);auto.
         in_split_result S3.
       + apply add_return_to_semax_reverse_group2 with (normal_post res1);auto.
       in_split_result S4.
      }  
      - in_split_result S3.
      - eapply Forall_forall. intros. 
        assert (Enpe :(continue_post res1) <> nil). 
        {destruct (continue_post res1);try discriminate. exfalso. eauto. }
        eapply soundness_null_aux1;eauto.
        + assert ( T1: ~ (pre res2 = [] /\ normal_atom res2 = [] /\ break_atom res2 = [] /\ continue_atom res2 = [] /\ return_atom res2 = [])).
        { apply split_not_empty with stm2. eauto. }
        rewrite Econt_atom in T1. intro T. apply T1. repeat split;try apply T. destruct H;eauto.
         destruct T as (_ & T & _).  apply atoms_conn_pres_nil in T. destruct T;eauto. exfalso;eauto.
        + intros. 
          apply path_conn_to_semax_reverse_group4 with (continue_post res1);eauto.
          in_split_result S2.
       + intros.
         apply path_conn_to_semax_reverse_group4 with (continue_post res1);eauto.
         ++ apply all_basic_atoms_conn_pres;eauto.
         ++ assert (Forall (path_to_semax Delta) (posts_conn_pres (posts_conn_atoms (continue_post res1) (normal_atom res2)) (pre res1))) .
            { in_split_result S2. }          
            pose proof conn_assoc1.
            eapply Forall_forall. intros.
            apply conn_assoc1 in H8;eauto. 
            eapply Forall_forall in H6. apply H6. auto.
       + intros. 
        apply add_post_to_semax_reverse_group2 with (continue_post res1);auto.
        in_split_result S3.
       + intros. 
       apply add_return_to_semax_reverse_group2 with (continue_post res1);auto.
       in_split_result S4. 
       + apply add_post_to_semax_reverse_group2 with (continue_post res1);auto.
         in_split_result S3.
       + apply add_return_to_semax_reverse_group2 with (continue_post res1);auto.
       in_split_result S4.
      - in_split_result S4.
      - apply Forall_forall. intros.
        apply aux_semax_extract_exists.
        intros inv.
        rewrite andp_comm. apply aux_semax_extract_prop.
        intros.
        assert(Enr2: normal_atom res2 = []).
        { destruct H;eauto. 
          assert (normal_atom res1 <> []). { intro. rewrite H6 in H4. inversion H4. }
          exfalso. apply H6; destruct H. eauto.
        }
        assert (Easy: atom_to_semax Delta inv  ( EX Q'' : assert,
               Q'' &&
               !! (Forall (add_pre_to_semax Delta Q'') (pre res2) /\
                   Forall (add_pre_to_semax Delta Q'') (atoms_conn_pres (normal_atom res2) (pre res1)) /\
                   Forall (atom_return_to_semax Delta Q'' Qr) (return_atom res2) /\
                   Forall (atom_to_semax Delta Q'' Qn) (break_atom res2)/\
                   Forall (atom_to_semax Delta Q'' Qn) (atoms_conn_atoms (normal_atom res2) (break_atom res1)) /\
                   Forall (atom_return_to_semax Delta Q'' Qr) (atoms_conn_returns (normal_atom res2) (return_atom res1))
                   
                   ) )(x)).
         { 
          eapply soundness_null_aux2;eauto. 
          +   assert ( T1: ~ (pre res2 = [] /\ normal_atom res2 = [] /\ break_atom res2 = [] /\ continue_atom res2 = [] /\ return_atom res2 = [])).
            { apply split_not_empty with stm2. eauto. } intro.
            destruct H6 as (PT1 & PT2&PT3&PT4 & PT5 &PT6). 
            apply atoms_conn_pres_nil in PT4.
            destruct PT4;eauto.
          + intros.
            apply atom_conn_atom_to_semax_reverse_group with (normal_atom res1);eauto.
            destruct H5 as (G1 & G2 & G3 & G4 & G5 &G6 & G7 & G8 &G9). 
            in_split_result G6;eauto.
          + intros.
            eapply add_return_to_atom_semax_group with (normal_atom res1);eauto.
            destruct H5 as (G1 & G2 & G3 & G4 & G5 &G6 & G7 & G8 &G9). 
            in_split_result G8;eauto. 
          + intros.
            apply atom_conn_pres_to_semax_reverse_group3' with (normal_atom res1);eauto.
            destruct H5 as (G1 & G2 & G3 & G4 & G5 &G6 & G7 & G8 &G9). 
            in_split_result G2;eauto. 
          + intros.
            apply atom_conn_pres_to_semax_reverse_group3' with (normal_atom res1);eauto.
            left. apply all_basic_atoms_conn_pres. auto.
            assert (EMP1 :(atoms_conn_pres (normal_atom res1) (atoms_conn_pres (normal_atom res2) (pre res1))) = []).
           { destruct H. 
            - destruct H. rewrite H . simpl. auto.
            - rewrite H. simpl. induction (normal_atom res1) ;eauto. apply atoms_conn_pres_nil. right. auto. 
           }
          rewrite EMP1. auto.
          + intros.
            apply atom_conn_atom_to_semax_reverse_group with (normal_atom res1);eauto.
            destruct H.
             * destruct H. rewrite H. simpl.
               apply Forall_nil.
             * rewrite H. simpl.
               assert ( (atoms_conn_atoms (normal_atom res1) (@nil (list (sum expr atom_statement)))) = []).
                 {  rewrite atoms_conn_atoms_nil. right. auto. }
               rewrite H7. apply Forall_nil.
          + intros.
            eapply add_return_to_atom_semax_group with (normal_atom res1);eauto.
            destruct H.
             * destruct H. rewrite H. simpl.
               apply Forall_nil.
             * rewrite H. simpl.
                 assert ((atoms_conn_returns (normal_atom res1) (@nil (prod (list (sum expr atom_statement)) (option expr))))= (@nil (prod (list (sum expr atom_statement)) (option expr)))). 
                 {  rewrite atoms_conn_returns_nil. right. auto. }
               rewrite H7. apply Forall_nil.
            }
            apply Easy.
      - apply Forall_forall. intros.
        eapply atom_to_semax_derives_pre.
        2:{ apply atom_to_semax_sem. }
        Intros Q'. Exists Q'. apply andp_right;try solve_andp.
        apply prop_right. eapply Forall_forall in H11.
        apply H11. auto.
      - apply Forall_forall. intros.
        apply aux_semax_extract_exists.
        intros inv.
        rewrite andp_comm. apply aux_semax_extract_prop.
        intros.
        assert(Enr2: normal_atom res2 = []).
        { destruct H;eauto. 
          assert (continue_atom res1 <> []). {   intro. rewrite H6 in H4. inversion H4. }
          exfalso.
         apply H6; destruct H. eauto.
        } 
        assert (Easy: atom_to_semax Delta inv  ( EX Q'' : assert,
               Q'' &&
               !! (Forall (add_pre_to_semax Delta Q'') (pre res2) /\
                   Forall (add_pre_to_semax Delta Q'') (atoms_conn_pres (normal_atom res2) (pre res1)) /\
                   Forall (atom_return_to_semax Delta Q'' Qr) (return_atom res2) /\
                   Forall (atom_to_semax Delta Q'' Qn) (break_atom res2)/\
                  Forall (atom_to_semax Delta Q'' Qn) (atoms_conn_atoms (normal_atom res2) (break_atom res1)) /\
                   Forall (atom_return_to_semax Delta Q'' Qr) (atoms_conn_returns (normal_atom res2) (return_atom res1))
                   ) )(x)).
         { 
          eapply soundness_null_aux2;eauto. 
          +   assert ( T1: ~ (pre res2 = [] /\ normal_atom res2 = [] /\ break_atom res2 = [] /\ continue_atom res2 = [] /\ return_atom res2 = [])).
            { apply split_not_empty with stm2. eauto. } intro.
            destruct H6 as (PT1 & PT2&PT3&PT4 & PT5 &PT6). 
            apply atoms_conn_pres_nil in PT4.
            destruct PT4;eauto.
          + intros.
            apply atom_conn_atom_to_semax_reverse_group with (continue_atom res1);eauto.
            destruct H5 as (G1 & G2 & G3 & G4 & G5 &G6 & G7 & G8 &G9). 
            in_split_result G7;eauto.
        + intros.
          eapply add_return_to_atom_semax_group with (continue_atom res1);eauto.
          destruct H5 as (G1 & G2 & G3 & G4 & G5 &G6 & G7 & G8 &G9). 
          in_split_result G9;eauto. 
       + intros.
         apply atom_conn_pres_to_semax_reverse_group3' with (continue_atom res1);eauto.
          destruct H5 as (G1 & G2 & G3 & G4 & G5 &G6 & G7 & G8 &G9). 
          in_split_result G3;eauto. 
       + intros.
         apply atom_conn_pres_to_semax_reverse_group3' with (continue_atom res1);eauto.
         left. apply all_basic_atoms_conn_pres. auto.
         assert (EMP1 :(atoms_conn_pres (continue_atom res1) (atoms_conn_pres (normal_atom res2) (pre res1))) = []).
         { destruct H. 
          - destruct H. rewrite H7 . simpl. auto.
          - rewrite H. simpl. induction (continue_atom res1) ;eauto. apply atoms_conn_pres_nil. right. auto. 
         }
         rewrite EMP1. auto.
         + intros.
            apply atom_conn_atom_to_semax_reverse_group with (continue_atom res1);eauto.
            destruct H.
             * destruct H. rewrite H7. simpl.
               apply Forall_nil.
             * rewrite H. simpl.
               assert ( (atoms_conn_atoms (continue_atom res1) (@nil (list (sum expr atom_statement)))) = []).
                 {  rewrite atoms_conn_atoms_nil. right. auto. }
               rewrite H7. apply Forall_nil.
        + intros.
          eapply add_return_to_atom_semax_group with (continue_atom res1);eauto.
          destruct H.
           * destruct H. rewrite H7. simpl.
             apply Forall_nil.
           * rewrite H. simpl.
               assert ((atoms_conn_returns (continue_atom res1) (@nil (prod (list (sum expr atom_statement)) (option expr))))= (@nil (prod (list (sum expr atom_statement)) (option expr)))). 
               {  rewrite atoms_conn_returns_nil. right. auto. }
               rewrite H7. apply Forall_nil.
       }
        apply Easy.
      - apply Forall_forall. intros.
        eapply atom_return_to_semax_derives_pre.
        2:{ apply atom_return_to_semax_sem. }
        Intros Q'. Exists Q'. apply andp_right;try solve_andp.
        apply prop_right. eapply Forall_forall in H8.
        apply H8. auto.
    }
   {  (* inv2 c2 Q *)
      apply IHpath_split2;auto. 
      repeat split;unfold RA_normal, RA_break,
        RA_continue, RA_return.
      - apply Forall_forall. intros.
        eapply add_pre_to_semax_derives.
        2:{ apply add_pre_to_semax_sem. }
        Intros Q'. Exists Q'. apply andp_right;try solve_andp.
        apply prop_right. eapply Forall_forall in H5.
        apply H5. auto.
      - in_split_result S2.
      - eapply Forall_forall . intros. 
        {
        eapply soundness_null_aux3.
          + intro.
            destruct H5. auto.
          + intros.
            (* Check path_conn_to_semax_reverse_group4. *)
            apply path_conn_to_semax_reverse_group4 with (normal_post res2);eauto.
            in_split_result S2.
          + intros.
            apply path_conn_to_semax_reverse_group4 with (normal_post res2);eauto.
            apply all_basic_atoms_conn_pres;auto.
            assert (Forall (path_to_semax Delta) (posts_conn_pres (posts_conn_atoms (normal_post res2) (normal_atom res1)) (pre res2))).
            { in_split_result S2. }
            apply Forall_forall. intros. rewrite Forall_forall in H6. apply H6;auto.
            pose proof conn_assoc1. apply H8;auto.
          + intros.
            apply path_conn_to_semax_reverse_group4' with (normal_post res2);eauto.
            apply all_basic_atoms_conn_pres;auto.
            assert (Forall (path_to_semax Delta) (posts_conn_pres (posts_conn_atoms (normal_post res2) (continue_atom res1)) (pre res2))).
            { in_split_result S2. }
            apply Forall_forall. intros. rewrite Forall_forall in H6. apply H6;auto.
            pose proof conn_assoc1. apply H8;auto.
          + intros.
            apply add_return_to_semax_reverse_group2 with (normal_post res2);eauto. in_split_result S4.
          + intros.
            apply add_post_to_semax_reverse_group2 with (normal_post res2);eauto. in_split_result S3.
          + intros.
            apply add_post_to_semax_reverse_group2 with (normal_post res2);eauto. in_split_result S3.
          + intros.
            apply add_post_to_semax_reverse_group2 with (normal_post res2);eauto. in_split_result S3.
          + intros.
            apply add_return_to_semax_reverse_group2 with (normal_post res2);eauto. in_split_result S4.
          + intros.
            apply add_return_to_semax_reverse_group2 with (normal_post res2);eauto. in_split_result S4.
        }
      - in_split_result S3;eauto. 
      - rewrite Econt_post. constructor.
      - in_split_result S4.  
      - apply Forall_forall. intros.
        apply aux_semax_extract_exists. intros inv.
        rewrite andp_comm. apply aux_semax_extract_prop.
        intros. 
        assert(Easy: atom_to_semax Delta inv (EX Q' : assert,
               Q' &&
               !! (Forall (add_pre_to_semax Delta Q') (pre res1) /\
                   Forall (add_pre_to_semax Delta Q') (atoms_conn_pres (normal_atom res1) (pre res2)) /\
                   Forall (add_pre_to_semax Delta Q') (atoms_conn_pres (continue_atom res1) (pre res2)) /\
                   Forall (atom_return_to_semax Delta Q' Qr) (return_atom res1) /\
                   Forall (atom_to_semax Delta Q' Qn) (break_atom res1) /\
                   Forall (atom_to_semax Delta Q' Qn) (atoms_conn_atoms (normal_atom res1) (break_atom res2)) /\
                   Forall (atom_to_semax Delta Q' Qn) (atoms_conn_atoms (continue_atom res1) (break_atom res2)) /\
                   Forall (atom_return_to_semax Delta Q' Qr) (atoms_conn_returns (normal_atom res1) (return_atom res2)) /\
                   Forall (atom_return_to_semax Delta Q' Qr) (atoms_conn_returns (continue_atom res1) (return_atom res2)))) x  ).
              {
               eapply soundness_null_aux4;eauto.
               + intro;destruct H6;auto.
               + intros;apply atom_conn_pres_to_semax_reverse_group2' with (normal_atom res2);eauto;destruct H5 as (W1 & W2 & W3 &W4);auto.
               + intros;apply atom_conn_pres_to_semax_reverse_group2' with (normal_atom res2);eauto. 
                 apply all_basic_atoms_conn_pres;eauto. destruct H.
                 * destruct H. rewrite H. simpl.
                 assert ((atoms_conn_pres (normal_atom res2) []) = nil). 
                 {  rewrite atoms_conn_pres_nil. right. auto. }
                 rewrite H8. apply Forall_nil.
                 *  rewrite H. simpl. apply Forall_nil.
               + intros;apply atom_conn_pres_to_semax_reverse_group2' with (normal_atom res2);eauto. 
                  apply all_basic_atoms_conn_pres;eauto. destruct H.
                 * destruct H. rewrite H7. simpl.
                 assert ((atoms_conn_pres (normal_atom res2) []) = nil). 
                 {  rewrite atoms_conn_pres_nil. right. auto. }
                 rewrite H8. apply Forall_nil.
                 *  rewrite H. simpl. apply Forall_nil.
               + intros;apply add_return_to_atom_semax_group with (normal_atom res2);eauto.
                 destruct H5 as (W1 & W2 & W3 &W4 & W5 &W6);auto.
               + intros. 
                 apply atom_conn_atom_to_semax_reverse_group with (normal_atom res2);eauto.
                 destruct H5 as (W1 & W2 & W3 &W4 & W5 &W6);auto.
               + intros. 
                 apply atom_conn_atom_to_semax_reverse_group with (normal_atom res2);eauto.
                 destruct H.
                 * destruct H. rewrite H. simpl.
                 assert ( (atoms_conn_atoms (normal_atom res2) (@nil (list (sum expr atom_statement)))) = []).
                 {  rewrite atoms_conn_atoms_nil. right. auto. } (* # otherwise cannot rewrite*)
                 rewrite H8.  apply Forall_nil. 
                 *  rewrite H. simpl. apply Forall_nil.
               + intros. 
                 apply atom_conn_atom_to_semax_reverse_group with (normal_atom res2);eauto.
                 destruct H.
                 * destruct H. rewrite H7. simpl.
                 assert ( (atoms_conn_atoms (normal_atom res2) (@nil (list (sum expr atom_statement)))) = []).
                 {  rewrite atoms_conn_atoms_nil. right. auto. }
                 rewrite H8. apply Forall_nil.
                 *  rewrite H. simpl. apply Forall_nil.
               + intros;apply add_return_to_atom_semax_group with (normal_atom res2);eauto.
                 destruct H.
                 * destruct H. rewrite H. simpl.
                 assert ((atoms_conn_returns (normal_atom res2) (@nil (prod (list (sum expr atom_statement)) (option expr))))= (@nil (prod (list (sum expr atom_statement)) (option expr)))). 
                 {  rewrite atoms_conn_returns_nil. right. auto. } (* # otherwise cannot rewrite*)
                 rewrite H8.  apply Forall_nil. 
                 *  rewrite H. simpl. apply Forall_nil.
               + intros;apply add_return_to_atom_semax_group with (normal_atom res2);eauto.
                 destruct H.
                 * destruct H. rewrite H7. simpl.
                 assert ((atoms_conn_returns (normal_atom res2) (@nil (prod (list (sum expr atom_statement)) (option expr))))= (@nil (prod (list (sum expr atom_statement)) (option expr)))). 
                 {  rewrite atoms_conn_returns_nil. right. auto. }
                 rewrite H8. apply Forall_nil.
                 *  rewrite H. simpl. apply Forall_nil.
               }
              apply Easy.
      - apply Forall_forall. intros.
        eapply atom_to_semax_derives_pre.
        2:{ apply atom_to_semax_sem. }
        Intros Q'. Exists Q'. apply andp_right;try solve_andp.
        apply prop_right. eapply Forall_forall in H8.
        apply H8. auto.
      - rewrite Econt_atom. constructor.
      - apply Forall_forall. intros.
        eapply atom_return_to_semax_derives_pre.
        2:{ apply atom_return_to_semax_sem. }
        Intros Q'. Exists Q'. apply andp_right;try solve_andp.
        apply prop_right. eapply Forall_forall in H7.
        apply H7. auto.
   } 
}
Qed.

End Soundness.
