Require Import AClight.AClight.
Require Import VST.floyd.proofauto.
Require Import split.vst_ext.
Require Import split.defs.
Require Import split.rule.
Require Import split.semantics.
Section Soundness.

Context {CS: compspecs} {Espec: OracleKind} (Delta: tycontext).

Axiom conj_rule : forall  P Q c Q1 Q2 ,
  @semax CS Espec Delta P c (overridePost Q1 Q) ->
  @semax CS Espec Delta P c (overridePost Q2 Q) ->
  @semax CS Espec Delta P c (overridePost (andp Q1 Q2) Q).


Axiom bupd_tc_expr_cong: forall a, (|==> |> FF || tc_expr Delta a) 
                                  |-- tc_expr Delta a.

Axiom bupd_bool_type_cong: forall a, 
    (|==> |> FF || !! (bool_type (typeof a) = true))
    |-- !! (bool_type (typeof a) = true).


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
  + destruct HX as [x ?].  
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
  + auto.
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

(* -------------------------------------------------
   Assertion Derivation 
   for paths/partial paths/atoms 
--------------------------------------------------- *)
Lemma atom_return_to_semax_derives_pre: forall p P1 P2 Q,
P1 |-- P2 ->
atom_return_to_semax Delta P2 Q p ->
atom_return_to_semax Delta P1 Q p.
Proof.
 intros.
 destruct p.
 constructor.
 inv H0.
 eapply semax_pre.
 + simpl. intros. apply andp_left2. apply H.
 + apply H2.
Qed.

Lemma atom_return_to_semax_derives_pre_group: forall P1 P2 Q atoms,
  P1 |-- P2 ->
  Forall (atom_return_to_semax Delta P2 Q) atoms ->
  Forall (atom_return_to_semax Delta P1 Q) atoms.
Proof. 
  intros.
  eapply Forall_forall.
  intros. eapply atom_return_to_semax_derives_pre.
  apply H. eapply Forall_forall in H0. apply H0. auto.
Qed.

Lemma add_pre_to_semax_derives_group: forall P1 P2 pres,
  P1 |-- P2 ->
  Forall (add_pre_to_semax Delta P2) pres ->
  Forall (add_pre_to_semax Delta P1) pres.
Proof. 
  intros.
  eapply Forall_forall.
  intros. eapply add_pre_to_semax_derives.
  apply H. eapply Forall_forall in H0. apply H0. auto.
Qed.

Lemma atom_to_semax_derives_pre: forall p P1 P2 Q,
  P1 |-- P2 ->
  atom_to_semax Delta P2 Q p ->
  atom_to_semax Delta P1 Q p.
Proof.
  intros.
  eapply atom_to_semax_derives.
  - apply H.
  - apply ENTAIL_refl.
  - auto.
Qed.

Lemma atom_to_semax_derives_pre_group: forall P1 P2 Q atoms,
  P1 |-- P2 ->
  Forall (atom_to_semax Delta P2 Q) atoms ->
  Forall (atom_to_semax Delta P1 Q) atoms.
Proof. 
  intros.
  eapply Forall_forall.
  intros. eapply atom_to_semax_derives_pre.
  apply H. eapply Forall_forall in H0. apply H0. auto.
Qed.

Lemma atom_to_semax_derives_post: forall p P Q1 Q2,
  ENTAIL Delta, Q1 |-- Q2 ->
  atom_to_semax Delta P Q1 p ->
  atom_to_semax Delta P Q2 p.
Proof.
  intros.
  eapply atom_to_semax_derives.
  - apply derives_refl.
  - apply H.
  - auto.
Qed.

Lemma add_post_to_semax_conj_rule: forall Q1 Q2 post,
add_post_to_semax Delta Q1 post ->
add_post_to_semax Delta Q2 post ->
add_post_to_semax Delta (Q1 && Q2) post.
Proof.
  intros. destruct post as [post path].
  induction post.
  - constructor. inv H. inv H0.
    eapply semax_post.
    5: { eapply conj_rule with (Q1:=Q1) (Q2:=Q2)
          (Q:= {|
            RA_normal := Q2;
            RA_break := FALSE;
            RA_continue := FALSE;
            RA_return := fun _ : option val => FALSE |}).
        + apply H2.
        + apply H1.
    }
    { apply andp_left2. apply derives_refl. }
    { apply ENTAIL_refl. }
    { apply ENTAIL_refl. }
    { intros. apply ENTAIL_refl. }
  - constructor. intros. inv H. apply inj_pair2 in H4. subst.
    inv H0. apply inj_pair2 in H4. subst.
    apply H1;auto.
Qed.

Lemma atom_to_semax_conj_rule: forall P Q1 Q2 atom,
  atom_to_semax Delta P Q1 atom ->
  atom_to_semax Delta P Q2 atom ->
  atom_to_semax Delta P (Q1 && Q2) atom.
Proof.
  intros.
  constructor.
  inv H. inv H0.
  eapply conj_rule with (Q1:=Q1) (Q2:=Q2)
          (Q:= {|
            RA_normal := Q2;
            RA_break := FALSE;
            RA_continue := FALSE;
            RA_return := fun _ : option val => FALSE |});auto.
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
    inv H.
    apply semax_seq_inv in H1.
    destruct H1 as [Qret [H1 E2]].
    apply path_to_statement_app in H1.
    apply semax_seq_inv' in H1. unfold overridePost in H1.
    eapply add_post_to_semax_derives with (Q:=
    (EX Q : environ -> mpred,
                       !! DeepEmbeddedDef.semax Delta Q
                            (path_to_statement ret_atom)
                            {|
                            RA_normal := Qret;
                            RA_break := FALSE;
                            RA_continue := FALSE;
                            RA_return := R |} && Q)%assert).
    { Intros Q. Exists Q. apply andp_right.
      apply ENTAIL_refl. apply prop_right. constructor.
      eapply semax_seq. apply H.
      apply E2.
    }
    { constructor.
      eapply semax_noreturn_inv in H1;[apply H1|..].
      + apply noreturn_split_result.
      + reflexivity.
      + reflexivity.
      + reflexivity.
    }
  - constructor. intros.
    apply H0. inv H. apply inj_pair2 in H3. subst. simpl. auto.
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
    { constructor.
      simpl in H1. rewrite app_nil_r in H1.
      pose proof proj1 (Forall_forall _ _) H1.
      eapply DeepEmbedded.ConseqFacts.semax_post_simple;[..|apply semax_skip];
        unfold normal_ret_assert.
      + unfold RA_normal, normal_ret_assert. Exists a1. apply andp_right.
        apply derives_refl. apply prop_right. constructor;[|constructor].
        eapply path_conn_to_semax_reverse_simple. apply H2.
        apply in_split in H. destruct H as [posts1 [posts2 H]].
        rewrite H. rewrite posts_conn_pre_app. apply in_or_app. right.
        destruct p as [p2 a2]. destruct p2;simpl;auto.
      + unfold RA_break. apply FF_left.
      + apply FF_left.
      + intros. apply FF_left. }
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
      { constructor.
        eapply DeepEmbedded.ConseqFacts.semax_post_simple;[..|apply semax_skip];
        unfold normal_ret_assert.
        + unfold RA_normal, normal_ret_assert. Exists a1. apply andp_right.
          apply derives_refl. apply prop_right. constructor;[|constructor].
          eapply path_conn_to_semax_reverse_simple.
          apply (proj1 (Forall_forall _ _) H1). apply in_or_app. right.
          apply in_or_app. left.
          apply in_split in H. destruct H as [posts1 [posts2 H]].
          rewrite H. rewrite posts_conn_pre_app. apply in_or_app. right.
          destruct a as [p2 a2]. destruct p2;simpl;auto.
        + unfold RA_break. apply FF_left.
        + apply FF_left.
        + intros. apply FF_left.
      }
      eapply add_post_to_semax_derives.
      2:{ eapply add_post_to_semax_conj_rule.
          apply H4. apply IHpres.  
      }
      { Intros Q1. Intros Q2.
        Exists (Q1 && Q2). apply andp_right.
        + apply ENTAIL_refl.
        + apply prop_right. constructor.
          - inv H6.
            eapply add_pre_to_semax_derives;[..|apply H9].
            { apply andp_left2. apply derives_refl. }
          - constructor.
            { inv H5. eapply add_pre_to_semax_derives;[..|apply H9].
              { apply andp_left1. apply derives_refl. } }
            { inv H6. apply Forall_forall. intros.
              apply (proj1 (Forall_forall _ _) H10) in H6.
              eapply add_pre_to_semax_derives;[..|apply H6].
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
    { constructor.
      simpl in H1. destruct a2; try inversion H1. simpl in H2.
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
      inv H4. apply path_to_statement_app in H6.
      apply semax_seq_inv' in H6. simpl in H6.
      eapply DeepEmbedded.ConseqFacts.semax_post_simple;[..|apply H6];intros;
        try apply derives_refl.
      simpl. intros. Intros Q. Exists Q.
      apply andp_right;[apply derives_refl|apply prop_right].
      constructor;[|constructor]. constructor.
      auto.
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
      { constructor.
        inv E1.
        apply path_to_statement_app in H4.
        apply semax_seq_inv' in H4. simpl in H4.
        eapply DeepEmbedded.ConseqFacts.semax_post_simple;[..|apply H4];intros;
          try apply derives_refl.
        simpl. intros. Intros Q. Exists Q.
        apply andp_right;[apply derives_refl|]. apply prop_right.
        constructor. auto.
      }
      eapply add_post_to_semax_derives.
      2:{ eapply add_post_to_semax_conj_rule.
          apply E2. apply IHpres.  
      }
      { Intros Q1. Intros Q2.
        Exists (Q1 && Q2). apply andp_right.
        + apply ENTAIL_refl.
        + apply prop_right. constructor.
          - inv H4.
            eapply add_pre_to_semax_derives;[..|apply H7].
            { apply andp_left2. apply derives_refl. }
          - constructor.
            { eapply add_pre_to_semax_derives;[..|apply H3].
            { apply andp_left1. apply derives_refl. } }
            { inv H4. apply Forall_forall. intros.
              apply (proj1 (Forall_forall _ _) H8) in H4.
              eapply add_pre_to_semax_derives;[..|apply H4].
              { apply andp_left2. apply derives_refl. } }
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
  - constructor. inv H. apply path_to_statement_app in H1. apply semax_seq_inv in H1. destruct H1 as [Q [H1 H2]].
    unfold overridePost in H1. eapply semax_conseq;[..|apply H1]. 
    + apply derives_full_refl.
    + unfold RA_normal. (* Search bupd later derives. *) apply aux1_reduceR. (* Search derives bupd. *) eapply derives_trans.
    2:{apply bupd_intro. }
    1:{ Exists Q. apply andp_right. solve_andp. apply prop_right. constructor. apply H2. }
    + unfold RA_break. apply derives_full_refl.
    + unfold RA_continue. apply derives_full_refl.
    + intros. unfold RA_return. apply derives_full_refl.
  - constructor. intros. apply H0. simpl in H. inv H. apply inj_pair2 in H2. subst.
    simpl. apply H5.
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
    inv H3. eapply add_post_to_semax_derives.
    2:{ apply path_conn_to_semax_reverse. apply H5. }
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
      + eapply add_pre_to_semax_derives. apply andp_left1. apply derives_refl.
        eapply Forall_forall in H1. apply H1.
        left. exact H5.
      + destruct H5. eapply add_pre_to_semax_derives. apply andp_left2. apply derives_refl.
        rewrite H5 in H3. exact H3.
        eapply add_pre_to_semax_derives. apply andp_left1. apply derives_refl.
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
    { constructor.
      eapply DeepEmbedded.ConseqFacts.semax_post_simple;[..|apply semax_skip];
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
      { constructor.
        eapply DeepEmbedded.ConseqFacts.semax_post_simple;[..|apply semax_skip];
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
        + apply ENTAIL_refl.
        + apply prop_right. constructor.
          - inv H6.
            eapply add_pre_to_semax_derives;[..|apply H9].
            { apply andp_left2. apply derives_refl. }
          - constructor.
            { inv H5. eapply add_pre_to_semax_derives;[..|apply H9].
            { apply andp_left1. apply derives_refl. } }
            { inv H6. apply Forall_forall. intros.
              apply (proj1 (Forall_forall _ _) H10) in H6.
              eapply add_pre_to_semax_derives;[..|apply H6].
              { apply andp_left2. apply derives_refl. } }
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
    { constructor. destruct p0 as [a2 p2].
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
      inv H4. apply path_to_statement_app in H5.
      apply semax_seq_inv' in H5. simpl in H5.
      eapply DeepEmbedded.ConseqFacts.semax_post_simple;[..|apply H5];intros;
        try apply derives_refl.
      simpl. intros. Intros Q. Exists Q.
      apply andp_right;[apply derives_refl|apply prop_right].
      constructor;[|constructor]. constructor.
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
      { constructor.
        inv E1.
        apply path_to_statement_app in H4.
        apply semax_seq_inv' in H4. simpl in H4.
        eapply DeepEmbedded.ConseqFacts.semax_post_simple;[..|apply H4];intros;
          try apply derives_refl.
        simpl. intros. Intros Q. Exists Q.
        apply andp_right;[apply derives_refl|]. apply prop_right.
        constructor. auto.
      }
      eapply atom_to_semax_derives.
      1:{ apply derives_refl. }
      2:{ eapply atom_to_semax_conj_rule.
          apply E2. apply IHpres.  
      }
      { Intros Q1. Intros Q2.
        Exists (Q1 && Q2). apply andp_right.
        + apply ENTAIL_refl.
        + apply prop_right. constructor.
          - inv H4.
            eapply add_pre_to_semax_derives;[..|apply H7].
            { apply andp_left2. apply derives_refl. }
          - constructor.
            { eapply add_pre_to_semax_derives;[..|apply H3].
            { apply andp_left1. apply derives_refl. } }
            { inv H4. apply Forall_forall. intros.
              apply (proj1 (Forall_forall _ _) H8) in H4.
              eapply add_pre_to_semax_derives;[..|apply H4].
              { apply andp_left2. apply derives_refl. } }
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
  inv H.
  apply semax_seq_inv in H1.
  destruct H1 as [Q_ret [H1 H2]].
  apply path_to_statement_app in H1.
  apply semax_seq_inv' in H1. unfold overridePost in H1.
  eapply atom_to_semax_derives with (Q1:=
    (EX Q : environ -> mpred,
                       !! DeepEmbeddedDef.semax Delta Q
                            (path_to_statement ret_atom)
                            {|
                            RA_normal := Q_ret;
                            RA_break := FALSE;
                            RA_continue := FALSE;
                            RA_return := R |} && Q)%assert).
  { apply derives_refl. }
  { Intros Q. Exists Q. apply andp_right.
    apply ENTAIL_refl. apply prop_right. constructor.
    eapply semax_seq. apply H.
    apply H2.   }
  { constructor.
    eapply semax_noreturn_inv in H1;[apply H1|..].
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
          { intros. apply ENTAIL_refl. }
          { eapply Forall_forall in H2. apply H2. simpl. auto. }
        + eapply atom_return_to_semax_derives.
          { apply andp_left2. apply derives_refl. }
          { intros. apply ENTAIL_refl. }
          { destruct x. apply H3. }
        +  eapply atom_return_to_semax_derives.
          { apply andp_left1. apply derives_refl. }
          { intros. apply ENTAIL_refl. }
          { eapply Forall_forall in H2. apply H2. simpl. auto. }
      }  
Qed.

  
Lemma atom_conn_atom_to_semax_reverse: forall atom1 atom2 P R,
  atom_to_semax Delta P R (atom1 ++  atom2) ->
  atom_to_semax Delta P (EX Q, Q && !!
                 ( atom_to_semax Delta Q R atom2)) atom1.
Proof.
  intros.
  inv H. apply path_to_statement_app in H0.
  apply semax_seq_inv' in H0. unfold overridePost in H0.
  eapply atom_to_semax_derives with (Q1:=
   (EX Q : environ -> mpred,
                       !! DeepEmbeddedDef.semax Delta Q 
                            (path_to_statement atom2)
                            {|
                            RA_normal := R;
                            RA_break := FALSE;
                            RA_continue := FALSE;
                            RA_return := fun _ : option val => FALSE |} && Q)%assert).
  { apply derives_refl. }
  { Intros Q. Exists Q. apply andp_right.
    apply ENTAIL_refl. apply prop_right. constructor.
    auto. }
  { constructor. auto. }
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

Lemma soundness_null_aux1:  forall l1 l2 l3 l4 R1 R2 x,
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
  constructor. Intros Q.
  apply semax_extract_prop.
  intros. inv H.
  apply H0.
Qed.

  
Lemma atom_return_to_semax_sem: forall x R,
 (atom_return_to_semax Delta 
        (EX Q : assert,
          !! (atom_return_to_semax Delta Q R x) && Q)) R
      x.
Proof.
  intros. destruct x as [p v].
  constructor. Intros Q.
  apply semax_extract_prop.
  intros. inv H.
  apply H1.
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
  + inv H. simpl in H1.
    eapply semax_seq_inv in H1.
    destruct H1 as [Q [H1 H2]].
    unfold overridePost in H1.
    apply DeepEmbedded.semax_ifthenelse_inv in H1.
    constructor. eapply semax_conseq with (R':={|
        RA_normal := a0;
        RA_break := FALSE;
        RA_continue := FALSE;
        RA_return := fun _ : option val => FALSE |}).
    { eapply derives_trans;[|apply H1]. simpl. intros.
      solve_andp.
    }
    { apply derives_full_refl. }
    { apply derives_full_refl. }
    { apply derives_full_refl. }
    { intros. apply derives_full_refl. }
    Intros P'. rewrite andp_comm.
    rewrite andp_assoc. apply semax_extract_prop.
    intros [E1 E2]. rewrite andp_comm.
    rewrite andp_assoc. apply semax_extract_prop.
    intros E3. eapply semax_conseq;[..|apply H2].
    { apply semax_skip_inv in E1. unfold RA_normal in E1.
      apply semax_break_inv in E2. unfold RA_break in E2.
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
        apply andp_right.
          apply andp_left1. apply derives_refl.
        rewrite andp_comm.  apply andp_right.
          repeat apply andp_left1. apply derives_refl.
        rewrite (andp_comm (allp_fun_id Delta x)).
        rewrite (andp_comm _ (P' x)). apply andp_right.
          repeat apply andp_left1. apply derives_refl.
        apply andp_left1. apply andp_left2. apply derives_refl. }
      { eapply derives_trans with (Q0:=|==> |> !! False || FALSE x ).
        2:{ apply bupd_mono. apply orp_left.
            apply orp_right1. apply derives_refl.
            unfold FALSE. unfold PROPx. simpl.
            apply derives_extract_prop. intros. tauto. }
        eapply derives_trans;[|apply E2].
        rewrite <- andp_comm. rewrite andp_assoc.
        apply andp_right.
          apply andp_left1. apply derives_refl.
        rewrite andp_comm.  apply andp_right.
          repeat apply andp_left1. apply derives_refl.
        rewrite (andp_comm (allp_fun_id Delta x)).
        rewrite (andp_comm _ (P' x)). apply andp_right.
          repeat apply andp_left1. apply derives_refl.
        apply andp_left1. apply andp_left2. apply derives_refl. }
    }
    { apply derives_full_refl. }
    { apply derives_full_refl. }
    { apply derives_full_refl. }
    { intros. apply derives_full_refl. }
  + constructor. intros. eapply H0.
    inv H. apply inj_pair2 in H3. subst. auto.
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
  + inv H. simpl in H1.
    eapply semax_seq_inv in H1.
    destruct H1 as [Q [H1 H2]].
    unfold overridePost in H1.
    apply DeepEmbedded.semax_ifthenelse_inv in H1.
    constructor. eapply semax_conseq with (R':={|
        RA_normal := a0;
        RA_break := FALSE;
        RA_continue := FALSE;
        RA_return := fun _ : option val => FALSE |}).
    { eapply derives_trans;[|apply H1]. simpl. intros.
      solve_andp.
    }
    { apply derives_full_refl. }
    { apply derives_full_refl. }
    { apply derives_full_refl. }
    { intros. apply derives_full_refl. }
    Intros P'. rewrite andp_comm.
    rewrite andp_assoc. apply semax_extract_prop.
    intros [E1 E2]. rewrite andp_comm.
    rewrite andp_assoc. apply semax_extract_prop.
    intros E3. eapply semax_conseq;[..|apply H2].
    { apply semax_skip_inv in E1. unfold RA_normal in E1.
      apply semax_break_inv in E2. unfold RA_break in E2.
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
        apply andp_right.
          apply andp_left1. apply derives_refl.
        rewrite andp_comm.  apply andp_right.
          repeat apply andp_left1. apply derives_refl.
        rewrite (andp_comm (allp_fun_id Delta x)).
        rewrite (andp_comm _ (P' x)). apply andp_right.
          repeat apply andp_left1. apply derives_refl.
        apply andp_left1. apply andp_left2. apply derives_refl. }
      { eapply derives_trans with (Q0:=|==> |> !! False || FALSE x ).
        2:{ apply bupd_mono. apply orp_left.
            apply orp_right1. apply derives_refl.
            unfold FALSE. unfold PROPx. simpl.
            apply derives_extract_prop. intros. tauto. }
        eapply derives_trans;[|apply E2].
        rewrite <- andp_comm. rewrite andp_assoc.
        apply andp_right.
          apply andp_left1. apply derives_refl.
        rewrite andp_comm.  apply andp_right.
          repeat apply andp_left1. apply derives_refl.
        rewrite (andp_comm (allp_fun_id Delta x)).
        rewrite (andp_comm _ (P' x)). apply andp_right.
          repeat apply andp_left1. apply derives_refl.
        apply andp_left1. apply andp_left2. apply derives_refl. }
    }
    { apply derives_full_refl. }
    { apply derives_full_refl. }
    { apply derives_full_refl. }
    { intros. apply derives_full_refl. }
  + constructor. intros. eapply H0.
    inv H. apply inj_pair2 in H3. subst. auto.
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
+ inv H. simpl in H1.
  eapply semax_seq_inv in H1.
  destruct H1 as [Q [H1 H2]].
  unfold overridePost in H1.
  apply DeepEmbedded.semax_ifthenelse_inv in H1.
  constructor. eapply semax_conseq with (R':={|
      RA_normal := a0;
      RA_break := FALSE;
      RA_continue := FALSE;
      RA_return := fun _ : option val => FALSE |}).
  { eapply derives_trans;[|apply H1]. simpl. intros.
    solve_andp.
  }
  { apply derives_full_refl. }
  { apply derives_full_refl. }
  { apply derives_full_refl. }
  { intros. apply derives_full_refl. }
  Intros P'. rewrite andp_comm.
  rewrite andp_assoc. apply semax_extract_prop.
  intros [E1 E2]. rewrite andp_comm.
  rewrite andp_assoc. apply semax_extract_prop.
  intros E3. eapply semax_conseq;[..|apply H2].
  { apply semax_skip_inv in E1. unfold RA_normal in E1.
    apply semax_break_inv in E2. unfold RA_break in E2.
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
      apply andp_right.
        apply andp_left1. apply derives_refl.
      rewrite andp_comm.  apply andp_right.
        repeat apply andp_left1. apply derives_refl.
      rewrite (andp_comm (allp_fun_id Delta x)).
      rewrite (andp_comm _ (P' x)). apply andp_right.
        repeat apply andp_left1. apply derives_refl.
      apply andp_left1. apply andp_left2. apply derives_refl. }
    { eapply derives_trans with (Q0:=|==> |> !! False || FALSE x ).
      2:{ apply bupd_mono. apply orp_left.
          apply orp_right1. apply derives_refl.
          unfold FALSE. unfold PROPx. simpl.
          apply derives_extract_prop. intros. tauto. }
      eapply derives_trans;[|apply E2].
      rewrite <- andp_comm. rewrite andp_assoc.
      apply andp_right.
        apply andp_left1. apply derives_refl.
      rewrite andp_comm.  apply andp_right.
        repeat apply andp_left1. apply derives_refl.
      rewrite (andp_comm (allp_fun_id Delta x)).
      rewrite (andp_comm _ (P' x)). apply andp_right.
        repeat apply andp_left1. apply derives_refl.
      apply andp_left1. apply andp_left2. apply derives_refl. }
  }
  { apply derives_full_refl. }
  { apply derives_full_refl. }
  { apply derives_full_refl. }
  { intros. apply derives_full_refl. }
+ constructor. intros. eapply H0.
  inv H. apply inj_pair2 in H3. subst. auto.
Qed.

Lemma add_exp_to_atom_inv: forall P Q (a:expr) atom,
      atom_to_semax Delta P Q ((inl a)::atom) ->
       atom_to_semax Delta (P && (local
                                 (@liftx (Tarrow val (LiftEnviron Prop))
                                 (typed_true (typeof a)) (@eval_expr CS a)))
                        ) Q atom.
Proof.
  intros. inv H.
  simpl in H0. 
  eapply semax_seq_inv in H0.
  destruct H0 as [R [H1 H2]].
  unfold overridePost in H1.
  apply DeepEmbedded.semax_ifthenelse_inv in H1.
  constructor. eapply semax_conseq with (R':={|
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
    { apply derives_full_refl. }
    { apply derives_full_refl. }
    { apply derives_full_refl. }
    { intros. apply derives_full_refl. }
    Intros P'. rewrite andp_comm.
    rewrite andp_assoc. apply semax_extract_prop.
    intros [E1 E2]. rewrite andp_comm.
    rewrite andp_assoc. apply semax_extract_prop.
    intros E3. eapply semax_conseq;[..|apply H2].
    { apply semax_skip_inv in E1. unfold RA_normal in E1.
      apply semax_break_inv in E2. unfold RA_break in E2.
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
        apply andp_right.
          apply andp_left1. apply derives_refl.
        rewrite andp_comm.  apply andp_right.
          repeat apply andp_left1. apply derives_refl.
        rewrite (andp_comm (allp_fun_id Delta x)).
        rewrite (andp_comm _ (P' x)). apply andp_right.
          repeat apply andp_left1. apply derives_refl.
        apply andp_left1. apply andp_left2. apply derives_refl. }
      { eapply derives_trans with (Q0:=|==> |> !! False || FALSE x ).
        2:{ apply bupd_mono. apply orp_left.
            apply orp_right1. apply derives_refl.
            unfold FALSE. unfold PROPx. simpl.
            apply derives_extract_prop. intros. tauto. }
        eapply derives_trans;[|apply E2].
        rewrite <- andp_comm. rewrite andp_assoc.
        apply andp_right.
          apply andp_left1. apply derives_refl.
        rewrite andp_comm.  apply andp_right.
          repeat apply andp_left1. apply derives_refl.
        rewrite (andp_comm (allp_fun_id Delta x)).
        rewrite (andp_comm _ (P' x)). apply andp_right.
          repeat apply andp_left1. apply derives_refl.
        apply andp_left1. apply andp_left2. apply derives_refl. }
    }
    { apply derives_full_refl. }
    { apply derives_full_refl. }
    { apply derives_full_refl. }
    { intros. apply derives_full_refl. }
Qed.

Lemma add_exp_to_atom_inv_false: forall P Q (a:expr) atom,
      atom_to_semax Delta P Q ((inl (semax_lemmas.Cnot a))::atom) ->
       atom_to_semax Delta (P && (local
                                 (@liftx (Tarrow val (LiftEnviron Prop))
                                 (typed_false (typeof a)) (@eval_expr CS a)))
                        ) Q atom.
Proof.
  intros. inv H.
  simpl in H0. 
  eapply semax_seq_inv in H0.
  destruct H0 as [R [H1 H2]].
  unfold overridePost in H1.
  apply DeepEmbedded.semax_ifthenelse_inv in H1.
  constructor. eapply semax_conseq with (R':={|
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
    { apply derives_full_refl. }
    { apply derives_full_refl. }
    { apply derives_full_refl. }
    { intros. apply derives_full_refl. }
    Intros P'. rewrite andp_comm.
    rewrite andp_assoc. apply semax_extract_prop.
    intros [E1 E2]. rewrite andp_comm.
    rewrite andp_assoc. apply semax_extract_prop.
    intros E3. eapply semax_conseq;[..|apply H2].
    { apply semax_skip_inv in E1. unfold RA_normal in E1.
      apply semax_break_inv in E2. unfold RA_break in E2.
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
        apply andp_right.
          apply andp_left1. apply derives_refl.
        rewrite andp_comm.  apply andp_right.
          repeat apply andp_left1. apply derives_refl.
        rewrite (andp_comm (allp_fun_id Delta x)).
        rewrite (andp_comm _ (P' x)). apply andp_right.
          repeat apply andp_left1. apply derives_refl.
        apply andp_left1. apply andp_left2. apply derives_refl. }
      { eapply derives_trans with (Q0:=|==> |> !! False || FALSE x ).
        2:{ apply bupd_mono. apply orp_left.
            apply orp_right1. apply derives_refl.
            unfold FALSE. unfold PROPx. simpl.
            apply derives_extract_prop. intros. tauto. }
        eapply derives_trans;[|apply E2].
        rewrite <- andp_comm. rewrite andp_assoc.
        apply andp_right.
          apply andp_left1. apply derives_refl.
        rewrite andp_comm.  apply andp_right.
          repeat apply andp_left1. apply derives_refl.
        rewrite (andp_comm (allp_fun_id Delta x)).
        rewrite (andp_comm _ (P' x)). apply andp_right.
          repeat apply andp_left1. apply derives_refl.
        apply andp_left1. apply andp_left2. apply derives_refl. }
    }
    { apply derives_full_refl. }
    { apply derives_full_refl. }
    { apply derives_full_refl. }
    { intros. apply derives_full_refl. }
Qed.

Lemma add_exp_to_atom_inv': forall P Q (a:expr) atom,
      atom_to_semax Delta P Q ((inl a)::atom) ->
       atom_to_semax Delta (P && (local
                                 (@liftx (Tarrow val (LiftEnviron Prop))
                                 (typed_true (typeof a)) (@eval_expr CS a)))
                        && (!! (bool_type (typeof a) = true))
                        ) Q atom.
Proof.
  intros. inv H.
  simpl in H0. 
  eapply semax_seq_inv in H0.
  destruct H0 as [R [H1 H2]].
  unfold overridePost in H1.
  apply DeepEmbedded.semax_ifthenelse_inv in H1.
  constructor. eapply semax_conseq with (R':={|
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
    { apply derives_full_refl. }
    { apply derives_full_refl. }
    { apply derives_full_refl. }
    { intros. apply derives_full_refl. }
    Intros P'. rewrite andp_comm.
    rewrite andp_assoc. apply semax_extract_prop.
    intros [E1 E2]. rewrite andp_comm.
    rewrite andp_assoc. apply semax_extract_prop.
    intros E3. eapply semax_conseq;[..|apply H2].
    { apply semax_skip_inv in E1. unfold RA_normal in E1.
      apply semax_break_inv in E2. unfold RA_break in E2.
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
        apply andp_right.
          apply andp_left1. apply derives_refl.
        rewrite andp_comm.  apply andp_right.
          repeat apply andp_left1. apply derives_refl.
        rewrite (andp_comm (allp_fun_id Delta x)).
        rewrite (andp_comm _ (P' x)). apply andp_right.
          repeat apply andp_left1. apply derives_refl.
        apply andp_left1. apply andp_left2. apply derives_refl. }
      { eapply derives_trans with (Q0:=|==> |> !! False || FALSE x ).
        2:{ apply bupd_mono. apply orp_left.
            apply orp_right1. apply derives_refl.
            unfold FALSE. unfold PROPx. simpl.
            apply derives_extract_prop. intros. tauto. }
        eapply derives_trans;[|apply E2].
        rewrite <- andp_comm. rewrite andp_assoc.
        apply andp_right.
          apply andp_left1. apply derives_refl.
        rewrite andp_comm.  apply andp_right.
          repeat apply andp_left1. apply derives_refl.
        rewrite (andp_comm (allp_fun_id Delta x)).
        rewrite (andp_comm _ (P' x)). apply andp_right.
          repeat apply andp_left1. apply derives_refl.
        apply andp_left1. apply andp_left2. apply derives_refl. }
    }
    { apply derives_full_refl. }
    { apply derives_full_refl. }
    { apply derives_full_refl. }
    { intros. apply derives_full_refl. }
Qed.

Lemma add_exp_to_return_atom_inv: forall P Q (a:expr) atom,
      atom_return_to_semax Delta P Q (add_exp_to_return_atom a atom) ->
      atom_return_to_semax Delta (P && (local
                                 (@liftx (Tarrow val (LiftEnviron Prop))
                                 (typed_true (typeof a)) (@eval_expr CS a)))
                        ) Q atom.
Proof.
  intros. destruct atom as [atom ret_val]. inv H.
  simpl in H1. 
  eapply semax_seq_inv in H1.
  destruct H1 as [R' [H1 H0]].
  eapply semax_seq_inv in H1.
  destruct H1 as [R [H1 H2]].
  unfold overridePost in H1.
  apply DeepEmbedded.semax_ifthenelse_inv in H1.
  constructor.
  eapply semax_seq;[..|apply H0].
  unfold overridePost.
  eapply semax_noreturn_inv with (Post:={|
    RA_normal := R';RA_break:=FALSE;RA_continue:=FALSE;RA_return:=(fun _ => FALSE)
  |});try reflexivity.
  { apply noreturn_split_result. }
  eapply semax_conseq with (R':={|
        RA_normal := R';
        RA_break := FALSE;
        RA_continue := FALSE;
        RA_return := fun _ : option val => FALSE |}).
    { eapply derives_trans;[|apply H1]. simpl. intros.
      repeat apply andp_right.
      + apply andp_left1. apply derives_refl.
      + apply andp_left2. apply andp_left1. apply derives_refl.
      + apply andp_left2. apply andp_left2. apply andp_left1.
        apply derives_refl.
    }
    { apply derives_full_refl. }
    { apply derives_full_refl. }
    { apply derives_full_refl. }
    { intros. apply derives_full_refl. }
    Intros P'. rewrite andp_comm.
    rewrite andp_assoc. apply semax_extract_prop.
    intros [E1 E2]. rewrite andp_comm.
    rewrite andp_assoc. apply semax_extract_prop.
    intros E3. 
    eapply semax_noreturn_inv with (Post:={|
      RA_normal:=R';RA_break:=FALSE;RA_continue:=FALSE;RA_return:=Q
    |});try reflexivity. { apply noreturn_split_result. }
    eapply semax_conseq;[..|apply H2].
    { apply semax_skip_inv in E1. unfold RA_normal in E1.
      apply semax_break_inv in E2. unfold RA_break in E2.
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
      { eapply derives_trans with (Q0:=|==> |> !! False || FALSE x ).
        2:{ apply bupd_mono. apply orp_left.
            apply orp_right1. apply derives_refl.
            unfold FALSE. unfold PROPx. simpl.
            apply derives_extract_prop. intros. tauto. }
        eapply derives_trans;[|apply E2].
        solve_andp. }
    }
    { apply derives_full_refl. }
    { apply derives_full_refl. }
    { apply derives_full_refl. }
    { intros. apply derives_full_refl. }
Qed.

Lemma add_exp_to_return_atom_inv_false: forall P Q (a:expr) atom,
      atom_return_to_semax Delta P Q (add_exp_to_return_atom (semax_lemmas.Cnot a) atom) ->
      atom_return_to_semax Delta (P && (local
                                 (@liftx (Tarrow val (LiftEnviron Prop))
                                 (typed_false (typeof a)) (@eval_expr CS a)))
                        ) Q atom.
Proof.
  intros. destruct atom as [atom ret_val]. inv H.
  simpl in H1. 
  eapply semax_seq_inv in H1.
  destruct H1 as [R' [H1 H0]].
  eapply semax_seq_inv in H1.
  destruct H1 as [R [H1 H2]].
  unfold overridePost in H1.
  apply DeepEmbedded.semax_ifthenelse_inv in H1.
  constructor.
  eapply semax_seq;[..|apply H0].
  unfold overridePost.
  eapply semax_noreturn_inv with (Post:={|
    RA_normal := R';RA_break:=FALSE;RA_continue:=FALSE;RA_return:=(fun _ => FALSE)
  |});try reflexivity.
  { apply noreturn_split_result. }
  eapply semax_conseq with (R':={|
        RA_normal := R';
        RA_break := FALSE;
        RA_continue := FALSE;
        RA_return := fun _ : option val => FALSE |}).
    { eapply derives_trans;[|apply H1]. simpl. intros.
      repeat apply andp_right.
      + apply andp_left1. apply derives_refl.
      + apply andp_left2. apply andp_left1. apply derives_refl.
      + apply andp_left2. apply andp_left2. apply andp_left1.
        apply derives_refl.
    }
    { apply derives_full_refl. }
    { apply derives_full_refl. }
    { apply derives_full_refl. }
    { intros. apply derives_full_refl. }
    Intros P'. rewrite andp_comm.
    rewrite andp_assoc. apply semax_extract_prop.
    intros [E1 E2]. rewrite andp_comm.
    rewrite andp_assoc. apply semax_extract_prop.
    intros E3. 
    eapply semax_noreturn_inv with (Post:={|
      RA_normal:=R';RA_break:=FALSE;RA_continue:=FALSE;RA_return:=Q
    |});try reflexivity. { apply noreturn_split_result. }
    eapply semax_conseq;[..|apply H2].
    { apply semax_skip_inv in E1. unfold RA_normal in E1.
      apply semax_break_inv in E2. unfold RA_break in E2.
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
      { eapply derives_trans with (Q0:=|==> |> !! False || FALSE x ).
        2:{ apply bupd_mono. apply orp_left.
            apply orp_right1. apply derives_refl.
            unfold FALSE. unfold PROPx. simpl.
            apply derives_extract_prop. intros. tauto. }
        eapply derives_trans;[|apply E2].
        solve_andp. }
    }
    { apply derives_full_refl. }
    { apply derives_full_refl. }
    { apply derives_full_refl. }
    { intros. apply derives_full_refl. }
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
    semax Delta P (Clight.Sifthenelse a c1' c2') Q'.
Proof.
  intros. destruct pre'. induction p.
  - inv H. simpl in H1. apply semax_seq_inv in H1. destruct H1 as [Q' [? ?]].
     exists Clight.Sskip, Clight.Sbreak, (overridePost Q'
             {| RA_normal := a0;
                RA_break := FALSE;
                RA_continue := FALSE;
                RA_return := fun _ : option val => FALSE |}).
    apply H.
  - pose proof HA. destruct H1 as [x _].
    specialize (H0 x). eapply H0. simpl in H.
    inv H. apply inj_pair2 in H3. subst.
    specialize (H2 x). auto. 
Qed.

Lemma add_exp_to_atom_tc: forall P Q a normal_atom',
  atom_to_semax Delta P Q (inl a :: normal_atom') ->
  exists (c1' c2' : Clight.statement) (Q' : ret_assert),
    semax Delta P (Clight.Sifthenelse a c1' c2') Q'.
Proof.
  intros. inv H. simpl in H0.
  apply semax_seq_inv in H0. destruct H0 as [Q' [? ?]].
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
  semax Delta P (Clight.Sifthenelse a c1' c2') Q'.
Proof.
  intros. destruct return_atom'. inv H. simpl in H1.
  apply semax_seq_inv in H1. destruct H1 as [Q'' [? ?]].
  apply semax_seq_inv in H. destruct H as [Q' [? ?]].  
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
  intros. revert x.
  inv H. apply inj_pair2 in H1. subst.
  auto.
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
      * constructor. inv H1. inv H2. auto.
      * constructor. intros x. apply H.
        inv H1. eapply path_to_semax_given_sem in H3.
        simpl.
        destruct (p x) eqn:E;(constructor;[rewrite <- E; apply H3| constructor]).
      (*         
        inv H3. inv H2 apply inj_pair2 in H1. subst.
        specialize (H1 x).
        simpl in H1. simpl. destruct (p x) eqn:E. 
        { constructor;[|constructor]. auto. }
        { constructor;[|constructor]. auto. } *)
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
  constructor. inv H. auto.
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
  constructor. inv H. auto.
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
  - inv H0. constructor. auto.
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
  - inv H0. constructor. auto.
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
  { constructor. inv H. auto. }
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
  { constructor. inv H. auto. }
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
    - constructor. inv H. auto.
    - constructor. intros. apply H0. inv H.
      apply inj_pair2 in H2. subst. auto. }
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
  - inv H. rewrite app_nil_r in H1. constructor. auto.
  - simpl in *. constructor. intros. apply H0.
    inv H. apply inj_pair2 in H2. subst. apply H5.
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
  inv H. constructor.
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
  inv H. constructor.
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
  inv H. constructor.
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

Lemma conn_assoc1:forall pres posts atoms,
 (posts_conn_pres (posts_conn_atoms (posts) (atoms)) (pres)) = 
 (posts_conn_pres posts (atoms_conn_pres (atoms) (pres))).
Proof.
  intros. destruct posts.
  Admitted.

Lemma all_basic_atoms_conn_pres:forall (atoms:atom_statements) pres,
all_basic (pres) = true ->
all_basic (atoms_conn_pres atoms pres) = true.
Proof.
intros. Print all_basic.
destruct atoms.
- Check atoms_conn_pres_nil1.
  rewrite atoms_conn_pres_nil. auto.
- Check atoms_conn_pres_app1.

unfold atoms_conn_pres. simpl. 
unfold all_basic.



Theorem soundness: forall 
(P:assert) (Q:ret_assert) (stm: statement) (c_stm: Clight.statement)
(s: split_result),
path_split stm s ->
split_Semax Delta P Q s ->
AClight_to_Clight stm c_stm ->
@semax CS Espec Delta P c_stm Q.
Proof.
  intros. generalize dependent c_stm. 
  generalize dependent P.
  generalize dependent Q.
  induction H.
  + intros. inv H3.
    apply inj_pair2 in H6. subst.
    pose proof bind_result_add_inv _ _ _ _ _ _ _ H2 H.
    (* non empty type is also used here *)
    destruct HX as [? ?].
    apply (H1 x);auto.
  + intros R P Hvalid c_stm Hc. inv Hc.
     eapply semax_seq
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
         + apply derives_refl.
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
    - inv H5. inv H11. simpl in H5.
      apply semax_seq_skip in H5.
      eapply DeepEmbedded.ConseqFacts.semax_post_simple;[..|apply H5].       
      * apply derives_refl.
      * apply derives_extract_PROP'. intros C. destruct C.
      * apply derives_extract_PROP'. intros C. destruct C.
      * intros. apply derives_extract_PROP'. intros C. destruct C.
    - inv H5. inv H11. simpl in H5.
      apply semax_seq_skip in H5.
      eapply DeepEmbedded.ConseqFacts.semax_post_simple;[..|apply H5];
        unfold RA_normal, RA_break, RA_continue, RA_return in *.
      * apply derives_refl.
      * apply derives_extract_PROP'. intros C. destruct C.
      * apply derives_extract_PROP'. intros C. destruct C.
      * intros. apply derives_extract_PROP'. intros C. destruct C.
    - inv H1. inv H11. simpl in H9.
      inv H. inv H11. simpl in H1.
      econstructor;[..|apply H9].
      * eapply semax_skip_inv in H1. unfold RA_normal in H1.
        apply H1.
      * unfold RA_normal. apply derives_full_refl.
      * unfold RA_break. apply aux1_reduceR.
        apply andp_left2. apply andp_left2.
        apply derives_extract_PROP'. intros C;destruct C.
      * unfold RA_continue. apply aux1_reduceR.
        apply andp_left2. apply andp_left2.
        apply derives_extract_PROP'. intros C;destruct C.
      * unfold RA_return. intros.  apply aux1_reduceR.
        apply andp_left2. apply andp_left2.
        apply derives_extract_PROP'. intros C;destruct C.
    - inv H7. inv H11. simpl in H7.
      eapply DeepEmbeddedPracticalLogic.CSHL_MinimumLogic.semax_conseq.
      { apply semax_skip_inv in H7. apply H7. }
      { apply derives_full_refl. }
      { apply derives_full_refl. }
      { apply derives_full_refl. }
      { intros. apply derives_full_refl. }
      { unfold RA_normal. 
        replace Qc with (
          RA_continue {| RA_normal := Qn; RA_break := Qb; RA_continue := Qc; RA_return := Qr |}
        ) by reflexivity.
        apply semax_continue. }
    - inv H6. inv H11. simpl in H6.
      eapply DeepEmbeddedPracticalLogic.CSHL_MinimumLogic.semax_conseq.
      { apply semax_skip_inv in H6. apply H6. }
      { apply derives_full_refl. }
      { apply derives_full_refl. }
      { apply derives_full_refl. }
      { intros. apply derives_full_refl. }
      { unfold RA_normal. 
        replace Qb with (
          RA_break {| RA_normal := Qn; RA_break := Qb; RA_continue := Qc; RA_return := Qr |}
        ) by reflexivity.
        apply semax_break. }
    - inv H5. inv H11.
      simpl in H5.
      eapply DeepEmbeddedPracticalLogic.CSHL_MinimumLogic.semax_conseq;[..|apply semax_skip];unfold normal_ret_assert, RA_normal,
      RA_return,RA_break,RA_continue.
      { apply semax_skip_inv in H5. apply H5. }
      { apply derives_full_refl. }
      { apply aux1_reduceR. apply andp_left2.
        apply derives_extract_prop'. intros C;destruct C. }
      { apply aux1_reduceR. apply andp_left2.
        apply derives_extract_prop'. intros C;destruct C. }
      { intros. apply aux1_reduceR. apply andp_left2.
        apply derives_extract_prop'. intros C;destruct C. }
    - inv H8. inv H11. simpl in H9.
      apply semax_skip_seq in H9.
      eapply DeepEmbeddedPracticalLogic.CSHL_MinimumLogic.semax_conseq;[..|apply H9];unfold normal_ret_assert, RA_normal,
      RA_return,RA_break,RA_continue.
      { apply derives_full_refl. }
      { apply aux1_reduceR. apply andp_left2.
        apply derives_extract_PROP. intros C;destruct C. }
      { apply aux1_reduceR. apply andp_left2.
        apply derives_extract_PROP. intros C;destruct C. }
      { apply aux1_reduceR. apply andp_left2.
        apply derives_extract_PROP. intros C;destruct C. }
      { intros. apply derives_full_refl. }
    - inv H5. inv H11. simpl in H5. apply semax_seq_skip in H5.
      eapply DeepEmbeddedPracticalLogic.CSHL_MinimumLogic.semax_conseq;[..|apply H5];unfold normal_ret_assert, RA_normal,
      RA_return,RA_break,RA_continue;try apply derives_full_refl.
      { apply aux1_reduceR. apply andp_left2.
        apply derives_extract_PROP. intros C;destruct C. }
      { apply aux1_reduceR. apply andp_left2.
        apply derives_extract_PROP. intros C;destruct C. }
      { intros. apply aux1_reduceR. apply andp_left2.
        apply derives_extract_PROP. intros C;destruct C. }
+ intros.
  inv H2.
  eapply semax_conseq with (P':= (!! ((bool_type (typeof a)) = true)) &&
   (tc_expr Delta (Eunop Onotbool a (Tint I32 Signed noattr))) &&
  (
    !! (split_Semax Delta (P && local (liftx (typed_true (typeof a)) (eval_expr a))) Q res1 /\ 
    split_Semax Delta (P && local (liftx (typed_false (typeof a)) (eval_expr a))) Q res2
  ) && P)) (R':= Q); try (intros;apply derives_full_refl).
  2:{ rewrite andp_assoc.
      apply semax_extract_prop. intros.
      rewrite andp_comm. rewrite andp_assoc. 
      apply semax_extract_prop.
      intros [E1 E2].
      eapply semax_pre_simple.
      2:{ eapply semax_ifthenelse;auto.
      + apply IHpath_split1. apply E1. auto.
      + apply IHpath_split2. apply E2. auto. }
      solve_andp. }
    assert (exists c1' c2' Q', semax Delta P (Clight.Sifthenelse a c1' c2') Q').
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
  apply semax_ifthenelse_inv in H2.
  assert (ENTAIL Delta, allp_fun_id Delta && P 
          |-- tc_expr Delta  (Eunop Onotbool a (Tint I32 Signed noattr))) as E1.
  { eapply derives_trans;[apply H2|].
    eapply derives_trans;[| apply bupd_tc_expr_cong].
    apply bupd_mono.     
    apply orp_left;[apply orp_right1;apply derives_refl|].
    apply orp_right2. apply andp_left1.
    apply andp_left2. apply derives_refl. }
    assert (ENTAIL Delta, allp_fun_id Delta && P 
    |-- !! (bool_type (typeof a) = true)) as E2.
  { simpl. intros env.
    simpl in H2. specialize (H2 env).
    eapply derives_trans;[apply H2|].
    eapply derives_trans;[|apply bupd_bool_type_cong].
    apply bupd_mono.     
    apply orp_left;[apply orp_right1;apply derives_refl|].
    apply orp_right2. apply andp_left1.
    apply andp_left1. apply derives_refl. }
  pose proof andp_right _ _ _ E1 E2.
  apply add_andp in H3.
  rewrite H3.
  apply aux1_reduceR. eapply derives_trans;[|apply bupd_intro].
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
  inv S1. clear H5. simpl in H4. inv H4. simpl in H3.
  apply semax_skip_inv in H3. unfold RA_normal in H3.
  eapply semax_conseq with (R':=Q);[apply H3|..];intros;try apply derives_full_refl.
  inv H2. eapply semax_loop with (Q':= inv2).
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

+ intros. inv H5.
  assert (AClight_to_Clight
    (Sloop (LIDouble inv inv) (c1;; c2) AClight.Sskip)
    (Clight.Sloop (Clight.Ssequence c_stm1 c_stm2) Clight.Sskip)
  ).
  { try repeat constructor;auto. }
  destruct H2.
  { (* no continue *)
    assert (c1' = c_stm1).
    { eapply AClight_to_Clight_unique. apply H. apply H10. }
    subst.
    specialize (IHpath_split _ _ H4 _ H5).
    apply semax_loop_inv in IHpath_split.
    destruct Q as [Qn Qb Qc Qr].
    eapply semax_conseq;[apply IHpath_split|..];
      try (intros;apply derives_full_refl).
    Intros Q1 Q2. apply semax_extract_prop.
    intros [Hq1 Hq2].
    apply semax_skip_inv in Hq2.
    unfold RA_normal, loop2_ret_assert in Hq2.
    unfold loop1_ret_assert in Hq1.
    assert (E:semax Delta Q1 (Clight.Ssequence c_stm1 c_stm2)
              {|
              RA_normal := Q1;
              RA_break := Qn;
              RA_continue := Q1;
              RA_return := Qr |}
    ).
    { eapply semax_conseq;[..|apply Hq1];
      try (intros; apply derives_full_refl);
      unfold RA_normal,RA_continue;auto. }
    apply semax_seq_inv in E.
    unfold overridePost in E.
    destruct E as [inv2 [E1 E2]].
    eapply semax_loop; unfold loop1_ret_assert, loop2_ret_assert.
    { eapply semax_nocontinue_inv;[..|apply E1];auto.
      - unfold RA_normal. reflexivity.
      - unfold RA_break. reflexivity.
      - unfold RA_return. reflexivity. }
    { eapply semax_nocontinue_inv;[..|apply E2];auto.
      assert (c2' = c_stm2).
      { eapply AClight_to_Clight_unique. apply H0. apply H11. }
      subst. auto. }
  }
  { (* c2 = skip *)
    assert (c2' = c_stm2).
    { eapply AClight_to_Clight_unique. apply H0. apply H11. }
    subst. inv H0.
    specialize (IHpath_split _ _ H4 _ H5).
    destruct Q as [Qn Qb Qc Qr].
    apply semax_loop_inv in IHpath_split.
    eapply semax_conseq;[apply IHpath_split|..];
    try (intros; apply derives_full_refl).
    Intros inv1 inv2.
    apply semax_extract_prop;unfold loop1_ret_assert, loop2_ret_assert.
    intros [E1 E2].
    assert (E:semax Delta inv1 c_stm1
              {|
              RA_normal := inv1;
              RA_break := Qn;
              RA_continue := inv1;
              RA_return := Qr |}
    ).
    { eapply semax_skip_inv in E2.
      apply semax_seq_inv in E1. unfold RA_normal in E2.
      destruct E1 as [Q' [E1 E3]].
      apply semax_skip_inv in E3. unfold RA_normal in E3.
      unfold overridePost in E1.
      eapply semax_conseq with (R' := {|
        RA_normal := inv2;
        RA_break := Qn;
        RA_continue := inv2;
        RA_return := Qr      
      |});unfold overridePost, RA_normal,
      RA_break, RA_return, RA_continue; try (intros; apply derives_full_refl);auto.
      eapply semax_conseq;[..|apply E1];unfold overridePost, RA_normal,
      RA_break, RA_return, RA_continue; try (intros; apply derives_full_refl);auto.
    }
    eapply semax_loop.
    { eapply semax_conseq;[..|apply E];unfold loop1_ret_assert, RA_normal,
      RA_break, RA_continue, RA_return;try (intros; apply derives_full_refl). }
    eapply semax_conseq;[..|eapply semax_skip];unfold normal_ret_assert;
    unfold loop2_ret_assert, RA_normal, RA_break, RA_continue, RA_return;
    [apply derives_full_refl|..];[apply derives_full_refl|..];
    try (intros; apply andp_left2; apply andp_left2; apply FF_left).
  }
+ (* one loop invariant.*)
  simpl. rewrite !app_nil_r. intros. 
  hnf in H1;simpl in H1. destruct H1 as [S1 [S2 [S3 [_ [_ [S4 [_ [_ [_ _]]]]]]]]].
  inv S1. clear H5. simpl in H4. inv H4. simpl in H3.
  apply semax_skip_inv in H3. unfold RA_normal in H3.
  eapply semax_conseq with (R':=Q);[apply H3|..];intros;try apply derives_full_refl.
  inv H2.  eapply semax_loop with (Q':=
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
            + apply derives_refl.
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
    hnf in H4;simpl in H4. destruct H4 as (S1 & S2 & S3 & _ & _ & S4 & S5 & S6 & _ & S7).
    (* Print semax_conseq.
    Check semax_conseq. *)
    eapply semax_conseq with (P':= 
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
      )) ); try apply derives_full_refl. 
    2:{ intros. apply derives_full_refl. } (* this is trivial*)
    1:{ (* {P} c {inv1} *)
        (* Search bupd later derives. *) apply aux1_reduceR.
        (* Search derives bupd. *) eapply derives_trans.
      2:{ apply bupd_intro. }
      Exists P. repeat apply andp_right;try solve_andp.
      apply prop_right. repeat split;try in_split_result S1;try in_split_result S5;try in_split_result S7.
  (*    - in_split_result S1.
      - in_split_result S1.
      - in_split_result S1.
      - in_split_result S6.
      - in_split_result S5.
      - in_split_result S5.
      - in_split_result S5.
      - in_split_result S6.
      - in_split_result S6. *)
    }
    inv H5. destruct Q as [Qn Qb Qc Qr].
    eapply semax_loop with (Q':=
    EX Q'':assert, andp Q'' (
      !!
        ( Forall (add_pre_to_semax Delta Q'') (pre res2) /\
          Forall (add_pre_to_semax Delta Q'') (atoms_conn_pres (normal_atom res2) (pre res1))/\
          Forall (atom_return_to_semax Delta Q'' Qr) (return_atom res2) /\
          Forall (atom_to_semax Delta Q'' Qn) (break_atom res2))
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
        apply Forall_forall. intros.
        assert (Enpe :(normal_post res1) <> nil). 
        {destruct (normal_post res1);try discriminate. exfalso. eauto. (*  wxw nb *)  }
        eapply soundness_null_aux1;eauto.
        + assert ( WXWNB: ~ (pre res2 = [] /\ normal_atom res2 = [] /\ break_atom res2 = [] /\ continue_atom res2 = [] /\ return_atom res2 = [])).
        { apply split_not_empty with stm2. eauto. }
        rewrite Econt_atom in WXWNB. intro T. apply WXWNB. repeat split;try apply T. destruct H;eauto.
         destruct T as (_ & T & _).  apply atoms_conn_pres_nil in T. destruct T;eauto. exfalso;eauto.
        + intros. 
         Check path_conn_to_semax_reverse_group4.
          apply path_conn_to_semax_reverse_group4 with (normal_post res1);eauto.
          in_split_result S2.
       + intros.
       Check path_conn_to_semax_reverse_group4. 
         apply path_conn_to_semax_reverse_group4 with (normal_post res1);eauto.
         2:{
         Print in_split_result. 
         assert (Forall (path_to_semax Delta) (posts_conn_pres (posts_conn_atoms (normal_post res1) (normal_atom res2)) (pre res1))) .
         { in_split_result S2. }          
         rewrite conn_assoc1 in H6;eauto. } 
         
       +  
       + admit.
                                
(*         eapply soundness_null_aux1;auto;try assumption.
        + assert (TNE: ~ (pre res2 = [] /\ normal_atom res2 = [] /\ break_atom res2 = [] /\ continue_atom res2 = [] /\ return_atom res2 = [])).
        { apply split_not_empty with stm2. try assumption. }
        rewrite Econt_atom in TNE. intro. apply TNE. repeat split;try apply H5. destruct H.
          2:{auto. }
          1:{

(*          apply Forall_app in S3;destruct S3 as [H4 S3].
         apply Forall_app in S3;destruct S3 as [H5 S3].
 *)        admit.   
*)
        }  

        
       (* can be inved, use a lemma *)
      - in_split_result S3.
      - admit. (* can be inved, use a lemma *)
      - in_split_result S4.
      - apply Forall_forall. intros.
        constructor. Intros inv.
        rewrite andp_comm. apply semax_extract_prop.
        intros. (* normal_atom res2 must be empty
          otherwise atoms1 and atoms2 are not empty at the same time,
          the rest of the three clauses can be inved from H4
        *) admit.
      - apply Forall_forall. intros.
        eapply atom_to_semax_derives_pre.
        2:{ apply atom_to_semax_sem. }
        Intros Q'. Exists Q'. apply andp_right;try solve_andp.
        apply prop_right. eapply Forall_forall in H11.
        apply H11. auto.
      - apply Forall_forall. intros.
        constructor. Intros inv.
        rewrite andp_comm. apply semax_extract_prop.
        intros. (* normal_atom res2 must be empty
          otherwise atoms1 and atoms2 are not empty at the same time,
          the rest of the three clauses can be inved from H4
        *) admit.
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
      - admit. (* can be inved, write a lemma
        normal_post2 + break_atom1 is missing in S3
        normal_post2 + normal_atom1/continue + break_atom2 is missing in S3
        normal_post2 + normal_atom1/continue + return_atom2 is missing in S4
      *)
      - admit. (* missing break_post2 in S3 *)
      - rewrite Econt_post. constructor.
      - admit. (* missing return_post2 in S3 *)
      - apply Forall_forall. intros.
        constructor. Intros inv.
        rewrite andp_comm. apply semax_extract_prop.
        intros. (* 
          1 -> inv from H4
          2,3 -> must be empty
          5,6 -> must be empty
          H4 is not powerful enough to be a weakest pre, missing:
          - normal_atom2 + break_atom1 + Qn
          - normal_atom2 + return_atom1 + Qr
          should be inved from H4 after refinement
        *) admit.
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
Admitted.

End Soundness.
