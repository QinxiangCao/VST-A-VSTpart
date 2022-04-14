Require Import VST.msl.log_normalize.
Require Import VST.msl.alg_seplog.
Require Import VST.veric.base.
Require Import VST.veric.compcert_rmaps.
Require Import VST.veric.res_predicates.

Require Import compcert.cfrontend.Ctypes.
Require Import VST.veric.address_conflict.
Require Import VST.veric.val_lemmas.
Require Import VST.veric.Cop2.
Require Import VST.veric.shares.
Require Import VST.veric.slice.

Require Import VST.veric.mpred.
Require Import VST.veric.mapsto_memory_block.


Lemma relation_power_level: forall n x y,
 relation_power n age x y -> ((level x) = n + (level y))%nat.
Proof.
intros n. induction n;intros.
{ simpl. hnf in H. f_equal. auto. }
simpl in H. destruct H as [x' [? ?]].
apply IHn in H0. simpl. rewrite <- H0.
apply age_level. auto.
Qed.


Lemma share_sub_lub: forall sh1 sh2 sh3,
join_sub sh1 sh2 ->
join_sub sh1 sh3 ->
join_sub sh1 (Share.lub sh2 sh3).
Proof.
intros. destruct H. destruct H0.
destruct H. destruct H0.
exists (Share.lub x x0).
split.
- rewrite Share.distrib1. rewrite H. rewrite H0. rewrite Share.lub_bot. reflexivity.
- rewrite <- (Share.lub_idem sh1).
  rewrite Share.lub_assoc. rewrite <- (Share.lub_assoc sh1 x).
  rewrite H1. rewrite (Share.lub_commute sh2 x0).
  rewrite <- Share.lub_assoc. rewrite H2.
  rewrite Share.lub_commute. reflexivity.
Qed.


Definition join_sub_share sh1 res :=
match res with
| YES sh _ _ _ | NO sh _ => join_sub sh1 sh
| _ => True
end.

Definition resourece_share res:= 
match res with
| YES sh _ _ _ | NO sh _ => sh
| _ => Share.top
end.


Lemma join_rem_nsh rall sh1 sh2 
(nsh:  ~ readable_share (resourece_share rall))
(JS1:join_sub sh1 (resourece_share rall)) (JS2:join_sub sh2 (resourece_share rall)) :
~ readable_share (Share.glb (resourece_share rall) (Share.comp (Share.lub sh1 sh2))).
Proof.
intros.
intros C. apply nsh. destruct rall. 
{ simpl in *. destruct JS1 as [sh1' H], JS2 as [sh2' H0].
  pose proof share_cross_split _ _ _ _ _ H H0.
  destruct X as [shs E].
  destruct shs as [[[sh11 sh12] sh21] sh22].
  destruct E as (E1 & E2 & E3 & E4).
  apply join_comm in E2. apply join_comm in H.
  epose proof join_assoc E2 H. destruct X as [sh_u [E5 E6]].
  assert (Share.lub sh1 sh2 = sh_u).
  { destruct E5. rewrite <- H2. rewrite Share.lub_commute.
    destruct E3. rewrite <- H4.
    destruct E1. rewrite <- !H6.
    rewrite (Share.lub_commute sh11 sh21).
    rewrite Share.lub_assoc. rewrite <- (Share.lub_assoc sh11).
    rewrite Share.lub_idem. reflexivity. }
  rewrite H1 in C.
  assert (Share.glb sh (Share.comp sh_u) = sh22).
  { destruct E6. rewrite <- H3.
    rewrite Share.glb_commute. rewrite Share.distrib1.
    rewrite (Share.glb_commute _ sh_u). rewrite Share.comp2.
    rewrite Share.lub_bot. apply share_lemma87.
    rewrite Share.glb_commute. assumption. }
  rewrite H2 in C.
  eapply readable_share_join.
  { apply E6. } auto. }
{ simpl in *. destruct JS1 as [sh1' H], JS2 as [sh2' H0].
  pose proof share_cross_split _ _ _ _ _ H H0.
  destruct X as [shs E].
  destruct shs as [[[sh11 sh12] sh21] sh22].
  destruct E as (E1 & E2 & E3 & E4).
  apply join_comm in E2. apply join_comm in H.
  epose proof join_assoc E2 H. destruct X as [sh_u [E5 E6]].
  assert (Share.lub sh1 sh2 = sh_u).
  { destruct E5. rewrite <- H2. rewrite Share.lub_commute.
    destruct E3. rewrite <- H4.
    destruct E1. rewrite <- !H6.
    rewrite (Share.lub_commute sh11 sh21).
    rewrite Share.lub_assoc. rewrite <- (Share.lub_assoc sh11).
    rewrite Share.lub_idem. reflexivity. }
  rewrite H1 in C.
  assert (Share.glb sh (Share.comp sh_u) = sh22).
  { destruct E6. rewrite <- H3.
    rewrite Share.glb_commute. rewrite Share.distrib1.
    rewrite (Share.glb_commute _ sh_u). rewrite Share.comp2.
    rewrite Share.lub_bot. apply share_lemma87.
    rewrite Share.glb_commute. assumption. }
  rewrite H2 in C.
  eapply readable_share_join.
  { apply E6. } auto. }
{ simpl in C. simpl. auto. }
Qed.


Definition join_rem_of sh1 sh2 rall
(JS1:join_sub sh1 (resourece_share rall))
(JS2:join_sub sh2 (resourece_share rall)) :=
match rall with
| YES sh rsh k p =>
    let sh' := Share.glb sh (Share.comp (Share.lub sh1 sh2)) in
    match (dec_readable sh') with
    | left rsh' => YES sh' rsh' k p
    | right nsh' => NO sh' nsh'
    end
| NO sh nsh =>
    let sh' := Share.glb (resourece_share rall) 
        (Share.comp (Share.lub sh1 sh2)) in
    match (dec_readable (resourece_share rall)) with
    | left rsh' => NO Share.bot bot_unreadable
    | right nsh' =>
        NO sh' (join_rem_nsh rall sh1 sh2 nsh' JS1 JS2)
    end
| PURE k p => PURE k p
end.



(* Using the notations from VST.msl.predicates_hered
below are semantic-level lemmas *)

Local Open Scope pred_derives.


Definition identity_resource_of res :=
  match res with
  | PURE k p => PURE k p
  | NO _ _ | YES _ _ _ _ => NO Share.bot bot_unreadable
  end.

Lemma identity_resource_of_sem res: join res (identity_resource_of res) res.
Proof.
  unfold identity_resource_of.
  destruct res; constructor;apply join_bot_eq .
Qed.

Lemma identity_resource_at_approx:
  forall phi l,
      resource_fmap (approx (level phi)) (approx (level phi)) (identity_resource_of (phi @ l)) = (identity_resource_of (phi @ l)).
Proof.
  intros. symmetry. rewrite rmap_level_eq. unfold resource_at.
  case_eq (unsquash phi); intros.
  simpl.
  set (phi' := (squash (n, (resource_fmap (approx n) (approx n) oo fst r, snd r)))).
  pose proof I.
  generalize (unsquash_inj phi phi'); intro.
  spec H1.
  replace (unsquash phi) with (unsquash (squash (unsquash phi))).
  2: rewrite squash_unsquash; auto.
  rewrite H.
  unfold phi'.
  repeat rewrite unsquash_squash.
  simpl.
  f_equal.
  unfold rmap_fmap, compose; simpl.
  f_equal.
  extensionality y.
  rewrite resource_fmap_fmap.
  rewrite approx_oo_approx; auto.
  unfold phi' in *; clear phi'.
  subst.
  rewrite unsquash_squash in H.
  injection H; clear H; intro.
  pattern r at 1. rewrite <- H.
  unfold rmap_fmap, compose.
  simpl; rewrite resource_fmap_fmap.
  rewrite approx_oo_approx; auto.
  destruct (fst r l);simpl;reflexivity.
Qed.


Notation "'ALL' x .. y , P " :=
  (allp (fun x => .. (allp (fun y => P%pred)) ..)) (at level 65, x binder, y binder, right associativity) : pred.


Inductive cut_resource_rmap_exp (sh:share) l (len:Z) (bl: list memval): rmap -> rmap -> Prop :=
| cut_resource_exp_intro: forall r_mapsto 
  r1 r2 (Hl: Z.of_nat (Datatypes.length bl) = len),
  (((ALL y, jam (adr_range_dec l len)
      (fun l' => yesat NoneP (VAL (nth (Z.to_nat (snd l' - snd l)) bl Undef)) sh l') noat y) && noghost) r_mapsto)%pred ->
  join r_mapsto r1 r2 ->
  cut_resource_rmap_exp sh l len bl r1 r2.

Inductive cut_resource_rmap (sh:share) l (len:Z): rmap -> rmap -> Prop :=
  | cut_resource_intro: forall (bl: list memval) r1 r2,
    cut_resource_rmap_exp sh l len bl r1 r2 ->
    cut_resource_rmap sh l len r1 r2.
  
Inductive cut_resource_rejoin (sh:share) l m v: rmap -> rmap -> Prop :=
| cut_resource_rejoin_exp_intro:
    forall r_rem r_rem' r_mapsto' r1 r2,
    address_mapsto m v sh l r_mapsto' ->
    cut_resource_rmap sh l (size_chunk m) r_rem r1 ->
    necR r_rem r_rem' ->
    join r_rem' r_mapsto' r2->
    cut_resource_rejoin sh l m v r1 r2.

Lemma cut_resource_rmap_unique: forall sh l len r1 r2 r,
cut_resource_rmap sh l len r1 r ->
cut_resource_rmap sh l len r2 r ->
r1 = r2.
Proof.
  intros. inv H. rename H1 into H.
  inv H0. rename H1 into H0. inv H. inv H0.
  pose proof join_join_sub H2.
  pose proof join_join_sub H3.
  assert (r_mapsto = r_mapsto0).
  { apply rmap_ext.
    + apply join_level in H2. apply join_level in H3.
      destruct H2, H3. congruence.
    + intros. hnf in H1. destruct H1, H.
      apply resource_at_join with (loc:=l0) in H2.
      apply resource_at_join with (loc:=l0) in H3.
      specialize (H1 l0).
      specialize (H l0). hnf in H1, H.
      if_tac in H1;subst.
      * destruct H1, H. rewrite H1, H. f_equal. apply proof_irr.
        f_equal. rewrite H1, H in *. inv H2; inv H3; try congruence.
      * do 3 red in H,H1.
        apply resource_at_join_sub with (l:=l0) in H0. 
        eapply join_sub_same_identity; eauto.
        - apply identity_unit'; auto.
        - apply (resource_at_join_sub _ _ l0) in H4.
          eapply join_sub_unit_for; eauto.
          apply identity_unit'; auto.
    + destruct H1, H. 
      eapply same_identity; auto.
      * destruct H0 as [? H0%ghost_of_join].
        rewrite (H5 _ _ H0) in H0. eauto.
      * destruct H4 as [? H4%ghost_of_join].
        rewrite (H6 _ _ H4) in H4; eauto.
  }
  subst r_mapsto0. clear H0 H4 H.
  apply rmap_ext.
  { apply join_level in H2. apply join_level in H3.
    destruct H2, H3. congruence. }
  { intros. hnf in H1. destruct H1.
    specialize (H l0).
    apply resource_at_join with (loc:=l0) in H2.
    apply resource_at_join with (loc:=l0) in H3. hnf in H.
    if_tac in H.
    + hnf in H. destruct H as [rsh H]. rewrite H in *.
      inv H2; inv H3; try congruence;rewrite <- H10 in H9; inv H9.
      - apply join_comm in RJ. apply join_comm in RJ0.
        pose proof join_canc RJ RJ0.
        subst sh0. f_equal. apply proof_irr.
      - apply join_comm in RJ. apply join_comm in RJ0.
        pose proof join_canc RJ RJ0.
        subst sh0. contradiction.
      - apply join_comm in RJ. apply join_comm in RJ0.
        pose proof join_canc RJ RJ0.
        subst sh0. contradiction.
      - apply join_comm in RJ. apply join_comm in RJ0.
        pose proof join_canc RJ RJ0.
        subst sh0. f_equal. apply proof_irr.
    + apply H in H2. apply H in H3. congruence.
  }
  { hnf in H1. destruct H1.
    apply ghost_of_join in H2.
    apply ghost_of_join in H3.
    apply H0 in H2. apply H0 in H3.
    congruence. }
Qed.


Lemma cut_resource_sem: forall r m v1 v2 sh l P,
  (address_mapsto m v1 sh l * (address_mapsto m v2 sh l -* P))%pred r ->
  forall r', cut_resource_rejoin sh l m v2 r r' -> P r'.
Proof.
  intros.
  destruct H as [r_maps [r_rem [H1 [H2 H3]]]]. inv H0.
  eapply H3.
  3:{ apply H. }
  2:{ apply H6. }
  assert (cut_resource_rmap sh l (size_chunk m) r_rem r).
  { destruct H2 as [bl H2]. eapply cut_resource_intro with (bl:=bl).
    destruct H2 as [[H2 ?] ?]. simpl in H2. destruct H2.
    apply cut_resource_exp_intro with (r_mapsto := r_maps);auto.
    { rewrite H2. rewrite size_chunk_conv. reflexivity. }
    { split;auto. }
  }
  pose proof cut_resource_rmap_unique _ _ _ _ _ _ H4 H0.
  subst. auto.
Qed.


Lemma cut_resource_sem_inv: forall r m v1 v2 sh l bl (P: pred rmap) r_rem,
  cut_resource_rmap_exp sh l (size_chunk m) bl r_rem r ->
  decode_val m bl = v1 -> (align_chunk m | snd l) ->
  (forall r', cut_resource_rejoin sh l m v2 r r' -> P r') ->
  (address_mapsto m v1 sh l * (address_mapsto m v2 sh l -* P))%pred r.
Proof.
  intros. inversion H as [bm]. subst.
  inversion H. subst. exists r_mapsto, r_rem. split;auto. split.
  - hnf. exists bl. destruct H0. split;auto. split;auto. simpl;auto.
    rewrite size_chunk_conv in Hl.  repeat split;auto.
    rewrite <- Nat2Z.id at 1. rewrite Hl0. reflexivity.
  - hnf. intros r_rem' r_maps' r'. intros.
    apply H2. eapply cut_resource_rejoin_exp_intro; try eassumption.
    apply cut_resource_intro with (bl:=bl);auto.
Qed.



Lemma share_resource_join_aux: forall sh1 sh2 sh3 sh5 sh,
join sh1 sh3 sh -> join sh2 sh5 sh -> join (Share.lub sh1 sh2) (Share.glb sh (Share.comp (Share.lub sh1 sh2))) sh.
Proof.
intros.
pose proof share_cross_split _ _ _ _ _ H H0.
destruct X as [shs E].
destruct shs as [[[sh11 sh12] sh21] sh22].
destruct E as (E1 & E2 & E3 & E4).
apply join_comm in E2. apply join_comm in H.
epose proof join_assoc E2 H. destruct X as [sh_u [E5 E6]].
assert (Share.lub sh1 sh2 = sh_u).
{ destruct E5. rewrite <- H2. rewrite Share.lub_commute.
  destruct E3. rewrite <- H4.
  destruct E1. rewrite <- !H6.
  rewrite (Share.lub_commute sh11 sh21).
  rewrite Share.lub_assoc. rewrite <- (Share.lub_assoc sh11).
  rewrite Share.lub_idem. reflexivity. }
rewrite H1.
assert (Share.glb sh (Share.comp sh_u) = sh22).
{ destruct E6. rewrite <- H3.
  rewrite Share.glb_commute. rewrite Share.distrib1.
  rewrite (Share.glb_commute _ sh_u). rewrite Share.comp2.
  rewrite Share.lub_bot. apply share_lemma87.
  rewrite Share.glb_commute. assumption. }
rewrite H2.
auto.
Qed.



Lemma cut_resource_map_preserve_necR_aux {sh lbase len bm}:
  forall n r_rem r r_rem' r',
  relation_power n age r_rem r_rem' ->
  relation_power n age r r' ->
  cut_resource_rmap_exp sh lbase len bm r_rem r ->
  cut_resource_rmap_exp sh lbase len bm r_rem' r'.
Proof.
  induction n;intros.
  - simpl in H0. simpl in H. subst. tauto.
  - destruct H as [r_rem'' [? ?]].
    destruct H0 as [r'' [? ?]].
    apply (IHn _ _ _ _ H2 H3).
    { inv H1.
      assert (exists r_mapsto'', age r_mapsto r_mapsto'').
      { eapply level_age_fash. apply join_level in H5.
        apply age_level in H0. rewrite (proj1 H5). apply H0. }
      destruct H1 as [r_mapsto'' H1].
      eapply cut_resource_exp_intro with (r_mapsto:= r_mapsto'');auto.
      2:{ eapply age1_join_eq;[apply H5|..];auto. }
      hnf in H.
      destruct H4. split.
      + intros l. specialize (H4 l).
        hnf in H4. hnf. if_tac.
        { destruct H4. exists x. hnf in H4.
          hnf. simpl. epose proof age1_YES _ _ _ _ _ _ H1.
          apply H8 in H4. auto. }
        { epose proof age1_resource_at_identity _ _ _ H1.
          apply H8 in H4. auto. }
      + epose proof age1_ghost_of_identity _ _ H1.
        apply H7 in H6. auto.
    }
Qed.


Lemma cut_resource_map_preserve_necR {sh lbase len bm}:
  forall r_rem r r_rem' r',
  cut_resource_rmap_exp sh lbase len bm r_rem r ->
  necR r_rem r_rem' ->
  necR r r' ->
  level r' = level r_rem' ->
  cut_resource_rmap_exp sh lbase len bm r_rem' r'.
Proof.
  intros. apply necR_power_age in H0. apply necR_power_age in H1.
  destruct H0 as [m H0]. destruct H1 as [n H1].
  assert (m = n).
  { inv H. apply join_level in H4.
    apply relation_power_level in H0. apply relation_power_level in H1.
    omega. }
  subst m. eapply cut_resource_map_preserve_necR_aux;try eassumption.
Qed.

Lemma address_mapsto_preserve_necR {sh lbase m v}:
  forall r_mapsto' r_mapsto,
    necR r_mapsto r_mapsto' ->
    address_mapsto m v sh lbase r_mapsto' <->
    address_mapsto m v sh lbase r_mapsto.
Proof.
  intros. apply necR_power_age in H.
  destruct H as [n H]. revert dependent r_mapsto'.
  revert dependent r_mapsto.
  induction n;intros.
  - inv H. subst. tauto.
  - destruct H as [r_mapsto'' [? ?]].
    apply IHn in H0. rewrite H0. clear H0.
    hnf in H. split;intro.
    { inv H0. exists x. destruct H1 as [[? ?] ?].
      split;[split|].
      + simpl. simpl in H0. auto.
      + intros l. specialize (H1 l).
        hnf in H1. hnf. if_tac.
        { destruct H1. exists x0. hnf in H1.
          hnf. simpl. epose proof age1_YES _ _ _ _ _ _ H.
          apply H4 in H1. auto. }
        { epose proof age1_resource_at_identity _ _ _ H.
          apply H4 in H1. auto. }
      + epose proof age1_ghost_of_identity _ _ H.
        apply H3 in H2. auto.
    }
    { inv H0. exists x. destruct H1 as [[? ?] ?].
      split;[split|].
      + simpl. simpl in H0. auto.
      + intros l. specialize (H1 l).
        hnf in H1. hnf. if_tac.
        { destruct H1. exists x0. hnf in H1.
          hnf. simpl. epose proof age1_YES _ _ _ _ _ _ H.
          apply H4 in H1. auto. }
        { epose proof age1_resource_at_identity _ _ _ H.
          apply H4 in H1. auto. }
      + epose proof age1_ghost_of_identity _ _ H.
        apply H3 in H2. auto.
    }
Qed.


Lemma two_share_join: forall sh1 sh2,
join sh1 (Share.glb (Share.comp sh1) sh2) (Share.lub sh1 sh2).
Proof.
  intros. split.
  - rewrite <- Share.glb_assoc. rewrite Share.comp2.
    rewrite Share.glb_commute. rewrite Share.glb_bot. reflexivity.
  - rewrite Share.distrib2. rewrite Share.comp1.
    rewrite Share.glb_commute. rewrite Share.glb_top. reflexivity.
Qed.


Lemma cut_resource_rejoin_merge: 
forall sh1 sh2 lbase m r (Q1 Q2: pred rmap)
  (wsh1: writable_share sh1) (wsh2: writable_share sh2)
  (Hw1: forall v' r', cut_resource_rejoin sh1 lbase m v' r r' -> Q1 r')
  (Hw2: forall v' r', cut_resource_rejoin sh2 lbase m v' r r' -> Q2 r'),
    (forall v' r', cut_resource_rejoin (Share.lub sh1 sh2) lbase m v' r r' -> Q1 r').
Proof.
  intros.
  inv H. pose proof sepalg_list.nec_join3 H3 H2.
  destruct H as [r_mapsto'' [r'' [? [? ?]]]].
  eapply pred_nec_hereditary; try eassumption.
  eapply Hw1.
  apply (@address_mapsto_preserve_necR 
    (Share.lub sh1 sh2) lbase m v' _ _ H4) in H0.
  clear dependent r_rem'.
  clear dependent r_mapsto'. clear  dependent r'.
  assert (rsh1: readable_share sh1). 
  { apply writable_readable_share. auto. }
  assert (nsh2: ~ readable_share (Share.glb (Share.comp sh1) sh2)).
  { intros C. eapply join_writable_readable.
    2:{ apply wsh1. } 2:{ apply C. }
    apply two_share_join. }
  inversion H0 as [bm].
  inv H1. inv H3.
  remember (squash (level r_rem,(fun l =>
    if (adr_range_dec lbase (size_chunk m) l) 
    then YES sh1 rsh1 (VAL (nth (Z.to_nat (snd l - snd lbase)) bm Undef)) NoneP
    else (r_mapsto'' @ l)
  ,ghost_of r_mapsto''))) as r_maps1''.
  remember (squash (level r_rem,(fun l =>
    if (adr_range_dec lbase (size_chunk m) l) 
    then YES sh1 rsh1 (VAL (nth (Z.to_nat (snd l - snd lbase)) bl Undef)) NoneP
    else (r_mapsto @ l)
  ,ghost_of r_mapsto))) as r_maps1.
  remember (squash (level r_rem,(fun l =>
    if (adr_range_dec lbase (size_chunk m) l) 
    then NO (Share.glb (Share.comp sh1) sh2) nsh2 
    else identity_resource_of (r_mapsto @ l)
  ,nil))) as r_rem2.

  assert (E1: join r_rem2 r_maps1'' r_mapsto'').
  { apply join_unsquash. subst.
    rewrite !unsquash_squash. split.
    - simpl. apply join_level in H.
       rewrite rmap_level_eq in *.
       constructor;omega.
    - split.
      + simpl. unfold join. unfold Join_pi. 
        intros l. unfold compose. simpl.
        destruct H2 as [[? ?] ?].
        specialize (H3 l). simpl in H3. if_tac.
        { simpl. destruct H3. unfold resource_at in H3.
          rewrite H3. constructor.
          apply join_comm. apply two_share_join. }
        { destruct H1. specialize (H1 l). simpl in H1.
          assert (level r_rem = level r_mapsto).
          { apply join_level in H4. omega. }
          rewrite H8. rewrite identity_resource_at_approx. clear H8.
          assert (level r_mapsto = level r_mapsto'').
          { apply join_level in H. apply join_level in H4. omega. }
          rewrite H8. rewrite resource_at_approx. clear H8.
          unfold resource_at.
          pose proof resource_at_join _ _ _ l H as Et1.
          pose proof resource_at_join _ _ _ l H4 as Et2.
          if_tac in H1; try tauto.
          pose proof H1 _ _ Et2. apply join_comm in Et1.
          pose proof H3 _ _ Et1. rewrite H9 in *. rewrite H10 in *.
          unfold resource_at in Et1, Et2. clear H9. clear H10.
          destruct ((fst (snd (unsquash r_mapsto)) l));simpl;
          destruct ((fst (snd (unsquash r_mapsto'')) l));simpl;try constructor;try apply bot_join_eq; try solve [inv Et1; inv Et2; congruence].
          inv Et1. inv Et2. rewrite H12. rewrite <- H13. constructor.
        }
      + simpl. assert (level r_rem = level r_mapsto'').
        { apply join_level in H. omega. }
        rewrite H3. rewrite ghost_of_approx. unfold ghost_of.
        constructor.
  }

  assert (E2: join r_rem2 r_maps1 r_mapsto).
  { apply join_unsquash. subst.
    rewrite !unsquash_squash. split.
    - simpl. apply join_level in H4.
       rewrite rmap_level_eq in *.
       constructor;omega.
    - split.
      + simpl. unfold join. unfold Join_pi. 
        intros l. unfold compose. simpl.
        destruct H2 as [[? ?] ?].
        destruct H1. specialize (H1 l). simpl in H1.
        if_tac.
        { simpl. destruct H1. unfold resource_at in H1.
          rewrite H1. constructor. apply join_comm.
          apply two_share_join. }
        { assert (level r_rem = level r_mapsto).
          { apply join_level in H4. omega. }
          rewrite H8. rewrite identity_resource_at_approx. clear H8.
          rewrite resource_at_approx. apply join_comm.
          apply identity_resource_of_sem. }
      + simpl. assert (level r_rem = level r_mapsto).
        { apply join_level in H4. omega. }
        rewrite H3. rewrite ghost_of_approx. unfold ghost_of.
        constructor.
  }
  assert (E3: address_mapsto m v' sh1 lbase r_maps1'').
  { rewrite Heqr_maps1''. destruct H2 as [[? ?] ?].
    exists bm. split;[split|].
    - simpl. simpl in H2. auto.
    - intros l. simpl. if_tac.
      { exists rsh1. unfold resource_at. rewrite unsquash_squash.
        simpl. unfold compose. if_tac;try tauto. }
      { unfold resource_at. rewrite unsquash_squash. simpl.
        unfold compose. if_tac; try tauto.
        assert (level r_rem = level r_mapsto'').
        { apply join_level in H. omega. }
        rewrite H8. replace (fst (snd (unsquash r_mapsto'')) l) with
        (r_mapsto'' @ l) by reflexivity.
        rewrite resource_at_approx.
        specialize (H3 l). simpl in H3. if_tac in H3;try tauto. }
    - simpl. unfold ghost_of. rewrite unsquash_squash.
      simpl. 
      assert (level r_rem = level r_mapsto'').
      { apply join_level in H4. apply join_level in H. omega. }
      rewrite H6. rewrite ghost_of_approx. auto.
  }
  

  apply join_comm in H.  apply join_comm in E1. apply join_comm in E2.
  destruct (join_assoc E1 H) as [r_rm [HJ1 HJ2]].
  destruct (join_assoc E2 H4) as [r_rm'' [HJ3 HJ4]].
  assert (r_rm = r_rm'').
  { eapply join_eq;eassumption. }
  subst r_rm''. clear HJ3.
  econstructor.
  4:{ apply join_comm in HJ2. apply HJ2. }
  3:{ apply necR_refl. }
  { apply E3. }
  { exists bl.
    apply cut_resource_exp_intro with 
     (r_mapsto:=r_maps1);auto. subst r_maps1.
    split.
    - intros l. simpl. if_tac.
      { exists rsh1. unfold resource_at. rewrite unsquash_squash.
        simpl. unfold compose. if_tac;try tauto. }
      { unfold resource_at. rewrite unsquash_squash. simpl.
        unfold compose. if_tac; try tauto.
        assert (level r_rem = level r_mapsto).
        { apply join_level in H4. omega. }
        rewrite H6. replace (fst (snd (unsquash r_mapsto)) l) with
        (r_mapsto @ l) by reflexivity.
        rewrite resource_at_approx. destruct H1.
        specialize (H1 l). simpl in H1. if_tac in H1;try tauto. }
    - simpl. unfold ghost_of. rewrite unsquash_squash.
      simpl. 
      assert (level r_rem = level r_mapsto).
      { apply join_level in H4. omega. }
      rewrite H3. rewrite ghost_of_approx. destruct H1. auto.
  }
Qed.


Lemma cut_resource_rejoin_merge_det: 
forall sh1 sh2 lbase m r (Q1 Q2: pred rmap) v'
  (wsh1: writable_share sh1) (wsh2: writable_share sh2)
  (Hw1: forall r', cut_resource_rejoin sh1 lbase m v' r r' -> Q1 r')
  (Hw2: forall r', cut_resource_rejoin sh2 lbase m v' r r' -> Q2 r'),
    (forall r', cut_resource_rejoin (Share.lub sh1 sh2) lbase m v' r r' -> Q1 r').
Proof.
  intros.
  inv H. pose proof sepalg_list.nec_join3 H3 H2.
  destruct H as [r_mapsto'' [r'' [? [? ?]]]].
  eapply pred_nec_hereditary; try eassumption.
  eapply Hw1.
  apply (@address_mapsto_preserve_necR 
    (Share.lub sh1 sh2) lbase m v' _ _ H4) in H0.
  clear dependent r_rem'.
  clear dependent r_mapsto'. clear  dependent r'.
  assert (rsh1: readable_share sh1). 
  { apply writable_readable_share. auto. }
  assert (nsh2: ~ readable_share (Share.glb (Share.comp sh1) sh2)).
  { intros C. eapply join_writable_readable.
    2:{ apply wsh1. } 2:{ apply C. }
    apply two_share_join. }
  inversion H0 as [bm].
  inv H1. inv H3.
  remember (squash (level r_rem,(fun l =>
    if (adr_range_dec lbase (size_chunk m) l) 
    then YES sh1 rsh1 (VAL (nth (Z.to_nat (snd l - snd lbase)) bm Undef)) NoneP
    else (r_mapsto'' @ l)
  ,ghost_of r_mapsto''))) as r_maps1''.
  remember (squash (level r_rem,(fun l =>
    if (adr_range_dec lbase (size_chunk m) l) 
    then YES sh1 rsh1 (VAL (nth (Z.to_nat (snd l - snd lbase)) bl Undef)) NoneP
    else (r_mapsto @ l)
  ,ghost_of r_mapsto))) as r_maps1.
  remember (squash (level r_rem,(fun l =>
    if (adr_range_dec lbase (size_chunk m) l) 
    then NO (Share.glb (Share.comp sh1) sh2) nsh2 
    else identity_resource_of (r_mapsto @ l)
  ,nil))) as r_rem2.

  assert (E1: join r_rem2 r_maps1'' r_mapsto'').
  { apply join_unsquash. subst.
    rewrite !unsquash_squash. split.
    - simpl. apply join_level in H.
       rewrite rmap_level_eq in *.
       constructor;omega.
    - split.
      + simpl. unfold join. unfold Join_pi. 
        intros l. unfold compose. simpl.
        destruct H2 as [[? ?] ?].
        specialize (H3 l). simpl in H3. if_tac.
        { simpl. destruct H3. unfold resource_at in H3.
          rewrite H3. constructor.
          apply join_comm. apply two_share_join. }
        { destruct H1. specialize (H1 l). simpl in H1.
          assert (level r_rem = level r_mapsto).
          { apply join_level in H4. omega. }
          rewrite H8. rewrite identity_resource_at_approx. clear H8.
          assert (level r_mapsto = level r_mapsto'').
          { apply join_level in H. apply join_level in H4. omega. }
          rewrite H8. rewrite resource_at_approx. clear H8.
          unfold resource_at.
          pose proof resource_at_join _ _ _ l H as Et1.
          pose proof resource_at_join _ _ _ l H4 as Et2.
          if_tac in H1; try tauto.
          pose proof H1 _ _ Et2. apply join_comm in Et1.
          pose proof H3 _ _ Et1. rewrite H9 in *. rewrite H10 in *.
          unfold resource_at in Et1, Et2. clear H9. clear H10.
          destruct ((fst (snd (unsquash r_mapsto)) l));simpl;
          destruct ((fst (snd (unsquash r_mapsto'')) l));simpl;try constructor;try apply bot_join_eq; try solve [inv Et1; inv Et2; congruence].
          inv Et1. inv Et2. rewrite H12. rewrite <- H13. constructor.
        }
      + simpl. assert (level r_rem = level r_mapsto'').
        { apply join_level in H. omega. }
        rewrite H3. rewrite ghost_of_approx. unfold ghost_of.
        constructor.
  }

  assert (E2: join r_rem2 r_maps1 r_mapsto).
  { apply join_unsquash. subst.
    rewrite !unsquash_squash. split.
    - simpl. apply join_level in H4.
       rewrite rmap_level_eq in *.
       constructor;omega.
    - split.
      + simpl. unfold join. unfold Join_pi. 
        intros l. unfold compose. simpl.
        destruct H2 as [[? ?] ?].
        destruct H1. specialize (H1 l). simpl in H1.
        if_tac.
        { simpl. destruct H1. unfold resource_at in H1.
          rewrite H1. constructor. apply join_comm.
          apply two_share_join. }
        { assert (level r_rem = level r_mapsto).
          { apply join_level in H4. omega. }
          rewrite H8. rewrite identity_resource_at_approx. clear H8.
          rewrite resource_at_approx. apply join_comm.
          apply identity_resource_of_sem. }
      + simpl. assert (level r_rem = level r_mapsto).
        { apply join_level in H4. omega. }
        rewrite H3. rewrite ghost_of_approx. unfold ghost_of.
        constructor.
  }
  assert (E3: address_mapsto m v' sh1 lbase r_maps1'').
  { rewrite Heqr_maps1''. destruct H2 as [[? ?] ?].
    exists bm. split;[split|].
    - simpl. simpl in H2. auto.
    - intros l. simpl. if_tac.
      { exists rsh1. unfold resource_at. rewrite unsquash_squash.
        simpl. unfold compose. if_tac;try tauto. }
      { unfold resource_at. rewrite unsquash_squash. simpl.
        unfold compose. if_tac; try tauto.
        assert (level r_rem = level r_mapsto'').
        { apply join_level in H. omega. }
        rewrite H8. replace (fst (snd (unsquash r_mapsto'')) l) with
        (r_mapsto'' @ l) by reflexivity.
        rewrite resource_at_approx.
        specialize (H3 l). simpl in H3. if_tac in H3;try tauto. }
    - simpl. unfold ghost_of. rewrite unsquash_squash.
      simpl. 
      assert (level r_rem = level r_mapsto'').
      { apply join_level in H4. apply join_level in H. omega. }
      rewrite H6. rewrite ghost_of_approx. auto.
  }
  

  apply join_comm in H.  apply join_comm in E1. apply join_comm in E2.
  destruct (join_assoc E1 H) as [r_rm [HJ1 HJ2]].
  destruct (join_assoc E2 H4) as [r_rm'' [HJ3 HJ4]].
  assert (r_rm = r_rm'').
  { eapply join_eq;eassumption. }
  subst r_rm''. clear HJ3.
  econstructor.
  4:{ apply join_comm in HJ2. apply HJ2. }
  3:{ apply necR_refl. }
  { apply E3. }
  { exists bl.
    apply cut_resource_exp_intro with 
     (r_mapsto:=r_maps1);auto. subst r_maps1.
    split.
    - intros l. simpl. if_tac.
      { exists rsh1. unfold resource_at. rewrite unsquash_squash.
        simpl. unfold compose. if_tac;try tauto. }
      { unfold resource_at. rewrite unsquash_squash. simpl.
        unfold compose. if_tac; try tauto.
        assert (level r_rem = level r_mapsto).
        { apply join_level in H4. omega. }
        rewrite H6. replace (fst (snd (unsquash r_mapsto)) l) with
        (r_mapsto @ l) by reflexivity.
        rewrite resource_at_approx. destruct H1.
        specialize (H1 l). simpl in H1. if_tac in H1;try tauto. }
    - simpl. unfold ghost_of. rewrite unsquash_squash.
      simpl. 
      assert (level r_rem = level r_mapsto).
      { apply join_level in H4. omega. }
      rewrite H3. rewrite ghost_of_approx. destruct H1. auto.
  }
Qed.


Lemma cut_resource_join: forall sh1 sh2 lbase len r1 r2 r
(rsh1: readable_share sh1) (rsh2: readable_share sh2),
cut_resource_rmap sh1 lbase len r1 r ->
cut_resource_rmap sh2 lbase len r2 r ->
exists r3, cut_resource_rmap (Share.lub sh1 sh2) lbase len r3 r.
Proof.
  intros.
  inversion H as [b1 ? ? H']. subst.
  inversion H0 as [b2 ? ? H0']. subst.
  inversion H' as [r_mapsto1 ? ? Hl1 [Hm1 Hg1] HJ1];subst.
  inversion H0' as [r_mapsto2 ? ? Hl0 [Hm2 Hg2] HJ2];subst.
  assert (rsh:readable_share (Share.lub sh1 sh2)).
  { apply readable_share_lub. auto. }
  assert (JS1: forall l, adr_range lbase (Z.of_nat (Datatypes.length b1)) l -> join_sub sh1 (resourece_share (r @ l))).
  { intros. pose proof resource_at_join _ _ _ l HJ1 as Hl1.
    pose proof Hm1 l as Hml1. hnf in Hml1.
    if_tac in Hml1;try tauto.
    - destruct Hml1. rewrite H3 in Hl1.
      inv Hl1;simpl in *;auto.
      { exists sh3. auto. }
      { exists sh3. auto. }
  }
  assert (JS2: forall l, adr_range lbase (Z.of_nat (Datatypes.length b1)) l -> join_sub sh2 (resourece_share (r @ l))).
  { intros. pose proof resource_at_join _ _ _ l HJ2 as Hl3.
    pose proof Hm2 l as Hml2. hnf in Hml2.
    if_tac in Hml2;try tauto.
    - destruct Hml2. rewrite H3 in Hl3.
      inv Hl3;simpl in *;auto.
      { exists sh3. auto. }
      { exists sh3. auto. }
  }
  exists (squash (level r, (
    (fun l => match (adr_range_dec lbase (Z.of_nat (Datatypes.length b1)) l) with
              | left i => join_rem_of sh1 sh2 (r @ l) (JS1 l i) (JS2 l i)
              | right _ => (r @ l) end),
    ghost_of r1))).
  apply cut_resource_intro with (bl:=b1).
    apply cut_resource_exp_intro with
    (r_mapsto:= (squash (level r, (
      (fun l => if (adr_range_dec lbase (Z.of_nat (Datatypes.length b1)) l)
                then YES (Share.lub sh1 sh2) rsh (VAL (nth (Z.to_nat (snd l - snd lbase)) b1 Undef)) NoneP
                else match (r @ l) with
                | PURE k p => (r @ l)
                | _ => (NO Share.bot bot_unreadable) end),
      ghost_of r_mapsto1))));auto.
    - split.
      2:{ simpl. unfold ghost_of. rewrite unsquash_squash. simpl.
          replace (level r) with (level r_mapsto1).
          2:{ apply join_level in HJ1. tauto.  }
          rewrite ghost_of_approx. auto. }
      intros l.
      pose proof resource_at_join _ _ _ l HJ1 as Hl1.
      pose proof resource_at_join _ _ _ l HJ2 as Hl2.
      pose proof Hm1 l as Hml1. pose proof Hm2 l as Hml2.
      hnf in Hml1, Hml2. hnf. if_tac.
      + hnf. exists rsh. hnf. rewrite rmap_level_eq.
        unfold resource_at. rewrite unsquash_squash. simpl.
        unfold compose. if_tac;try tauto.
      + simpl. unfold resource_at at 1. rewrite unsquash_squash.
        simpl. unfold compose. if_tac;try tauto.
        destruct (r@l);simpl;try apply NO_identity; try apply PURE_identity.
    - apply join_unsquash. constructor.
      + rewrite !unsquash_squash. simpl.
        rewrite rmap_level_eq. constructor;auto.
      + rewrite !unsquash_squash. simpl. constructor.
        { unfold join. unfold Join_pi. intros l.
          pose proof resource_at_join _ _ _ l HJ1 as Hl1.
          pose proof resource_at_join _ _ _ l HJ2 as Hl2.
          pose proof Hm1 l as Hml1. pose proof Hm2 l as Hml2.
          hnf in Hml1. hnf in Hml2.
          simpl. unfold compose. if_tac; simpl.
          * simpl. 
            assert (join_sub sh1 (resourece_share (r@l))).
            { apply JS1. auto. }
            pose proof proof_irr (JS1 l H1) H2. rewrite H3. clear H3.
            clear JS1.
            assert (join_sub sh2 (resourece_share (r@l))).
            { apply JS2. auto. }
            pose proof proof_irr (JS2 l H1) H3. rewrite H4. clear H4.
            clear JS2. unfold join_rem_of.
            destruct (r@l) eqn:E;simpl.
            + destruct (dec_readable);try contradiction.
              destruct Hml1. rewrite H4 in Hl1. inv Hl1.
            + destruct Hml1 as [rsha Hml1], Hml2 as [rshb Hml2].
              rewrite Hml1 in Hl1. rewrite Hml2 in Hl2.
              unfold resource_at in E. rewrite E.
              inv Hl1; inv Hl2;destruct (dec_readable);
              constructor; eapply share_resource_join_aux;eassumption.
            + destruct Hml1 as [rsha Hml1], Hml2 as [rshb Hml2].
              rewrite Hml1 in Hl1. rewrite Hml2 in Hl2. inv Hl1.
          * simpl. 
            replace (fst (snd (unsquash r)) l) with (r@l) by reflexivity.
            destruct (r @ l) eqn:E.
            - simpl. constructor. apply bot_join_eq.
            - rewrite <- E. rewrite resource_at_approx. simpl.
              rewrite E. constructor. apply bot_join_eq.
            - rewrite <- E. rewrite resource_at_approx. simpl.
              rewrite E. constructor.
        }
        { simpl.
          replace (level r) with (level r_mapsto1).
          2:{ apply join_level in HJ1. tauto. }
          rewrite ghost_of_approx.
          replace (level r_mapsto1) with (level r1).
          2:{ apply join_level in HJ1. omega. }
          rewrite ghost_of_approx. apply ghost_of_join.
          auto. }
Qed.


Lemma list_nth_eq': forall {A:Type} (l1 l2: list A) d,
Datatypes.length (rev l1) = Datatypes.length (rev l2) ->
(forall l, (l < Datatypes.length (rev l1))%nat ->
  nth l (rev l1) d = nth l (rev l2) d) ->
l1 = l2.
Proof.
intros. generalize dependent l2.
induction l1.
+ intros. destruct l2;auto.
  simpl in H. rewrite app_length in H. simpl in H. omega.
+ intros. destruct l2.
  * simpl in H. rewrite app_length in H.
    inv H. omega.
  * assert (Datatypes.length (rev l1) = Datatypes.length (rev l2)).
    { rewrite !rev_length. rewrite !rev_length in H.
      simpl in H. inv H. auto. }
    f_equal.
    { specialize (H0 (Datatypes.length l1)).
      simpl in H0. rewrite <-!(rev_length l1) in H0.
      rewrite app_nth2 in H0; try omega.
      rewrite Nat.sub_diag in H0.
      rewrite H1 in H0.
      rewrite app_nth2 in H0; try omega.
      rewrite Nat.sub_diag in H0. simpl in H0.
      apply H0. rewrite <- H1. rewrite app_length.
      simpl. omega. 
    }
    { apply IHl1;auto.
      intros. simpl in H0. specialize (H0 l).
      rewrite app_nth1 in H0;try omega.
      rewrite app_nth1 in H0;try omega.
      apply H0. rewrite app_length. simpl. omega.
    }
Qed.

Lemma list_nth_eq: forall {A:Type} (l1 l2: list A) d,
Datatypes.length l1 = Datatypes.length l2 ->
(forall l, (l < Datatypes.length l1)%nat ->
  nth l l1 d = nth l l2 d) ->
l1 = l2.
Proof.
intros. rewrite <- (rev_involutive l1) in *.
rewrite <- (rev_involutive l2) in *. f_equal.
apply list_nth_eq' with (d0:=d);auto.
Qed.


Lemma address_mapsto_join_value: 
forall sh1 sh2 r1_maps r1_rem r v1 r2_maps r2_rem v2 m lbase,
join r1_maps r1_rem r ->
join r2_maps r2_rem r -> 
address_mapsto m v1 sh1 lbase r1_maps ->
address_mapsto m v2 sh2 lbase r2_maps ->
v1 = v2.
Proof.
intros.
destruct H1 as [bm1 [[[E1a [E1b E1c]] E2] E3]].
destruct H2 as [bm2 [[[E2a [E2b E2c]] E4] E5]].
subst v1 v2.
assert (forall l, adr_range lbase (size_chunk m) l ->
    nth (Z.to_nat (snd l - snd lbase)) bm1 Undef = 
    nth (Z.to_nat (snd l - snd lbase)) bm2 Undef
).
{ intros. specialize (E2 l). specialize (E4 l).
  hnf in E2. hnf in E4. if_tac in E2;try tauto.
  destruct E2. destruct E4.
  apply resource_at_join with (loc:=l) in H.
  apply resource_at_join with (loc:=l) in H0.
  rewrite H3 in H. rewrite H4 in H0.
  inv H0; inv H;
  rewrite <- H11 in H10; inv H10; reflexivity.
}
f_equal. eapply list_nth_eq with (d:=Undef).
+ omega.
+ intros. destruct lbase.
  replace l with (Z.to_nat (snd (b, z + Z.of_nat l) - snd (b, z))).
  2:{ simpl. rewrite <- Nat2Z.id.
      f_equal. omega. }
  apply H1. hnf. split;auto. rewrite E1a in H2.
  unfold size_chunk_nat in H2. rewrite <- (Nat2Z.id l) in H2.
  apply Z2Nat.inj_lt in H2;try omega. destruct m;simpl;omega.
Qed.

Lemma address_mapsto_nonlock_join: forall sh1 sh2 r1_maps r1_rem r v1 r2_maps r2_rem m lbase,
readable_share sh1 -> ~ readable_share sh2 ->
join r1_maps r1_rem r -> 
join r2_maps r2_rem r -> 
address_mapsto m v1 sh1 lbase r1_maps ->
nonlock_permission_bytes sh2 lbase (size_chunk m) r2_maps ->
exists r_maps r_rem, join r_maps r_rem r /\
address_mapsto m v1 (Share.lub sh1 sh2) lbase r_maps.
Proof.
  intros.
  rename H1 into HJ1. rename H2 into HJ2.
  destruct H3 as [bm1 [[[E1a [E1b E1c]] E2] E3]].
  destruct H4.
  assert (rsh:readable_share (Share.lub sh1 sh2)).
  { rewrite Share.lub_commute. apply readable_share_lub. auto. }
  assert (JS1: forall l, adr_range lbase (size_chunk m) l -> join_sub sh1 (resourece_share (r @ l))).
  { intros. pose proof resource_at_join _ _ _ l HJ1 as Hl1.
    pose proof E2 l as Hml1. hnf in Hml1.
    if_tac in Hml1;try tauto.
    - destruct Hml1. rewrite H5 in Hl1.
      inv Hl1;simpl in *;auto.
      { exists sh3. auto. }
      { exists sh3. auto. }
  }
  assert (JS2: forall l, adr_range lbase (size_chunk m) l -> join_sub sh2 (resourece_share (r @ l))).
  { intros. pose proof resource_at_join _ _ _ l HJ2 as Hl3.
    pose proof H1 l as Hml2. hnf in Hml2.
    if_tac in Hml2;try tauto. destruct Hml2. hnf in H5.
    inv Hl3;simpl in *;auto;
    rewrite <- H8 in H5; inv H5; exists sh3; auto.
  }
  exists ((squash (level r, (
    (fun l => if (adr_range_dec lbase (size_chunk m) l)
              then YES (Share.lub sh1 sh2) rsh (VAL (nth (Z.to_nat (snd l - snd lbase)) bm1 Undef)) NoneP
              else match (r @ l) with
              | PURE k p => (r @ l)
              | _ => (NO Share.bot bot_unreadable) end),
    ghost_of r1_maps)))).
  exists (squash (level r, (
    (fun l => match (adr_range_dec lbase (size_chunk m) l) with
              | left i => join_rem_of sh1 sh2 (r @ l) (JS1 l i) (JS2 l i)
              | right _ => (r @ l) end),
    ghost_of r1_rem))).
  split.
  + apply join_unsquash. rewrite unsquash_squash. split;[|split].
    - simpl. rewrite unsquash_squash. simpl. rewrite rmap_level_eq. auto.
    - simpl. rewrite unsquash_squash. simpl. unfold compose. unfold join.
      unfold Join_pi. intros l.
      pose proof resource_at_join _ _ _ l HJ1 as Hl1.
      pose proof resource_at_join _ _ _ l HJ2 as Hl2.
      pose proof E2 l as Hml1. pose proof H1 l as Hml2.
      hnf in Hml1, Hml2. hnf. if_tac;simpl.
      { simpl. 
        assert (join_sub sh1 (resourece_share (r@l))).
        { apply JS1. auto. }
        pose proof proof_irr (JS1 l H3) H4. rewrite H5. clear H5.
        clear JS1.
        assert (join_sub sh2 (resourece_share (r@l))).
        { apply JS2. auto. }
        pose proof proof_irr (JS2 l H3) H5. rewrite H6. clear H6.
        clear JS2. unfold join_rem_of.
        destruct (r@l) eqn:E;simpl.
        + destruct (dec_readable);try contradiction. simpl.
          destruct Hml1. rewrite H6 in Hl1. inv Hl1.
        + destruct Hml1 as [rsha Hml1], Hml2 as [Hml2a Hml2b].
          hnf in Hml2a.
          rewrite Hml1 in Hl1. inv Hl1.
          { inv Hl2;
              rewrite <- H7 in Hml2a; simpl in Hml2a; inv Hml2a;
              destruct (dec_readable);simpl;
              unfold "@" in E; rewrite E; constructor;
                eapply share_resource_join_aux;eassumption. }
          { inv Hl2;
            rewrite <- H7 in Hml2a; simpl in Hml2a; inv Hml2a;
            destruct (dec_readable);simpl;
            unfold "@" in E; rewrite E; constructor;
            eapply share_resource_join_aux;eassumption. }
        + destruct Hml1. hnf in H6. rewrite H6 in Hl1. inv Hl1.
      }
      { replace (fst (snd (unsquash r)) l) with (r@l) by reflexivity.
        destruct (r @ l) eqn:E.
        - simpl. constructor. apply bot_join_eq.
        - rewrite <- E. rewrite resource_at_approx. simpl.
          rewrite E. constructor. apply bot_join_eq.
        - rewrite <- E. rewrite resource_at_approx. simpl.
          rewrite E. constructor.
      }
    - simpl. rewrite unsquash_squash. simpl.
      replace (level r) with (level r1_maps).
      2:{ apply join_level in HJ1. tauto. }
      rewrite ghost_of_approx.
      replace (level r1_maps) with (level r1_rem).
      2:{ apply join_level in HJ1. omega. }
      rewrite ghost_of_approx. apply ghost_of_join. auto.
  + hnf. exists bm1. split;[split|].
    - simpl. auto.
    - intros l. hnf. specialize (E2 l). specialize (H1 l).
      hnf in E2. hnf in H1. if_tac.
      { exists rsh. simpl. unfold resource_at.
        rewrite unsquash_squash. simpl. unfold compose.
        if_tac;try tauto. }
      { simpl. unfold resource_at.
        rewrite unsquash_squash. simpl. unfold compose.
        if_tac;try tauto.
        destruct (fst (snd (unsquash r)) l);simpl;
        try apply NO_identity. apply PURE_identity. }
    - simpl. unfold ghost_of. rewrite unsquash_squash. simpl.
      replace (level r) with (level r1_maps).
      2:{ apply join_level in HJ1. omega.  }
      rewrite ghost_of_approx. auto.
Qed.


Lemma unreadable_share_lub: forall sh1 sh2, 
   ~ readable_share sh1 -> ~ readable_share sh2 ->
   ~ (readable_share (Share.lub sh1 sh2)).
Proof.
  intros.
  intros C. unfold readable_share in *.
  unfold nonempty_share in *. unfold nonidentity in *.
  apply not_not_share_identity in H.
  apply not_not_share_identity in H0.
  apply C. apply identity_share_bot in H. 
  apply identity_share_bot in H0.
  rewrite Share.distrib1. rewrite H. rewrite H0.
  rewrite Share.lub_bot. apply bot_identity.
Qed.


(* Lemma address_nonlock_join: forall sh1 sh2 r1_maps r1_rem r r2_maps r2_rem m lbase,
~ readable_share sh1 -> ~ readable_share sh2 ->
join r1_maps r1_rem r -> 
join r2_maps r2_rem r -> 
nonlock_permission_bytes sh1 lbase (size_chunk m) r1_maps ->
nonlock_permission_bytes sh2 lbase (size_chunk m) r2_maps ->
exists r_maps r_rem, join r_maps r_rem r /\
nonlock_permission_bytes (Share.lub sh1 sh2) lbase (size_chunk m) r_maps. *)


Lemma address_mapsto_join: forall sh1 sh2 r1_maps r1_rem r v1 r2_maps r2_rem v2 m loc,
readable_share sh1 -> readable_share sh2 ->
join r1_maps r1_rem r -> 
join r2_maps r2_rem r -> 
address_mapsto m v1 sh1 loc r1_maps ->
address_mapsto m v2 sh2 loc r2_maps ->
v1 = v2 /\ exists r_maps r_rem, join r_maps r_rem r /\
address_mapsto m v1 (Share.lub sh1 sh2) loc r_maps.
Proof.
intros.
pose proof address_mapsto_join_value
   _ _ _ _ _ _ _ _ _ _ _ H1 H2 H3 H4. split;auto.
subst v2.
destruct H3 as [bm1 [[[E1a [E1b E1c]] E2] E3]].
destruct H4 as [bm2 [[[E2a [E2b E2c]] E4] E5]].
assert (cut_resource_rmap_exp sh1 loc (size_chunk m) bm1 r1_rem r).
{ apply cut_resource_exp_intro 
    with (bl:=bm1) (r_mapsto:=r1_maps);auto.
  { rewrite E1a. unfold size_chunk_nat. rewrite Z2Nat.id;auto. destruct m;simpl;omega. }
  { split;auto. }
}
assert (cut_resource_rmap_exp sh2 loc (size_chunk m) bm2 r2_rem r).
{ apply cut_resource_exp_intro 
    with (bl:=bm2) (r_mapsto:=r2_maps);auto.
  { rewrite E2a. unfold size_chunk_nat. rewrite Z2Nat.id;auto. destruct m;simpl;omega. }
  { split;auto. }
}
apply cut_resource_intro in H3. apply cut_resource_intro in H4.
pose proof cut_resource_join _ _ _ _ _ _ _ H H0 H3 H4.
destruct H5 as [r_rem H5]. pose proof H5 as H5'.
inv H5. inv H6.
exists r_mapsto, r_rem. split;auto.
hnf. exists bl. destruct H5. repeat split;auto.
+ unfold size_chunk_nat.
  rewrite <- (Nat2Z.id (Datatypes.length bl)).
  rewrite Hl. reflexivity.
+ assert (address_mapsto m (decode_val m bl) 
    (Share.lub sh1 sh2) loc r_mapsto).
  { exists bl. repeat split;auto.
    unfold size_chunk_nat.
    rewrite <- (Nat2Z.id (Datatypes.length bl)).
    rewrite Hl. reflexivity. }
  assert (address_mapsto m (decode_val m bm1) sh1
     loc r1_maps).
  { exists bm1. repeat split;auto. }
    pose proof address_mapsto_join_value
    _ _ _ _ _ _ _ _ _ _ _ H1 H7 H9 H8.
    auto.
Qed.


Lemma mapsto_join_andp: forall  sh1 sh2 t p v1 v2,
(* tc_val t v2 -> can't be undefined *)
v1 <> Vundef -> v2 <> Vundef ->
readable_share sh1 -> readable_share sh2 ->
(mapsto sh1 t p v1 * TT) && (mapsto sh2 t p v2 * TT)
|-- EX (sh':share), (mapsto sh' t p v1 * TT) && !!(v1 = v2).
Proof.
  intros sh1 sh2 t p v1 v2 H H0 Hsh1 Hsh2. unfold mapsto.
  assert (E: forall P, FF * TT && (FF * TT) |-- P).
  { rewrite !FF_sepcon. rewrite FF_and.
    apply FF_derives. }
  destruct (access_mode t);auto.
  destruct (type_is_volatile t);auto.
  destruct p;auto.
  if_tac; if_tac; try tauto.
  hnf. intros r.
  intros E0.
  destruct E0 as [Ea Eb].
  destruct Ea as [r1_maps [r1_rem [Ea1 [Eb1 _]]]].
  destruct Eb as [r2_maps [r2_rem [Ea2 [Eb2 _]]]].
  destruct Eb1 as [Eb1 | Eb1].
  2:{ simpl in Eb1. tauto. }
  destruct Eb1 as [Eb1 Ec1].
  destruct Eb2 as [Eb2 | Eb2].
  2:{ simpl in Eb2. tauto. }
  destruct Eb2 as [Eb2 Ec2].
  { pose proof address_mapsto_join
        _ _ _ _ _ _ _ _ _ _ _ H1 H2 Ea1 Ea2 Ec1 Ec2.
    destruct H3. subst v2.
    destruct H4 as [r_maps [r_rem [E1 E2]]].
    exists (Share.lub sh1 sh2).
    if_tac.
    2:{ exfalso. apply H3. apply readable_share_lub. auto. }
    split. 2:{ simpl. auto. }
    exists r_maps, r_rem. repeat split;auto. left.
    split;auto.
  }
Qed.

Lemma mapsto_join_andp_det: forall  sh1 sh2 t p v1 v2,
(* tc_val t v2 -> can't be undefined *)
v1 <> Vundef -> v2 <> Vundef ->
readable_share sh1 -> readable_share sh2 ->
(mapsto sh1 t p v1 * TT) && (mapsto sh2 t p v2 * TT)
|-- (mapsto (Share.lub sh1 sh2) t p v1 * TT) && !!(v1 = v2).
Proof.
  intros sh1 sh2 t p v1 v2 H H0 Hsh1 Hsh2. unfold mapsto.
  assert (E: forall P, FF * TT && (FF * TT) |-- P).
  { rewrite !FF_sepcon. rewrite FF_and.
    apply FF_derives. }
  destruct (access_mode t);auto.
  destruct (type_is_volatile t);auto.
  destruct p;auto.
  if_tac; if_tac; try tauto.
  hnf. intros r.
  intros E0.
  destruct E0 as [Ea Eb].
  destruct Ea as [r1_maps [r1_rem [Ea1 [Eb1 _]]]].
  destruct Eb as [r2_maps [r2_rem [Ea2 [Eb2 _]]]].
  destruct Eb1 as [Eb1 | Eb1].
  2:{ simpl in Eb1. tauto. }
  destruct Eb1 as [Eb1 Ec1].
  destruct Eb2 as [Eb2 | Eb2].
  2:{ simpl in Eb2. tauto. }
  destruct Eb2 as [Eb2 Ec2].
  { pose proof address_mapsto_join
        _ _ _ _ _ _ _ _ _ _ _ H1 H2 Ea1 Ea2 Ec1 Ec2.
    destruct H3. subst v2.
    destruct H4 as [r_maps [r_rem [E1 E2]]].
    if_tac.
    2:{ exfalso. apply H3. apply readable_share_lub. auto. }
    split. 2:{ simpl. auto. }
    exists r_maps, r_rem. repeat split;auto. left.
    split;auto.
  }
Qed.



Lemma mapsto__join_andp_det: forall  sh1 sh2 t p,
(* tc_val t v2 -> can't be undefined *)
(* v1 <> Vundef -> v2 <> Vundef -> *)
readable_share sh1 -> readable_share sh2 ->
(mapsto_ sh1 t p * TT) && (mapsto_ sh2 t p * TT)
|-- (mapsto_ (Share.lub sh1 sh2) t p * TT).
Proof.
  intros sh1 sh2 t p Hsh1 Hsh2. unfold mapsto_. unfold mapsto.
  assert (E: forall P, FF * TT && (FF * TT) |-- P).
  { rewrite !FF_sepcon. rewrite FF_and.
    apply FF_derives. }
  destruct (access_mode t);auto.
  destruct (type_is_volatile t);auto.
  destruct p;auto.
  if_tac; if_tac; try tauto.
  hnf. intros r.
  intros E0.
  destruct E0 as [Ea Eb].
  destruct Ea as [r1_maps [r1_rem [Ea1 [Eb1 _]]]].
  destruct Eb as [r2_maps [r2_rem [Ea2 [Eb2 _]]]].
  destruct Eb1 as [Eb1 | Eb1].
  { exfalso. destruct Eb1. apply tc_val_Vundef in H1. auto. }
  destruct Eb1 as [_ [v1 Ec1]].
  destruct Eb2 as [Eb2 | Eb2].
  { exfalso. destruct Eb2. apply tc_val_Vundef in H1. auto. }
  destruct Eb2 as [_ [v2 Ec2]].
  { pose proof address_mapsto_join
        _ _ _ _ _ _ _ _ _ _ _ H H0 Ea1 Ea2 Ec1 Ec2.
    destruct H1. subst v2.
    destruct H2 as [r_maps [r_rem [E1 E2]]].
    if_tac.
    2:{ exfalso. apply H1. apply readable_share_lub. auto. }
    exists r_maps, r_rem. repeat split;auto. right.
    split. { reflexivity. } exists v1. auto.
  }
Qed.

(* Lemma TODO_mapsto__join_andp_det: forall  sh1 sh2 t p,
(* tc_val t v2 -> can't be undefined *)
(* v1 <> Vundef -> v2 <> Vundef -> *)
(* readable_share sh1 -> readable_share sh2 -> *)
(mapsto_ sh1 t p * TT) && (mapsto_ sh2 t p * TT)
|-- (mapsto_ (Share.lub sh1 sh2) t p * TT). *)



(* 
Lemma mapsto_join_andp_write: forall sh1 sh2 t p P1 P2,
(* tc_val t v2 -> can't be undefined *)
writable_share sh1 -> writable_share sh2 ->
(mapsto_ sh1 t p * (ALL v', mapsto sh1 t p v' -* P1)) && 
(mapsto_ sh2 t p * (ALL v', mapsto sh2 t p v' -* P2))
|-- EX (sh':share), 
(mapsto_ sh' t p * (ALL v', mapsto sh' t p v' -* (P1 && P2))).
Proof.
  intros sh1 sh2 t p P1 P2 Hsh1w Hsh2w. unfold mapsto_. unfold mapsto.
  pose proof writable_readable_share Hsh1w as Hsh1.
  pose proof writable_readable_share Hsh2w as Hsh2.
  destruct (access_mode t); try solve [rewrite FF_sepcon; rewrite FF_and; auto].
  destruct (type_is_volatile t); try solve [rewrite FF_sepcon; rewrite FF_and; auto].
  destruct p; try solve [rewrite FF_sepcon; rewrite FF_and; auto].
  if_tac; try tauto. if_tac; try tauto.
  hnf. intros r.
  intros [E1 E2].
  destruct E1 as [r1_maps [r1_rem [Ea1 [Eb1 Ec1]]]].
  destruct E2 as [r2_maps [r2_rem [Ea2 [Eb2 Ec2]]]].
  destruct Eb1 as [Eb1 | Eb1].
  { destruct Eb1 as [H1 ?]. exfalso. eapply tc_val_Vundef. apply H1. }
  destruct Eb1 as [_ Eb1]. destruct Eb1 as [v1 Eb1].
  destruct Eb2 as [Eb2 | Eb2].
  { destruct Eb2 as [H1 ?]. exfalso. eapply tc_val_Vundef. apply H1. }
  destruct Eb2 as [_ Eb2]. destruct Eb2 as [v2 Eb2].
  { pose proof address_mapsto_join
        _ _ _ _ _ _ _ _ _ _ _ _ Hsh1 Hsh2 Ea1 Ea2 Eb1 Eb2.
    destruct H1. subst v2.
    destruct H2 as [r_maps [r_rem [E1 E2]]].
    assert (EP1: forall v' r', cut_resource_rejoin sh1 
                    (b, Ptrofs.unsigned i) m v' r r' -> P1 r').
    { intros v'. eapply cut_resource_sem.
      exists r1_maps, r1_rem.
      split;auto. split;try eassumption.
      hnf. intros.
      eapply Ec1. { apply H1. } { apply H2. }
      { right. split. 2:{ exists v'. auto. } reflexivity. }
    }
    assert (EP2: forall v' r', cut_resource_rejoin sh2
                    (b, Ptrofs.unsigned i) m v' r r' -> P2 r').
    { intros v'. eapply cut_resource_sem.
      exists r2_maps, r2_rem.
      split;auto. split;try eassumption.
      hnf. intros.
      eapply Ec2. { apply H1. } { apply H2. }
      { right. split. 2:{ exists v'. auto. } reflexivity. }
    }
    exists (Share.lub sh1 sh2).
    if_tac.
    2:{ exfalso. apply H1. apply readable_share_lub. auto. }
    exists r_maps, r_rem. split;auto.
    split.
    - right. split. { simpl. auto. } exists v1. tauto.
    - intros v'.
      pose proof cut_resource_rejoin_merge
         _ _ _ _ _ _ _ Hsh1w Hsh2w EP1 EP2 as T1.
      pose proof cut_resource_rejoin_merge
         _ _ _ _ _ _ _ Hsh2w Hsh1w EP2 EP1 as T2.
      rewrite Share.lub_commute in T2.
      hnf. intros. split.
      { destruct H4.
        + destruct H4. eapply T1 with (v':=v').
          econstructor; try eassumption.
          destruct E2 as [bl [[?E ?E] ?E]]. exists bl.
          econstructor. 3:{ apply E1. }
          2:{ split;auto. }
          destruct E. rewrite size_chunk_conv.
          rewrite H6. reflexivity.
        + destruct H4. clear H4. destruct H5.
          eapply T1 with (v':=x).
          econstructor; try eassumption.
          destruct E2 as [bl [[?E ?E] ?E]]. exists bl.
          econstructor. 3:{ apply E1. }
          2:{ split;auto. }
          destruct E. rewrite size_chunk_conv.
          rewrite H5. reflexivity.
      }
      { destruct H4.
        + destruct H4. eapply T2 with (v':=v').
          econstructor; try eassumption.
          destruct E2 as [bl [[?E ?E] ?E]]. exists bl.
          econstructor. 3:{ apply E1. }
          2:{ split;auto. }
          destruct E. rewrite size_chunk_conv.
          rewrite H6. reflexivity.
        + destruct H4. clear H4. destruct H5.
          eapply T2 with (v':=x).
          econstructor; try eassumption.
          destruct E2 as [bl [[?E ?E] ?E]]. exists bl.
          econstructor. 3:{ apply E1. }
          2:{ split;auto. }
          destruct E. rewrite size_chunk_conv.
          rewrite H5. reflexivity.
      }
  }
Qed. *)

Lemma address_mapsto_join_andp_write:
  forall sh1 sh2 v1 v2 P1 P2 loc m,
  writable_share sh1 ->
  writable_share sh2 ->
    (address_mapsto m v1 sh1 loc *
      (ALL v', address_mapsto m v' sh1 loc -* P1)) &&
    (address_mapsto m v2 sh2 loc *
      (ALL v', address_mapsto m v' sh2 loc -* P2))
  |-- (address_mapsto m v1 (Share.lub sh1 sh2) loc *
      (ALL v', address_mapsto m v' (Share.lub sh1 sh2) loc -*
        (P1 && P2))).
Proof.
  intros. intro r.
  intros [[r1_mapsto [r1_rem [H1_join [H1_mapsto H1_frame]]]]
          [r2_mapsto [r2_rem [H2_join [H2_mapsto H2_frame]]]]].
  pose proof writable_readable_share H as Hr1.
  pose proof writable_readable_share H0 as Hr2.
  pose proof address_mapsto_join 
    _ _ _ _ _ _ _ _ _ _ _ Hr1 Hr2
    H1_join H2_join H1_mapsto H2_mapsto.
  destruct H1. subst v2.
  destruct H2 as [rj_mapsto [rj_rem [Hj_join Hj_mapsto]]].
  exists rj_mapsto, rj_rem. split;[|split];auto.

  intros v'. intros rj_rem'' rj_mapsto'' rj''.
  intros Hj_necR Hj_join'' Hj_mapsto'.
  pose proof sepalg_list.nec_join3 Hj_join'' Hj_necR.
  destruct H1 as [rj_mapsto' [r' [Hj_join' [Hj_necR1 Hj_necR2]]]].
  eapply pred_nec_hereditary; try eassumption.
  apply (@address_mapsto_preserve_necR 
    (Share.lub sh1 sh2) loc m v' _ _ Hj_necR1) in Hj_mapsto'.
  clear dependent rj_rem''.
  clear dependent rj_mapsto''. clear  dependent rj''.


  split.
  { 
    assert (nsh2: ~ readable_share (Share.glb (Share.comp sh1) sh2)).
    { intros C. eapply join_writable_readable.
      2:{ apply H. } 2:{ apply C. }
      apply two_share_join. }
    
    destruct Hj_mapsto as [bl Hj_mapsto].
    destruct Hj_mapsto' as [bl' Hj_mapsto'].

    set (squash (level rj_rem,(fun l =>
      if (adr_range_dec loc (size_chunk m) l) 
      then YES sh1 Hr1 (VAL (nth (Z.to_nat (snd l - snd loc)) bl' Undef)) NoneP
      else (rj_mapsto' @ l)
    ,ghost_of rj_mapsto'))) as r_maps1'.
    (* set (squash (level rj_rem,(fun l =>
      if (adr_range_dec loc (size_chunk m) l) 
      then YES sh1 Hr1 (VAL (nth (Z.to_nat (snd l - snd loc)) bl Undef)) NoneP
      else (rj_mapsto @ l)
      ,ghost_of rj_mapsto))) as r_maps1. *)
    set (squash (level rj_rem,(fun l =>
      if (adr_range_dec loc (size_chunk m) l) 
      then NO (Share.glb (Share.comp sh1) sh2) nsh2 
      else identity_resource_of (rj_mapsto @ l)
      (* else identity_resource_of (r1_mapsto @ l) *)
      ,nil))) as r_rem2.

    assert (E1: join r_rem2 r_maps1' rj_mapsto').
    { apply join_unsquash. subst r_rem2 r_maps1'.
      rewrite !unsquash_squash. split;[|split].
      - simpl. apply join_level in Hj_join'.
        rewrite rmap_level_eq in *.
        constructor;omega.
      - simpl. unfold join. unfold Join_pi. 
        intros l. unfold compose. simpl.
        destruct Hj_mapsto' as [[? ?] ?]. 
        specialize (H2 l). simpl in H2.
        if_tac.
        { simpl. destruct H2. unfold resource_at in H2.
          rewrite H2. constructor.
          apply join_comm. apply two_share_join. }
        { 
          assert (level rj_rem = level rj_mapsto).
          { apply join_level in Hj_join. omega. }
          rewrite H5. 
          rewrite identity_resource_at_approx.
          assert (level rj_mapsto = level rj_mapsto').
          { apply join_level in Hj_join.
            apply join_level in Hj_join'. omega. }
          rewrite H6. rewrite resource_at_approx.
          unfold resource_at. clear H5 H6.
          pose proof resource_at_join _ _ _ l Hj_join as Et1.
          pose proof resource_at_join _ _ _ l Hj_join' as Et2.
          destruct Hj_mapsto as [[? ?] ?].
          specialize (H6 l). simpl in H6.
          if_tac in H6; try tauto.
          pose proof H6 _ _ Et1. apply join_comm in Et2.
          pose proof H2 _ _ Et2. rewrite H9 in *. rewrite H10 in *.
          unfold resource_at in Et1, Et2. clear H9. clear H10.

          destruct ((fst (snd (unsquash rj_mapsto)) l));simpl;
          destruct ((fst (snd (unsquash rj_mapsto')) l));simpl;
          try solve [inv Et1; inv Et2; congruence];
           try constructor;try apply bot_join_eq.

          inv Et1. inv Et2. rewrite H12. rewrite <- H13. constructor.
          (* assert (level rj_rem = level r1_mapsto).
          { apply join_level in H1_join.
          apply join_level in Hj_join. omega. }
          rewrite H5. 
          rewrite identity_resource_at_approx.
          assert (level r1_mapsto = level rj_mapsto').
          { apply join_level in Hj_join.
            apply join_level in Hj_join'. omega. }
          rewrite H6. rewrite resource_at_approx.
          unfold resource_at. clear H5 H6.
          pose proof resource_at_join _ _ _ l H1_join as Et1.
          pose proof resource_at_join _ _ _ l Hj_join as Et2.
          destruct H1_mapsto as [? [[? ?] ?]].
          specialize (H6 l). simpl in H6.
          if_tac in H6; try tauto.
          pose proof H6 _ _ Et1. 
          destruct Hj_mapsto as [[? ?] ?].
          specialize (H11 l). simpl in H11.
          if_tac in H11; try tauto.
          pose proof H11 _ _ Et2. rewrite H9 in *. rewrite H14 in *.
          unfold resource_at in Et1, Et2. clear H9. clear H14.

          destruct ((fst (snd (unsquash r1_mapsto)) l));simpl;
          destruct ((fst (snd (unsquash rj_mapsto)) l));simpl;
          destruct ((fst (snd (unsquash rj_mapsto')) l));simpl;
          try solve [inv Et1; inv Et2; congruence];
           try constructor;try apply bot_join_eq.

          inv Et1. inv Et2. rewrite H12. rewrite <- H13. constructor. *)
        }
      - simpl. assert (level rj_rem = level rj_mapsto').
        { apply join_level in Hj_join'. omega. }
        rewrite H1. rewrite ghost_of_approx. unfold ghost_of.
        constructor.
    }

    (* assert (E2: join r_rem2 r1_mapsto rj_mapsto).
    { apply join_unsquash. subst r_rem2.
      rewrite !unsquash_squash. split;[|split].
      - simpl. apply join_level in Hj_join.
        apply join_level in H1_join.
        rewrite rmap_level_eq in *.
        constructor;omega.
      - simpl. unfold join. unfold Join_pi. 
        intros l. unfold compose. simpl.
        destruct Hj_mapsto as [[? ?] ?].
         specialize (H2 l). simpl in H2.
        if_tac.
        { simpl. destruct H2. unfold resource_at in H2.
          rewrite H2. constructor. apply join_comm.
          apply two_share_join. }
        { assert (level rj_rem = level rj_mapsto).
          { apply join_level in Hj_join. omega. }
          rewrite H5. rewrite identity_resource_at_approx. clear H5.
          rewrite resource_at_approx. apply join_comm.
          apply identity_resource_of_sem. }
      - simpl. assert (level rj_rem = level rj_mapsto).
        { apply join_level in Hj_join. omega. }
        rewrite H1. rewrite ghost_of_approx. unfold ghost_of.
        constructor.
    } *)

    assert (E4: join r_rem2 r1_mapsto rj_mapsto).
    { apply join_unsquash. subst r_rem2.
      rewrite !unsquash_squash. split;[|split].
      - simpl. apply join_level in Hj_join.
        apply join_level in H1_join.
        rewrite rmap_level_eq in *.
        constructor;omega.
      - simpl. unfold join. unfold Join_pi. 
        intros l. unfold compose. simpl.
        destruct H1_mapsto as [? [[? ?] ?]].
         specialize (H2 l). simpl in H2.
        if_tac.
        { simpl. destruct H2. unfold resource_at in H2.
          rewrite H2.
          destruct Hj_mapsto as [[? ?] ?].
          specialize (H6 l). simpl in H6.
          if_tac in H6;try tauto.
          destruct H6. unfold resource_at in H6. rewrite H6.
          

          pose proof resource_at_join _ _ _ l H1_join as Et1.
          pose proof resource_at_join _ _ _ l Hj_join as Et2.
          unfold resource_at in Et1, Et2.
          rewrite H6 in Et2. rewrite H2 in Et1.

          assert ( nth (Z.to_nat (snd l - snd loc)) bl Undef
           =  nth (Z.to_nat (snd l - snd loc)) x Undef).
          { inv Et1; inv Et2; try congruence. }
          rewrite H9. constructor.
          apply join_comm.
          apply two_share_join. }
        { assert (level rj_rem = level rj_mapsto).
          { apply join_level in Hj_join. omega. }
          rewrite H5. rewrite identity_resource_at_approx. clear H5.
          unfold resource_at.
          pose proof resource_at_join _ _ _ l H1_join as Et1.
          pose proof resource_at_join _ _ _ l Hj_join as Et2.
          destruct Hj_mapsto as [[? ?] ?].
          specialize (H6 l). simpl in H6.
          if_tac in H6; try tauto.
          pose proof H2 _ _ Et1. 
          pose proof H6 _ _ Et2. rewrite H9 in *. rewrite H10 in *.
          unfold resource_at in Et1, Et2. clear H9. clear H10.

          destruct ((fst (snd (unsquash rj_mapsto)) l));simpl;
          destruct ((fst (snd (unsquash r1_mapsto)) l));simpl;  try solve [inv Et1; inv Et2; congruence].
          { inv Et1; inv Et2; try congruence. 
            + rewrite <- H11 in H12. inversion H12. subst. 
              constructor.   assert (sh0 = sh).
              { eapply join_canc. apply RJ. apply RJ0. }
              subst. apply bot_join_eq.
            + rewrite <- H11 in H12. inv H12. 
              constructor.   assert (sh0 = sh).
              { eapply join_canc. apply RJ. apply RJ0. }
              subst. apply bot_join_eq.
          }
          { inv Et1; inv Et2; try congruence. 
            + rewrite <- H13 in H11. inv H11.
              assert (sh0 = sh).
              { eapply join_canc. apply RJ. apply RJ0. }
              subst. tauto.
          }
          { inv Et1; inv Et2; try congruence. 
            + rewrite <- H14 in H11. inv H11.
              assert (sh0 = sh).
              { eapply join_canc. apply RJ. apply RJ0. }
              subst. tauto.
          }
          { inv Et1; inv Et2; try congruence. 
            + rewrite <- H13 in H14. inv H14.
              assert (sh0 = sh).
              { eapply join_canc. apply RJ. apply RJ0. }
              subst. constructor. apply bot_join_eq. }
          { inv Et1; inv Et2; try congruence.
            rewrite <- H12 in H13. rewrite H13. constructor. }
        }
      - simpl. assert (level r1_mapsto = level rj_mapsto).
        { apply join_level in Hj_join.
          apply join_level in H1_join. omega. }

        destruct H1_mapsto as [? [[? ?] ?]].
        apply identity_core in H4. unfold ghost_of in H4.
        rewrite ghost_core in H4. rewrite H4.
        destruct Hj_mapsto as [[? ?] ?].
        apply identity_core in H7. unfold ghost_of in H7.
        rewrite ghost_core in H7. rewrite H7. constructor.
    }

    assert (E3: address_mapsto m v' sh1 loc r_maps1').
    { subst r_maps1'. destruct Hj_mapsto' as [[? ?] ?].
      exists bl'. split;[split|].
      - simpl. simpl in H1. auto.
      - intros l. simpl. if_tac.
        { exists Hr1. unfold resource_at. rewrite unsquash_squash.
          simpl. unfold compose. if_tac;try tauto. }
        { unfold resource_at. rewrite unsquash_squash. simpl.
          unfold compose. if_tac; try tauto.
          assert (level rj_rem = level rj_mapsto').
          { apply join_level in Hj_join'. omega. }
          rewrite H6. replace (fst (snd (unsquash rj_mapsto')) l) with
          (rj_mapsto' @ l) by reflexivity.
          rewrite resource_at_approx.
          specialize (H2 l). simpl in H2. if_tac in H2;try tauto. }
      - simpl. unfold ghost_of. rewrite unsquash_squash.
        simpl. 
        assert (level rj_rem = level rj_mapsto').
        { apply join_level in Hj_join'.
          apply join_level in Hj_join. omega. }
        rewrite H4. rewrite ghost_of_approx. auto.
    }   
(* 
    assert (E4: join r1_rem r_maps1' r').
    { apply join_unsquash. subst r_maps1'.
      rewrite !unsquash_squash. split;[|split].
      - simpl. apply join_level in Hj_join'.
        apply join_level in Hj_join.
        apply join_level in H1_join.
        rewrite rmap_level_eq in *.
        constructor;omega.
      - simpl. unfold join. unfold Join_pi. 
        intros l. unfold compose. simpl.
        destruct H1_mapsto as [? [[? ?] ?]].
        specialize (H2 l). simpl in H2.
        if_tac.
        { simpl. destruct H2. unfold resource_at in H2.
          rewrite H2. constructor. apply join_comm.
          apply two_share_join. }
        { assert (level rj_rem = level rj_mapsto).
          { apply join_level in Hj_join. omega. }
          rewrite H5. rewrite identity_resource_at_approx. clear H5.
          rewrite resource_at_approx. apply join_comm.
          apply identity_resource_of_sem. }
      - simpl. assert (level rj_rem = level rj_mapsto).
        { apply join_level in Hj_join. omega. }
        rewrite H1. rewrite ghost_of_approx. unfold ghost_of.
        constructor.
    } *)

    assert (E2: join rj_rem r_rem2 r1_rem).
    { 
      apply join_unsquash. subst r_rem2.
      rewrite !unsquash_squash. split;[|split].
      - simpl. apply join_level in Hj_join.
        apply join_level in H1_join.
        rewrite rmap_level_eq in *.
        constructor;omega.
      - simpl. unfold join. unfold Join_pi. 
        intros l. unfold compose. simpl.
        destruct H1_mapsto as [bl1 [[? ?] ?]].
        destruct Hj_mapsto as [[? ?] ?].
        specialize (H2 l). simpl in H2.
        specialize (H5 l). simpl in H5.
        if_tac.
        { simpl.
          destruct H2. destruct H5.
          pose proof resource_at_join _ _ _ l H1_join as Et1.
          pose proof resource_at_join _ _ _ l Hj_join as Et2.
          rewrite H2 in Et1. rewrite H5 in Et2.
          inv Et1; inv Et2.
          { rewrite <- H13 in H15. inv H15.
            unfold resource_at in H12, H14.
            rewrite <- H12, <- H14.
            constructor.
            
            (* sh3 = sh4 - sh1
               sh5 = sh4 - (sh1 U sh2)
               sh5 + (sh2 - sh1) = 
               sh4 - sh1 = sh3 *)
            admit.
          }
          { assert (writable_share (Share.lub sh1 sh2)).
            { eapply join_writable1;[|apply H].
              apply two_share_join. }
            apply join_writable_readable in RJ0;auto. tauto. }
          { apply join_writable_readable in RJ;auto. tauto. }
          { apply join_writable_readable in RJ;auto. tauto. }
        }
        { assert (level rj_rem = level rj_mapsto).
          { apply join_level in Hj_join. omega. }
          rewrite H8. rewrite identity_resource_at_approx. clear H8.
          unfold resource_at.
          pose proof resource_at_join _ _ _ l H1_join as Et1.
          pose proof resource_at_join _ _ _ l Hj_join as Et2.
          pose proof H2 _ _ Et1. 
          pose proof H5 _ _ Et2. 
          unfold resource_at in *.
          rewrite H9 in *. rewrite H8 in *.
          clear H9. clear H8.

          destruct ((fst (snd (unsquash rj_mapsto)) l));simpl;
          destruct ((fst (snd (unsquash r1_mapsto)) l));simpl;  try solve [inv Et1; inv Et2; congruence].
          { inv Et1; inv Et2; try constructor; try apply join_bot_eq. }
          { inv Et1; inv Et2; try constructor; try apply join_bot_eq. }
          { inv Et1; inv Et2; try constructor; try apply join_bot_eq. }
          { inv Et1; inv Et2; try constructor; try apply join_bot_eq. }
          { inv Et1; inv Et2; try constructor. rewrite <- H11 in H12.
            rewrite H12. constructor. }
        }
      - simpl.
        destruct H1_mapsto as [? [[? ?] ?]].
        destruct Hj_mapsto as [[? ?] ?].
        apply ghost_of_join in H1_join.
        apply ghost_of_join in Hj_join.
        apply H3 in H1_join.
        apply H6 in Hj_join. unfold ghost_of in H1_join, Hj_join.
        rewrite H1_join. rewrite Hj_join. constructor.
    }

    specialize (H1_frame v').
    hnf in H1_frame. eapply H1_frame.
    3:{ apply E3. }
    { apply necR_refl. }

    apply join_comm in Hj_join'. apply join_comm in E1.
    destruct (join_assoc E1 Hj_join') as [r1_rem' [E5 E6]].
    assert (r1_rem' = r1_rem).
    { eapply join_eq. apply E5. apply join_comm. auto. }
    subst r1_rem'. auto.
  }

Admitted.


Lemma mapsto_join_andp_write_det: forall sh1 sh2 t p P1 P2 v',
tc_val t v' -> 
writable_share sh1 -> writable_share sh2 ->
(mapsto_ sh1 t p * (mapsto sh1 t p v' -* P1)) && 
(mapsto_ sh2 t p * (mapsto sh2 t p v' -* P2))
|-- 
(mapsto_ (Share.lub sh1 sh2) t p * (mapsto (Share.lub sh1 sh2) t p v' -* (P1 && P2))).
Proof.
  intros sh1 sh2 t p P1 P2 v' Htc Hsh1w Hsh2w.
  unfold mapsto_. unfold mapsto.
  pose proof writable_readable_share Hsh1w as Hsh1.
  pose proof writable_readable_share Hsh2w as Hsh2.
  destruct (access_mode t); try solve [rewrite FF_sepcon; rewrite FF_and; auto].
  destruct (type_is_volatile t); try solve [rewrite FF_sepcon; rewrite FF_and; auto].
  destruct p; try solve [rewrite FF_sepcon; rewrite FF_and; auto].
  if_tac; try tauto. if_tac; try tauto.
  hnf. intros r.
  intros [E1 E2].
  destruct E1 as [r1_maps [r1_rem [Ea1 [Eb1 Ec1]]]].
  destruct E2 as [r2_maps [r2_rem [Ea2 [Eb2 Ec2]]]].
  destruct Eb1 as [Eb1 | Eb1].
  { destruct Eb1 as [H1 ?]. exfalso. eapply tc_val_Vundef. apply H1. }
  destruct Eb1 as [_ Eb1]. destruct Eb1 as [v1 Eb1].
  destruct Eb2 as [Eb2 | Eb2].
  { destruct Eb2 as [H1 ?]. exfalso. eapply tc_val_Vundef. apply H1. }
  destruct Eb2 as [_ Eb2]. destruct Eb2 as [v2 Eb2].
  { pose proof address_mapsto_join
        _ _ _ _ _ _ _ _ _ _ _ _ Hsh1 Hsh2 Ea1 Ea2 Eb1 Eb2.
    destruct H1. subst v2.
    destruct H2 as [r_maps [r_rem [E1 E2]]].
    assert (EP1: forall r', cut_resource_rejoin sh1 
                    (b, Ptrofs.unsigned i) m v' r r' -> P1 r').
    { clear - Ec1 Ea1 Eb1 Htc.
      eapply cut_resource_sem.
      exists r1_maps, r1_rem.
      split;auto. split;try eassumption.
      hnf. intros.
      eapply Ec1. { apply H. } { apply H0. }
      left. split;auto.
    }
    assert (EP2: forall r', cut_resource_rejoin sh2
                    (b, Ptrofs.unsigned i) m v' r r' -> P2 r').
    { eapply cut_resource_sem.
      exists r2_maps, r2_rem.
      split;auto. split;try eassumption.
      hnf. intros.
      eapply Ec2. { apply H1. } { apply H2. }
      { left. split;auto. }
    }
    if_tac.
    2:{ exfalso. apply H1. apply readable_share_lub. auto. }
    exists r_maps, r_rem. split;auto.
    split.
    - right. split. { simpl. auto. } exists v1. tauto.
    - pose proof cut_resource_rejoin_merge_det
         _ _ _ _ _ _ _ _ Hsh1w Hsh2w EP1 EP2 as T1.
      pose proof cut_resource_rejoin_merge_det
         _ _ _ _ _ _ _ _ Hsh2w Hsh1w EP2 EP1 as T2.
      rewrite Share.lub_commute in T2.
      hnf. intros. split.
      { destruct H4.
        + destruct H4. eapply T1.
          econstructor; try eassumption.
          destruct E2 as [bl [[?E ?E] ?E]]. exists bl.
          econstructor. 3:{ apply E1. }
          2:{ split;auto. }
          destruct E. rewrite size_chunk_conv.
          rewrite H6. reflexivity.
        + destruct H4. simpl in H4. subst v'.
          exfalso. eapply tc_val_Vundef;eassumption.
      }
      { destruct H4.
        + destruct H4. eapply T2.
          econstructor; try eassumption.
          destruct E2 as [bl [[?E ?E] ?E]]. exists bl.
          econstructor. 3:{ apply E1. }
          2:{ split;auto. }
          destruct E. rewrite size_chunk_conv.
          rewrite H6. reflexivity.
        + destruct H4. simpl in H4. subst v'.
        exfalso. eapply tc_val_Vundef;eassumption.
      }
  }
Qed.


Lemma necR_split_1n: forall n r1 r2,
relation_power (S n) age r1 r2 -> exists y, age r1 y /\ necR y r2.
Proof.
intros n. induction n.
- intros. destruct H as [?[? ?]]. exists x. split;auto.
  apply necR_power_age. exists 0%nat. auto.
- intros. destruct H as [?[? ?]].
  apply IHn in H0. exists x. split;auto.
  destruct H0 as [? [? ?]].
  eapply rt_trans;[|apply H1]. apply rt_step. auto.
Qed.



Require Import VST.veric.semax_call.


(* for some reason when p is too complicated, coq will not inversion it *)
Lemma pure_eq_inv: forall p1 p2 k1 k2,
 PURE k1 p1 = PURE k2 p2 -> k1 = k2 /\ p1 = p2.
intros.
inv H. auto.
Qed.



Lemma func_at_unique2: forall r
fsig cc A P1 Q1 NEP1 NEQ1
P2 Q2 NEP2 NEQ2 l,
seplog.func_at (mk_funspec fsig cc A P1 Q1 NEP1 NEQ1) l r ->
seplog.func_at (mk_funspec fsig cc A P2 Q2 NEP2 NEQ2) l r ->
((((box laterM (unfash (fash (ALL ts x vl, (P2 ts x vl  <--> P1 ts x vl)))) r)) /\
( (box laterM (unfash (fash (ALL ts x vl, (Q2 ts x vl <--> Q1 ts x vl)))) r )))).
Proof.
  intros.
  unfold seplog.func_at in *. unfold pureat in *.
  simpl in H, H0. rewrite H in H0.
  apply pure_eq_inv in H0. destruct H0.
  apply function_pointer_aux in H1;auto.
  destruct H1.
  split. 
  { rewrite fash_allp. rewrite semax.unfash_allp. rewrite later_allp.
    intros ts. specialize (H1 ts).
    rewrite fash_allp. rewrite semax.unfash_allp. rewrite later_allp.
    intros x. specialize (H1 x).
    rewrite fash_allp. rewrite semax.unfash_allp. rewrite later_allp.
    intros vl. specialize (H1 vl).
    rewrite later_unfash. auto. }
  { rewrite fash_allp. rewrite semax.unfash_allp. rewrite later_allp.
    intros ts. specialize (H2 ts).
    rewrite fash_allp. rewrite semax.unfash_allp. rewrite later_allp.
    intros x. specialize (H2 x).
    rewrite fash_allp. rewrite semax.unfash_allp. rewrite later_allp.
    intros vl. specialize (H2 vl).
    rewrite later_unfash. auto. }
Qed.


Lemma func_at_unique2_later: forall r
fsig cc A P1 Q1 NEP1 NEQ1
P2 Q2 NEP2 NEQ2 l,
seplog.func_at (mk_funspec fsig cc A P1 Q1 NEP1 NEQ1) l r ->
seplog.func_at (mk_funspec fsig cc A P2 Q2 NEP2 NEQ2) l r ->
((((box laterM 
    (andp (unfash (fash (ALL ts x vl, (P2 ts x vl  <--> P1 ts x vl))))
          (unfash (fash (ALL ts x vl, (Q2 ts x vl <--> Q1 ts x vl))))))
    r))).
Proof.
  intros. rewrite later_andp.
  eapply func_at_unique2.
  { apply H. }
  { apply H0. }
Qed.

(* Lemma func_at_unique2_cor: forall r
fsig cc A P1 Q1 NEP1 NEQ1
P2 Q2 NEP2 NEQ2 l,
seplog.func_at (mk_funspec fsig cc A P1 Q1 NEP1 NEQ1) l r ->
seplog.func_at (mk_funspec fsig cc A P2 Q2 NEP2 NEQ2) l r ->
((((box laterM 
    ( !! corable.corable (ALL ts x vl, (P2 ts x vl  <--> P1 ts x vl)) &&
      (ALL ts x vl, (P2 ts x vl  <--> P1 ts x vl))
)) r)) /\
( (box laterM 
    ( !! corable.corable (ALL ts x vl, (Q2 ts x vl <--> Q1 ts x vl)) &&
     (ALL ts x vl, (Q2 ts x vl <--> Q1 ts x vl))) r ))).
Proof.
  intros.
  pose proof func_at_unique2 _ _ _ _ _ _ _ _ _ _ _ _ _ H H0.
  destruct H1. split.
  { eapply later_derives;[|apply H1].
    apply andp_right;[|apply semax.unfash_fash].
    intro rho'. intros.
Abort. *)

Lemma func_at_unique2': forall r
fsig cc A P1 Q1 NEP1 NEQ1
P2 Q2 NEP2 NEQ2 l,
seplog.func_at (mk_funspec fsig cc A P1 Q1 NEP1 NEQ1) l r ->
seplog.func_at (mk_funspec fsig cc A P2 Q2 NEP2 NEQ2) l r ->
(((forall ts x vl,  (box laterM (unfash (fash (P2 ts x vl <--> P1 ts x vl))) r )) /\
(forall ts x vl,  (box laterM (unfash (fash (Q2 ts x vl <--> Q1 ts x vl))) r )))).
Proof.
  intros.
  unfold seplog.func_at in *. unfold pureat in *.
  simpl in H, H0. rewrite H in H0.
  apply pure_eq_inv in H0. destruct H0.
  apply function_pointer_aux in H1;auto.
  destruct H1.
  split. 
  { intros ts x vl. specialize (H1 ts x vl).
    rewrite <- later_unfash in H1.
    auto.
  }
  { intros ts x vl. specialize (H2 ts x vl).
    rewrite <- later_unfash in H2.
    auto.
  }
  (* { intros ts x vl. specialize (H2 ts x vl).
    rewrite <- later_unfash in H2.
    eapply later_derives. 2:{ apply H2. }
    apply semax.unfash_fash.
  } *)
Qed.

Lemma func_at_unique1: forall r
    { fsig1 cc1 A1 P1 Q1 NEP1 NEQ1
    fsig2 cc2 A2 P2 Q2 NEP2 NEQ2 } l,
    seplog.func_at (mk_funspec fsig1 cc1 A1 P1 Q1 NEP1 NEQ1) l r ->
    seplog.func_at (mk_funspec fsig2 cc2 A2 P2 Q2 NEP2 NEQ2) l r ->
    (fsig1 = fsig2 /\ cc1 = cc2 /\ A1 = A2).
Proof.
intros.
unfold seplog.func_at in *. unfold pureat in *.
simpl in H, H0. rewrite H in H0. inv H0. auto.
Qed.

Require VST.floyd.SeparationLogicFacts.

Definition precise_funspec := 
fun (Delta : seplog.tycontext) (f : funspec) =>
match f with
| mk_funspec fsig0 _ A P R _ _ =>
	forall (bl : environ -> list val) (Q1 Q2 : environ -> mpred)
      (ret : option ident) r,
    (snd fsig0 = Tvoid -> ret = None) ->
    tc_fn_return Delta ret (snd fsig0) ->
    ((EX (ts1 : list Type)
      (x1 : (fix dtfr (T : rmaps.TypeTree) : functor :=
               match T with
               | rmaps.ConstType A0 => fconst A0
               | rmaps.Mpred => fidentity
               | rmaps.DependentType n => fconst (nth n ts1 unit)
               | rmaps.ProdType T1 T2 => fpair (dtfr T1) (dtfr T2)
               | rmaps.ArrowType T1 T2 => ffunc (dtfr T1) (dtfr T2)
               | rmaps.SigType I0 f0 => fsig (fun i : I0 => dtfr (f0 i))
               | rmaps.PiType I0 f0 => fpi (fun i : I0 => dtfr (f0 i))
               | rmaps.ListType T0 => flist (dtfr T0)
               end) A mpred),
      @lift.liftx (lift.Tarrow environ (LiftEnviron mpred)) (P ts1 x1 : environ -> mpred) (SeparationLogic.make_args' fsig0 bl) r *
      SeparationLogicFacts.oboxopt Delta ret (fun rho => maybe_retval (R ts1 x1) (snd fsig0) ret rho -* Q1 rho) r) &&
     (EX (ts2 : list Type)
      (x2 : (fix dtfr (T : rmaps.TypeTree) : functor :=
               match T with
               | rmaps.ConstType A0 => fconst A0
               | rmaps.Mpred => fidentity
               | rmaps.DependentType n => fconst (nth n ts2 unit)
               | rmaps.ProdType T1 T2 => fpair (dtfr T1) (dtfr T2)
               | rmaps.ArrowType T1 T2 => ffunc (dtfr T1) (dtfr T2)
               | rmaps.SigType I0 f0 => fsig (fun i : I0 => dtfr (f0 i))
               | rmaps.PiType I0 f0 => fpi (fun i : I0 => dtfr (f0 i))
               | rmaps.ListType T0 => flist (dtfr T0)
               end) A mpred),
        @lift.liftx (lift.Tarrow environ (LiftEnviron mpred)) (P ts2 x2 : environ -> mpred) (SeparationLogic.make_args' fsig0 bl) r  *
      SeparationLogicFacts.oboxopt Delta ret (fun rho => maybe_retval (R ts2 x2) (snd fsig0) ret rho -* Q2 rho) r))
    |-- (EX (ts : list Type)
         (x : (fix dtfr (T : rmaps.TypeTree) : functor :=
                 match T with
                 | rmaps.ConstType A0 => fconst A0
                 | rmaps.Mpred => fidentity
                 | rmaps.DependentType n => fconst (nth n ts unit)
                 | rmaps.ProdType T1 T2 => fpair (dtfr T1) (dtfr T2)
                 | rmaps.ArrowType T1 T2 => ffunc (dtfr T1) (dtfr T2)
                 | rmaps.SigType I0 f0 => fsig (fun i : I0 => dtfr (f0 i))
                 | rmaps.PiType I0 f0 => fpi (fun i : I0 => dtfr (f0 i))
                 | rmaps.ListType T0 => flist (dtfr T0)
                 end) A mpred),
        @lift.liftx (lift.Tarrow environ (LiftEnviron mpred)) (P ts x : environ -> mpred) (SeparationLogic.make_args' fsig0 bl) r *
         SeparationLogicFacts.oboxopt Delta ret
           (fun rho => maybe_retval (R ts x) (snd fsig0) ret rho -* Q1 rho && Q2 rho) r)
end.

Definition precise_fun_at_ptr (Delta:seplog.tycontext) (v:val) : mpred:= 
  (allp (fun (fs:funspec) =>
  allp (fun (b: block) =>
    imp ((!! (v = Vptr b Ptrofs.zero))  && seplog.func_at fs (b, 0)) 
       (!! (precise_funspec Delta fs) ))))%pred.

Lemma func_ptr_der: forall Delta argsig1 argsig2 retsig cc A1 A2 P1 P2 R1 R2 NEP1 NER1 NEP2 NER2 v,
(( (seplog.func_ptr_si (mk_funspec (argsig1, retsig) cc A1 P1 R1 NEP1 NER1))) v &&
((seplog.func_ptr_si (mk_funspec (argsig2, retsig) cc A2 P2 R2 NEP2 NER2))) v &&  
precise_fun_at_ptr Delta v)
|--
!! (argsig1 = argsig2) &&
(EX (blk_fun: block) (gA : rmaps.TypeTree)
      (gP1 gP2 gR1 gR2 : forall ts : list Type,
      functors.MixVariantFunctor._functor
        (rmaps.dependent_type_functor_rec ts (AssertTT gA)) mpred)  NEgP1 NEgP2 NEgR1 NEgR2,
      !! (v = Vptr blk_fun Ptrofs.zero 
      /\  precise_funspec Delta (mk_funspec (argsig1, retsig) cc gA gP1 gR1 NEgP1 NEgR1)
           ) &&
      ((seplog.func_at (mk_funspec (argsig1, retsig) cc gA gP1 gR1 NEgP1 NEgR1) (blk_fun, 0)) ) &&
      ((seplog.func_at (mk_funspec (argsig1, retsig) cc gA gP2 gR2 NEgP2 NEgR2) (blk_fun, 0)) ) &&
      ((seplog.funspec_sub_si (mk_funspec (argsig1, retsig) cc gA gP1 gR1 NEgP1 NEgR1)
                      (mk_funspec (argsig1, retsig) cc A1 P1 R1 NEP1 NER1))) &&
      ((seplog.funspec_sub_si (mk_funspec (argsig1, retsig) cc gA gP2 gR2 NEgP2 NEgR2)
                      (mk_funspec (argsig1, retsig) cc A2 P2 R2 NEP2 NER2)))).
Proof.
  intros.
  unfold seplog.func_ptr_si.
  repeat rewrite exp_andp1; apply exp_left; intro blk1.
  repeat rewrite andp_assoc; apply prop_andp_left; intros.
  repeat rewrite exp_andp1; apply exp_left; intro gs1.
  rewrite andp_comm.
  repeat rewrite exp_andp1; apply exp_left; intro blk2.
  repeat rewrite andp_assoc; apply prop_andp_left; intros.
  repeat rewrite exp_andp1; apply exp_left; intro gs2.
  rewrite H in H0. inv H0.
  destruct gs1 as [gsig1 gcc1 gA1 gP1 gQ1 gNP1 gNQ1].
  destruct gs2 as [gsig2 gcc2 gA2 gP2 gQ2 gNP2 gNQ2].
  subst. intro r.
  intros [[E1 E2] [E5 [E3 E4]]].
  pose proof func_at_unique1 _ _ E2 E4.
  destruct H as [? [? ?]]. subst.
  pose proof E1 as E1'.
  hnf in E1'. destruct E1' as [Heq E1']. clear E1'.
  pose proof E3 as E3'.
  hnf in E3'. destruct E3' as [Heq' E3']. clear E3'.
  destruct Heq. destruct Heq'. destruct gsig1. inv H.
  inv H1. subst. split. { reflexivity. }
  exists blk2.
  exists gA1, gP1, gP2, gQ1, gQ2.
  exists gNP1, gNP2, gNQ1, gNQ2.
  split;[split|];[split| |];auto. split;auto.
  split;auto.
  specialize (E5 (mk_funspec (argsig1, retsig) cc gA1 gP1 gQ1 gNP1 gNQ1) blk2).
  
  eapply E5. { apply necR_refl. }
  split;auto. reflexivity.
Qed.

Lemma fun_beta: forall {A B:Type} (a: A -> B) y, (fun x => a x) y = a y.
Proof.
  reflexivity.
Qed.

(* Lemma unify_func_at_subsume: forall phi psi1 psi2 addr,
( (seplog.func_at psi1 addr) && (seplog.func_at psi2 addr) &&
  (seplog.funspec_sub_si psi1 phi))
  |-- (seplog.funspec_sub_si psi2 phi).
Proof.
  intros. intro r.
  intros. destruct H. destruct H.
  destruct phi, psi1, psi2.
  pose proof func_at_unique1 _ _ H H1.
  destruct H2 as [? [? ?]]. subst.
  pose proof func_at_unique2 _ _ _ _ _ _ _ _ _ _ _ _ _ H H1.
  destruct H2.
  hnf in H0. hnf.
  destruct H0. destruct H0. subst f. subst c.
  split. { split;reflexivity. }
  intros ts2. intros x2. intros rho'.
  rewrite semax.unfash_allp in H4. specialize (H4 ts2).
  rewrite fun_beta in H4.
  rewrite semax.unfash_allp in H4. specialize (H4 x2).
  rewrite fun_beta in H4.
  rewrite semax.unfash_allp in H4. specialize (H4 rho').
  rewrite fun_beta in H4.
  (* apply semax.unfash_fash in H4. *)
  simpl. intros y Hry a' Hnec.
  specialize (H4 y Hry a' Hnec).
  intros HP. specialize (H4 HP).
  destruct H4 as [ts1 [x1 [F H4]]].
  exists ts1, x1, F. destruct H4 as [E1 E2].
  split. 
  { destruct E1 as [y0 [z [E1a [E1b E1c]]]].
    specialize (H2 ts1 x1 rho').
    simpl in H2.
    Check function_pointer_aux.
    Search seplog.func_at.
  
  }


  Search fash imp.
  apply derives_subp. Search imp derives.  simpl.
  pose proof fash_derives.
  Search fash. *)




(* Lemma func_ptr_der': forall  argsig1 argsig2 retsig cc A1 A2 P1 P2 R1 R2 NEP1 NER1 NEP2 NER2 v,
(( (seplog.func_ptr_si (mk_funspec (argsig1, retsig) cc A1 P1 R1 NEP1 NER1))) v &&
((seplog.func_ptr_si (mk_funspec (argsig2, retsig) cc A2 P2 R2 NEP2 NER2))) v)
|--
!! (argsig1 = argsig2) &&
(EX (blk_fun: address) (gA : rmaps.TypeTree)
      (gP gR : forall ts : list Type,
      functors.MixVariantFunctor._functor
        (rmaps.dependent_type_functor_rec ts (AssertTT gA)) mpred)  NEgP NEgR,
      ((seplog.func_at (mk_funspec (argsig1, retsig) cc gA gP gR NEgP NEgR) blk_fun) ) &&
      ((seplog.funspec_sub_si (mk_funspec (argsig1, retsig) cc gA gP gR NEgP NEgR)
                      (mk_funspec (argsig1, retsig) cc A1 P1 R1 NEP1 NER1))) &&
      ((seplog.funspec_sub_si (mk_funspec (argsig1, retsig) cc gA gP gR NEgP NEgR)
                      (mk_funspec (argsig1, retsig) cc A2 P2 R2 NEP2 NER2)))).
Proof.
  intros.
  unfold seplog.func_ptr_si.
  repeat rewrite exp_andp1; apply exp_left; intro blk1.
  repeat rewrite andp_assoc; apply prop_andp_left; intros.
  repeat rewrite exp_andp1; apply exp_left; intro gs1.
  rewrite andp_comm.
  repeat rewrite exp_andp1; apply exp_left; intro blk2.
  repeat rewrite andp_assoc; apply prop_andp_left; intros.
  repeat rewrite exp_andp1; apply exp_left; intro gs2.
  rewrite H in H0. inv H0.
  destruct gs1 as [gsig1 gcc1 gA1 gP1 gQ1 gNP1 gNQ1].
  destruct gs2 as [gsig2 gcc2 gA2 gP2 gQ2 gNP2 gNQ2].
  subst. intro r.
  intros [[E1 E2] [E3 E4]].
  pose proof func_at_unique1 _ _ E2 E4.
  destruct H as [? [? ?]]. subst.
  pose proof E1 as E1'.
  hnf in E1'. destruct E1' as [Heq E1']. clear E1'.
  pose proof E3 as E3'.
  hnf in E3'. destruct E3' as [Heq' E3']. clear E3'.
  destruct Heq. destruct Heq'. destruct gsig1. inv H.
  inv H1. subst. split. { reflexivity. }
  exists (blk2, 0).
  exists gA1, gP1, gQ1.
  exists gNP1, gNQ1.
  split;[split|];auto.
  
  pose proof func_at_unique2 _ _ _ _ _ _ _ _ _ _ _ _ _ E2 E4.
  destruct H as [HP HQ].
  destruct E3 as [_ E3].
  hnf. split. { split;reflexivity. }
  rewrite semax.unfash_allp. intros ts.
  rewrite semax.unfash_allp in E3. specialize (E3 ts). rewrite fun_beta in E3.
  rewrite semax.unfash_allp. intros x. 
  rewrite semax.unfash_allp in E3. specialize (E3 x).


  rewrite semax.unfash_fash.


  pose proof func_at_unique2.



Qed. *)


Require VST.veric.SeparationLogic.
(* Require Import VST.veric.lift. *)
Require VST.floyd.SeparationLogicFacts.
Require Import VST.veric.extend_tc.
Notation "P '-*' Q" := (wand P Q) : pred.



(* Lemma sepcon_imp_left: forall P Q R W r,
(!! W)%pred  r -> (!! W && P --> R)%pred r ->
(P * Q)%pred r -> (R * Q)%pred r. *)

(* Locate "|>".
Check box.
Print modality.
Check later_andp.
Locate liftx.
Check lift.Lift.


Lemma funspec_rewrite:  forall CS  gA gP gR 
(gNP: super_non_expansive gP) (gNR: super_non_expansive gR)
argsig retsig cc A P R 
(NEP: super_non_expansive P)
(NER: super_non_expansive R)
r bl ts1 x1 ret Q Delta, 
(* ret a bl P Q R r ts1 x1, *)
 seplog.tc_environ Delta r ->
 SeparationLogic.tc_exprlist Delta (snd (split argsig)) bl  &&
liftx (seplog.funspec_sub_si (mk_funspec (argsig, retsig) cc gA gP gR gNP gNR)
(mk_funspec (argsig, retsig) cc A P R NEP NER))
&& (P ts1 x1
(SeparationLogic.make_args' (argsig, retsig)
   (@expr.eval_exprlist CS (snd (split argsig)) bl)) *
   SeparationLogicFacts.oboxopt Delta ret
   (fun rho : environ =>
    wand (maybe_retval (R ts1 x1) retsig ret rho)  (Q rho)))
|-- ((EX ts' x',
  (gP ts' x' 
    (SeparationLogic.make_args' (argsig, retsig)
    (@expr.eval_exprlist CS (snd (split argsig)) bl))) *
  SeparationLogicFacts.oboxopt Delta ret
    (fun rho : environ => 
      wand (maybe_retval (gR ts' x') retsig ret rho)  (Q rho)))). *)



Lemma corable_fash_spec: forall (P: pred nat) (w1:rmap) (w2:rmap), core w1 = core w2 ->
  (! P)%pred w1 -> (! P)%pred w2.
Proof.
  intros.
  pose proof semax.corable_unfash _ _ _ _ _ _ P.
  rewrite corable_spec in H1.
  apply H1 with (x:=w1);auto.
Qed.

Lemma necR_unfash_spec: forall (P: pred rmap) (w1:rmap) (w2:rmap), necR w1 w2 ->
  (! # P)%pred w1 -> (P)%pred w2.
Proof.
  intros. unfold unfash in *. simpl in *.
  pose proof necR_level _ _ H.
  apply H0;auto.
Qed.


(* Lemma oboxopt_K:
  forall (Delta : seplog.tycontext) (i : option ident)
	(P Q : environ -> pred rmap) r,
  derives (P r) (Q r) ->
  derives ((SeparationLogicFacts.oboxopt Delta i P) r)
    (SeparationLogicFacts.oboxopt Delta i Q r).
Admitted. *)


Lemma oboxopt_K':
  forall (Delta : seplog.tycontext) (i : option ident)
	(P Q : environ -> pred rmap) r (w:rmap),
  ((P r w) -> (Q r w)) ->
  (forall i v, (P (env_set r i v) w) -> (Q (env_set r i v) w)) ->
  ((SeparationLogicFacts.oboxopt Delta i P : environ -> pred rmap) r w) ->
    ((SeparationLogicFacts.oboxopt Delta i Q : environ -> pred rmap) r w).
Proof.
  intros. 
  unfold SeparationLogicFacts.oboxopt. destruct i;auto.
  simpl in H1. unfold SeparationLogicFacts.obox in *. simpl in *.
  replace seplog.allp with (@allp rmap ag_rmap val) by reflexivity.
  replace seplog.allp with (@allp rmap ag_rmap val) in H1 by reflexivity.
  intro v. specialize (H1 v). rewrite fun_beta in H1.
  destruct ((seplog.temp_types Delta) ! i );auto.
  replace seplog.imp with (@imp rmap ag_rmap) by reflexivity.
  replace seplog.imp with (@imp rmap ag_rmap) in H1 by reflexivity.

  intros w' E E1.
  pose proof H1 _ (necR_refl _) E1.
  unfold SeparationLogic.subst in  *.
  apply (pred_nec_hereditary _ _ _ E).
  unfold lift.liftx in *. simpl in *.
  unfold lift.lift in *. auto.
Qed.

Lemma oboxopt_sepcon:
  forall (Delta : seplog.tycontext) (i : option ident) (P Q : environ -> mpred) r,
  SeparationLogicFacts.oboxopt Delta i P r * 
  SeparationLogicFacts.oboxopt Delta i Q r 
  |-- SeparationLogicFacts.oboxopt Delta i (fun rho => sepcon (P rho) (Q rho)) r.
Proof.
  intros.
  pose proof SeparationLogicFacts.oboxopt_sepcon Delta i P Q.
  apply H.
Qed.



Lemma funspec_rewrite:  forall CS  gA gP gR 
(gNP: super_non_expansive gP) (gNR: super_non_expansive gR)
argsig retsig cc A P R 
(NEP: super_non_expansive P)
(NER: super_non_expansive R)
r bl ret ts1 x1 Q Delta, 
(* ret a bl P Q R r ts1 x1, *)
 seplog.tc_environ Delta r ->
 SeparationLogic.tc_exprlist Delta (snd (split argsig)) bl r  &&
(seplog.funspec_sub_si (mk_funspec (argsig, retsig) cc gA gP gR gNP gNR)
(mk_funspec (argsig, retsig) cc A P R NEP NER))
&& (P ts1 x1
(SeparationLogic.make_args' (argsig, retsig)
   (@expr.eval_exprlist CS (snd (split argsig)) bl) r) *
   SeparationLogicFacts.oboxopt Delta ret
   (fun rho : environ =>
    wand (maybe_retval (R ts1 x1) retsig ret rho)  (Q rho)) r)    
|-- ((EX ts' x',
  (gP ts' x' 
    (SeparationLogic.make_args' (argsig, retsig)
    (@expr.eval_exprlist CS (snd (split argsig)) bl) r)) *
  SeparationLogicFacts.oboxopt Delta ret
    (fun rho : environ => 
      wand (maybe_retval (gR ts' x') retsig ret rho)  (Q rho)) r)).
Proof.
  intros.
  
  intro w.
  
  
  intros [[E1 E2] E4].
  pose proof assert_lemmas.corable_funspec_sub_si
    (mk_funspec (argsig, retsig) cc gA gP gR gNP gNR)
    (mk_funspec (argsig, retsig) cc A P R NEP NER) as Ecor.

  rewrite corable_spec in Ecor.

  pose proof semax_call.tc_environ_make_args' argsig retsig bl r Delta H _ E1 as Et.
  simpl in Et. destruct E4 as [w1 [w2 [Ejoin [E4 E5]]]].


  (*      w
       /    \
      w1    w2
     / \     \
   w1b w1a   \
    |  |     \
   gP  F   (R -* Q) 
   [x]

   w' = w1a + w2
   w1 |= forall r, forall a a', F * gR --> R

Step 1:
   w' |= forall r, forall a a', F * gR --> R
*)

  assert (Ecor1: core w = core w1).
  { symmetry. apply join_core in Ejoin. auto. }
  pose proof Ecor _ _ Ecor1 E2.

  destruct H0 as [_ E3].
  rewrite semax.unfash_allp in E3. specialize (E3 ts1).
  rewrite fun_beta in E3.
  rewrite semax.unfash_allp in E3. specialize (E3 x1).
  rewrite fun_beta in E3.
  rewrite semax.unfash_allp in E3. 
  specialize (E3 ((SeparationLogic.make_args' (argsig, retsig)
                (expr.eval_exprlist (snd (split argsig)) bl) r))).
  rewrite fun_beta in E3.
  apply semax.unfash_fash in E3.
  unfold imp in E3. 
  specialize (E3 w1 (necR_refl _)).
  destruct E3 as [ts' [x' [F [E3a E3b]]]].
  { split;auto. }
  
  destruct E3a as [w1a [w1b [Ejoin2 [E3a1 E3a2]]]].
  exists ts', x'.
  apply join_comm in Ejoin2.
  destruct (join_assoc Ejoin2 Ejoin) as [w' [Ejoin3 Ejoin4]].
  exists w1b, w'. split;auto. split;auto.

simpl.
  apply oboxopt_K' with (P:= (fun rho : environ =>
    sepcon F (maybe_retval (R ts1 x1) retsig ret rho -* Q rho)%pred)).
  { intros. destruct H0 as [m1 [m2 [Emjoin1 [Em1 Em2]]]].
    hnf. intros w'' m3 m4 EmnecR Emjoin2 Em3.
    (*   
                         m4 |=? Q
                       /   \
         w'  ~~~~~   w''   m3
        / \         / \    | 
       m1 m2      m1' m2'  gR
      /    \      /    \   
    F  (R -* Q) F  (R -* Q)
    *)


    destruct (nec_join2 Emjoin1 EmnecR) as [m1' [m2' [Emjoin3 [EmnecR1 EmnecR2]]]].
    pose proof pred_nec_hereditary _ _ _ EmnecR1 Em1 as Em1'.
    pose proof pred_nec_hereditary _ _ _ EmnecR2 Em2 as Em2'.
    (*   
              m4 |=? Q
            /   \
           w''   m3
          / \    | 
        m1' m2'  gR
        /    \   
       F  (R -* Q)

       m' = m1' + m3 |= F * gR --> R
    *)
    apply join_comm in Emjoin3.
    destruct (join_assoc Emjoin3 Emjoin2) as [m' [Emjoin4 Emjoin5]].
    apply Em2 with (x':=m2') (y:=m');auto.


    rewrite <- semax.unfash_allp in E3b.
    rewrite <- fash_allp in E3b.
    assert (exists m'', necR m'' m' /\ core m'' = core w1).
    { apply join_comm in Emjoin3.
      destruct (nec_join4 _ _ _ _ Emjoin3 EmnecR) as [? [? [? [? ?]]]].
      destruct (sepalg_list.nec_join3 Emjoin4 H1) as [? [? [? [? ?]]]].
      exists x3;split;auto.
      apply join_core in H3. apply join_core in H0.
      apply join_comm in Ejoin4. apply join_core in Ejoin4.
      congruence.
    }
    destruct H0 as [m'' [HnecRm Hcorm]].

    apply corable_fash_spec with (w2 := m'')in E3b;auto.
    apply necR_unfash_spec with (w2 := m')in E3b ;auto.

    (* Ready to use subsumption about post to prove F * gR --> R *)
    (* Case analysis on maybe_retval *)
    unfold maybe_retval. unfold maybe_retval in Em3.
    destruct ret.

    + specialize (E3b (Clight_seplog.get_result1 i r)).
      rewrite fun_beta in E3b.
      specialize (E3b m' (necR_refl _)).
      apply E3b. split.
      { hnf. simpl. split3.
        + hnf. intros. rewrite PTree.gempty in H0. inv H0.
        + hnf. intros. split;intros.
          - rewrite PTree.gempty in H0. inv H0.
          - destruct H0. inv H0.
        + hnf. intros. rewrite PTree.gempty in H0. inv H0. }
      { exists m1', m3;auto. }
    + 
    (* For non-void case *)
    assert (Htmp:
      (EX v : val, gR ts' x'
        (seplog.make_args (Clight_seplog.ret_temp :: nil) (v :: nil) r))%pred m3
      -> (EX v : val, R ts1 x1 
          (seplog.make_args (Clight_seplog.ret_temp :: nil) (v :: nil) r))%pred m').
      { intros E0. simpl in E0.
        destruct E0 as [v E0]. exists v.
        specialize (E3b ((seplog.make_args (Clight_seplog.ret_temp :: nil) (v :: nil) r))).
        rewrite fun_beta in E3b.
        specialize (E3b m' (necR_refl _)).
        apply E3b. split.
        { hnf. simpl. split3.
          + hnf. intros. rewrite PTree.gempty in H0. inv H0.
          + hnf. intros. split;intros.
            - rewrite PTree.gempty in H0. inv H0.
            - destruct H0. inv H0.
          + hnf. intros. rewrite PTree.gempty in H0. inv H0.
        }
        { exists m1', m3. auto. }
      }
    
    destruct retsig;auto. clear Htmp.
    * specialize (E3b (seplog.globals_only r)). rewrite fun_beta in E3b.
      specialize (E3b m' (necR_refl _)).
      apply E3b. split.
      { hnf. simpl. split3.
        + hnf. intros. rewrite PTree.gempty in H0. inv H0.
        + hnf. intros. split;intros.
          - rewrite PTree.gempty in H0. inv H0.
          - destruct H0. inv H0.
        + hnf. intros. rewrite PTree.gempty in H0. inv H0. }
      { exists m1', m3;auto. }
  }
  { intros. destruct H0 as [m1 [m2 [Emjoin1 [Em1 Em2]]]].
    hnf. intros w'' m3 m4 EmnecR Emjoin2 Em3.
    (*   
                         m4 |=? Q
                       /   \
         w'  ~~~~~   w''   m3
        / \         / \    | 
       m1 m2      m1' m2'  gR
      /    \      /    \   
    F  (R -* Q) F  (R -* Q)
    *)


    destruct (nec_join2 Emjoin1 EmnecR) as [m1' [m2' [Emjoin3 [EmnecR1 EmnecR2]]]].
    pose proof pred_nec_hereditary _ _ _ EmnecR1 Em1 as Em1'.
    pose proof pred_nec_hereditary _ _ _ EmnecR2 Em2 as Em2'.
    (*   
              m4 |=? Q
            /   \
           w''   m3
          / \    | 
        m1' m2'  gR
        /    \   
       F  (R -* Q)

       m' = m1' + m3 |= F * gR --> R
    *)
    apply join_comm in Emjoin3.
    destruct (join_assoc Emjoin3 Emjoin2) as [m' [Emjoin4 Emjoin5]].
    apply Em2 with (x':=m2') (y:=m');auto.


    rewrite <- semax.unfash_allp in E3b.
    rewrite <- fash_allp in E3b.
    assert (exists m'', necR m'' m' /\ core m'' = core w1).
    { apply join_comm in Emjoin3.
      destruct (nec_join4 _ _ _ _ Emjoin3 EmnecR) as [? [? [? [? ?]]]].
      destruct (sepalg_list.nec_join3 Emjoin4 H1) as [? [? [? [? ?]]]].
      exists x3;split;auto.
      apply join_core in H3. apply join_core in H0.
      apply join_comm in Ejoin4. apply join_core in Ejoin4.
      congruence.
    }
    destruct H0 as [m'' [HnecRm Hcorm]].

    apply corable_fash_spec with (w2 := m'')in E3b;auto.
    apply necR_unfash_spec with (w2 := m')in E3b ;auto.

    (* Ready to use subsumption about post to prove F * gR --> R *)
    (* Case analysis on maybe_retval *)
    unfold maybe_retval. unfold maybe_retval in Em3.
    destruct ret.

    + specialize (E3b (Clight_seplog.get_result1 i0 (env_set r i v))).
      rewrite fun_beta in E3b.
      specialize (E3b m' (necR_refl _)).
      apply E3b. split.
      { hnf. simpl. split3.
        + hnf. intros. rewrite PTree.gempty in H0. inv H0.
        + hnf. intros. split;intros.
          - rewrite PTree.gempty in H0. inv H0.
          - destruct H0. inv H0.
        + hnf. intros. rewrite PTree.gempty in H0. inv H0. }
      { exists m1', m3;auto. }
    + 
    (* For non-void case *)
    assert (Htmp:
      (EX v : val, gR ts' x'
        (seplog.make_args (Clight_seplog.ret_temp :: nil) (v :: nil) (env_set r i v)))%pred m3
      -> (EX v : val, R ts1 x1 
          (seplog.make_args (Clight_seplog.ret_temp :: nil) (v :: nil) (env_set r i v)))%pred m').
      { intros E0. simpl in E0.
        destruct E0 as [v' E0]. exists v'.
        specialize (E3b ((seplog.make_args (Clight_seplog.ret_temp :: nil) (v' :: nil) (env_set r i v)))).
        rewrite fun_beta in E3b.
        specialize (E3b m' (necR_refl _)).
        apply E3b. split.
        { hnf. simpl. split3.
          + hnf. intros. rewrite PTree.gempty in H0. inv H0.
          + hnf. intros. split;intros.
            - rewrite PTree.gempty in H0. inv H0.
            - destruct H0. inv H0.
          + hnf. intros. rewrite PTree.gempty in H0. inv H0.
        }
        { exists m1', m3. auto. }
      }
    
    destruct retsig;auto. clear Htmp.
    * specialize (E3b (seplog.globals_only r)). rewrite fun_beta in E3b.
      specialize (E3b m' (necR_refl _)).
      apply E3b. split.
      { hnf. simpl. split3.
        + hnf. intros. rewrite PTree.gempty in H0. inv H0.
        + hnf. intros. split;intros.
          - rewrite PTree.gempty in H0. inv H0.
          - destruct H0. inv H0.
        + hnf. intros. rewrite PTree.gempty in H0. inv H0. }
      { exists m1', m3;auto. }
  }
  { apply oboxopt_sepcon. exists w1a, w2. split;auto.
    split;auto.
    unfold SeparationLogicFacts.oboxopt. destruct ret;auto.
    unfold SeparationLogicFacts.obox. simpl.
    replace seplog.allp with (@allp rmap ag_rmap val) by reflexivity.
    intros x. destruct ((seplog.temp_types Delta) ! i ).
    { replace seplog.imp with (@imp rmap ag_rmap) by reflexivity.
      hnf. intros. unfold SeparationLogic.subst.
      apply pred_nec_hereditary with (a:= w1a);auto. }
    { replace seplog.prop with (@prop rmap ag_rmap)by reflexivity.
      simpl. auto. }
  }
Qed.
(* TODO: about this proof,
     can be simplified since proofs for
     [
       ((P r w) -> (Q r w)) ->
       (forall i v, (P (env_set r i v) w) -> (Q (env_set r i v) w)) ->
     ]
     are similar
*)


Lemma func_ptr_self: forall gs fs v blk,
  v = Vptr blk Ptrofs.zero ->
  seplog.funspec_sub_si gs fs &&
  seplog.func_at gs (blk, 0) |--
  SeparationLogic.func_ptr gs v.
Proof.
  intros. intro w.
  intros [E1 E2].
  hnf. exists blk.
  split;auto.
  exists gs.
  split;auto.
  apply seplog.funspec_sub_si_refl.
  auto.
Qed.


Lemma later_andp_aux: forall (P Q : mpred) r,
  (|> P)%pred r ->
  (|> Q)%pred r ->
  (|> andp P Q)%pred r.
Proof.
  intros. rewrite later_andp.
  split;auto.
Qed.

(* Parameter ass: environ -> mpred.
Parameter vl: environ -> environ.
Check @lift.liftx.
Check ((@lift.liftx ass) vl). *)



Lemma func_at_unique_rewrite : forall Delta argsig retsig cc A gP1
gP2 gR1 gR2 NEgP1 NEgP2 NEgR1 NEgR2 address (vl: environ -> environ)  ret Q (r: environ),
(lift.liftx (seplog.func_at (mk_funspec (argsig, retsig) cc A gP2 gR2 NEgP2 NEgR2) address)) r  &&
(lift.liftx (seplog.func_at (mk_funspec (argsig, retsig) cc A gP1 gR1 NEgP1 NEgR1) address)) r  &&
(box laterM (EX ts x, (((@lift.liftx (lift.Tarrow environ (LiftEnviron mpred))  (gP1 ts x : environ -> mpred)) (vl)) r) *    SeparationLogicFacts.oboxopt Delta ret (fun rho => wand (SeparationLogic.maybe_retval (gR1 ts x) retsig ret rho) (Q rho)) r))
|-- (box laterM (EX ts x, (((@lift.liftx (lift.Tarrow environ (LiftEnviron mpred))  (gP2 ts x: environ -> mpred)) (vl)) r) * SeparationLogicFacts.oboxopt Delta ret (fun rho => wand ((SeparationLogic.maybe_retval (gR2 ts x) retsig ret) rho) (Q rho)) r)).
Proof.
  intros. intros w.
  intros [[E1 E2] E3].
  pose proof func_at_unique2_later _ _ _ _ _ _ NEgP1 NEgR1 _ _  NEgP2 NEgR2 _ E2 E1.
  pose proof later_andp_aux _ _ _ E3 H as Eder.
  clear H.
  eapply later_derives. 2:{ apply Eder. }  
  clear Eder.
  intros w'.
  intros [Ew1 [Ew2 Ew3]].

  clear E1 E2 E3.

  destruct Ew1 as [ts [x [w1 [w2 [Ewjoin [Ew1 Ew4]]]]]].
  exists ts, x, w1, w2. split;auto. split.
  { unfold lift.liftx. unfold lift.lift. simpl.
    apply corable_fash_spec with (w2 := w1)in Ew2;auto.
    2:{ apply join_core in Ewjoin;auto. }
    apply semax.unfash_fash in Ew2.
    specialize (Ew2 ts x (vl r)).
    destruct Ew2. apply H0;auto. }
  { apply corable_fash_spec with (w2 := w2)in Ew3;auto.
    2:{ apply join_comm in Ewjoin. apply join_core in Ewjoin;auto. }
    eapply oboxopt_K'.
    3:{ apply Ew4. }
    (*  
        w'           z
      /  \          / \
      w1  w2 ------ x' y
    
      w' |= !# gR1 <-> gR2
      y  |= gR2
      Goal: y |= gR1
    *)
    { simpl. intros.
      apply H with (x' := x') (y := y) (z:= z);auto.
      pose proof pred_nec_hereditary _ _ _ H0 Ew3 as Ew3'.
      apply corable_fash_spec with (w2 := y) in Ew3';auto.
      2:{ apply join_core2 in H1. auto. }
      apply semax.unfash_fash in Ew3'.
      unfold maybe_retval. unfold maybe_retval in H2.
      destruct ret.
      { specialize (Ew3' ts x (Clight_seplog.get_result1 i r)).
        destruct Ew3'. apply H3;auto. }

      (* For non-void case  *)
      assert (Htmp:
      (EX v : val, gR2 ts x
        (seplog.make_args (Clight_seplog.ret_temp :: nil) (v :: nil) r))%pred y
      -> ((EX v : val, gR1 ts x 
        (seplog.make_args (Clight_seplog.ret_temp :: nil) (v :: nil) r))%pred y)).
      { intros E0. simpl in E0.
        destruct E0 as [v' E0]. exists v'.
        specialize (Ew3' ts x (env_set (seplog.globals_only r) Clight_seplog.ret_temp v')).
        apply Ew3';auto. }

      destruct retsig;auto.
      specialize (Ew3' ts x (seplog.globals_only r)).
      apply Ew3';auto.
    }

    { simpl. intros i0 v0. intros.
      apply H with (x' := x') (y := y) (z:= z);auto.
      pose proof pred_nec_hereditary _ _ _ H0 Ew3 as Ew3'.
      apply corable_fash_spec with (w2 := y) in Ew3';auto.
      2:{ apply join_core2 in H1. auto. }
      apply semax.unfash_fash in Ew3'.
      unfold maybe_retval. unfold maybe_retval in H2.
      destruct ret.
      { specialize (Ew3' ts x (Clight_seplog.get_result1 i (env_set r i0 v0))).
        destruct Ew3'. apply H3;auto. }

      (* For non-void case  *)
      assert (Htmp:
      (EX v : val, gR2 ts x
        (seplog.make_args (Clight_seplog.ret_temp :: nil) (v :: nil) r))%pred y
      -> ((EX v : val, gR1 ts x 
        (seplog.make_args (Clight_seplog.ret_temp :: nil) (v :: nil) r))%pred y)).
      { intros E0. simpl in E0.
        destruct E0 as [v' E0]. exists v'.
        specialize (Ew3' ts x (env_set (seplog.globals_only r) Clight_seplog.ret_temp v')).
        apply Ew3';auto. }

      destruct retsig;auto.
      specialize (Ew3' ts x (seplog.globals_only r)).
      apply Ew3';auto.
    }
  }
Qed.