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
(* Import predicates_hered.
Lemma func_ptr_unique: forall phi1 phi2 v,
  (predicates_hered.derives ((func_ptr phi1 v) && (func_ptr phi2 v)) (!! (phi1 = phi2)))%pred.
Proof.
  intros. unfold func_ptr. unfold func_ptr_si.
  rewrite !ex_and. apply predicates_hered.exp_left.
  intros x. rewrite andp_assoc. apply prop_andp_left. intros.
  rewrite !ex_and. apply exp_left. intros gs.
  rewrite andp_comm. rewrite !ex_and. apply exp_left. intros x1.
  rewrite !andp_assoc. apply prop_andp_left. intros.
  rewrite ex_and. apply exp_left. intros gs1.
  rewrite H in H0. inv H0.
Admitted.
Export predicates_hered. *)

Lemma func_at_unique: forall pp1 k1 pp2 k2 l,
  pureat pp1 k1 l && pureat pp2 k2 l |--
  !! (pp1 = pp2 /\ k1 = k2).
Proof.
  intros. intro r. simpl.
  intros. destruct H. rewrite H in H0.

  inv H0. unfold preds_fmap in H3.
  destruct pp1, pp2. simpl in H3. unfold fmap in H3.
  inv H3. apply inj_pair2 in H2.

  (** 01/05/2021
      trying to prove that func_at points to same fun spec
  *)

Admitted.



Lemma join_necR_aux: forall n x y z x' y' z',
relation_power n age x x' -> 
relation_power n age y y' -> join x y z -> join x' y' z' -> 
relation_power n age z z'.
Proof.
intros n. induction n.
{ intros. simpl in *. subst. eapply join_eq;eassumption. }
intros.

apply power_age_age1 in H. simpl in H.
destruct (age1 x) as [x''|] eqn:Ex.
2:{ inversion H. }
apply power_age_age1 in H0. simpl in H0.
destruct (age1 y) as [y''|] eqn:Ey.
2:{ inversion H0. }
pose proof @age1_join _ _ _ _ _ _ _ _ H1 Ex.
destruct H3 as [y''' [z'' [H3 [? ?]]]].
assert (y'' = y''').
{ hnf in H4. congruence. } subst y'''.
exists z''. split.
* auto.
* eapply IHn;try eassumption;apply power_age_age1;auto.
Qed.


Lemma relation_power_level: forall n x y,
 relation_power n age x y -> ((level x) = n + (level y))%nat.
Proof.
intros n. induction n;intros.
{ simpl. hnf in H. f_equal. auto. }
simpl in H. destruct H as [x' [? ?]].
apply IHn in H0. simpl. rewrite <- H0.
apply age_level. auto.
Qed.

Lemma join_necR_same_level: forall m n x y x' y',
relation_power m age x x' -> 
relation_power n age y y' -> level x = level y -> level x' = level y' -> m = n.
Proof.
intros. apply relation_power_level in H. apply relation_power_level in H0.
omega.
Qed.

Lemma join_necR: forall x y z x' y' z',
necR x x' -> 
necR y y' -> join x y z -> join x' y' z' -> 
necR z z'.
Proof.
intros.
pose proof join_level _ _ _ H1 as [E1 E2].
pose proof join_level _ _ _ H2 as [E3 E4].
apply necR_power_age in H. apply necR_power_age in H0.
destruct H as [n1 H], H0 as [n2 H0].
assert (n1 = n2).
{ pose proof join_necR_same_level _ _ _ _ _ _ H H0.
  apply H3;congruence. }
subst n2.
pose proof join_necR_aux _ _ _ _ _ _ _ H H0 H1 H2.
apply necR_power_age. exists n1. auto.
Qed.

Lemma join_necR_2: forall x y z x' y',
necR x x' -> 
necR y y' -> join x y z -> level x' = level y' ->
exists z', join x' y' z' /\ necR z z'.
Proof.
intros.
epose proof nec_join H1 H.
destruct H3 as [y'' [z' [? [? ?]]]].
exists z'. split;auto.
assert (y'' = y').
{ apply (necR_linear' H4 H0).
  apply join_level in H1. apply join_level in H3. omega. }
subst. auto.
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


Lemma address_mapsto_join: forall sh1 sh2 r1_maps r1_rem r v1 r2_maps r2_rem v2 m b i,
readable_share sh1 -> readable_share sh2 ->
join r1_maps r1_rem r -> 
join r2_maps r2_rem r -> 
address_mapsto m v1 sh1 (b, Ptrofs.unsigned i) r1_maps ->
address_mapsto m v2 sh2 (b, Ptrofs.unsigned i) r2_maps ->
v1 = v2 /\ exists r_maps r_rem, join r_maps r_rem r /\
address_mapsto m v1 (Share.lub sh1 sh2) (b, Ptrofs.unsigned i) r_maps.
Proof.
intros.
pose proof address_mapsto_join_value
   _ _ _ _ _ _ _ _ _ _ _ H1 H2 H3 H4. split;auto.
subst v2.
destruct H3 as [bm1 [[[E1a [E1b E1c]] E2] E3]].
destruct H4 as [bm2 [[[E2a [E2b E2c]] E4] E5]].
assert (cut_resource_rmap_exp sh1 (b, Ptrofs.unsigned i) (size_chunk m) bm1 r1_rem r).
{ apply cut_resource_exp_intro 
    with (bl:=bm1) (r_mapsto:=r1_maps);auto.
  { rewrite E1a. unfold size_chunk_nat. rewrite Z2Nat.id;auto. destruct m;simpl;omega. }
  { split;auto. }
}
assert (cut_resource_rmap_exp sh2 (b, Ptrofs.unsigned i) (size_chunk m) bm2 r2_rem r).
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
    (Share.lub sh1 sh2) (b, Ptrofs.unsigned i) r_mapsto).
  { exists bl. repeat split;auto.
    unfold size_chunk_nat.
    rewrite <- (Nat2Z.id (Datatypes.length bl)).
    rewrite Hl. reflexivity. }
  assert (address_mapsto m (decode_val m bm1) sh1
     (b, Ptrofs.unsigned i) r1_maps).
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
        _ _ _ _ _ _ _ _ _ _ _ _ H1 H2 Ea1 Ea2 Ec1 Ec2.
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
        _ _ _ _ _ _ _ _ _ _ _ _ H1 H2 Ea1 Ea2 Ec1 Ec2.
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
        _ _ _ _ _ _ _ _ _ _ _ _ H H0 Ea1 Ea2 Ec1 Ec2.
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
Qed.


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
    { eapply cut_resource_sem.
      exists r1_maps, r1_rem.
      split;auto. split;try eassumption.
      hnf. intros.
      eapply Ec1. { apply H1. } { apply H2. }
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
