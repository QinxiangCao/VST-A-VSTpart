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

(* Lemma join_necR_aux2: forall n x y z x' y',
relation_power n age x x' -> 
relation_power n age y y' -> join x y z ->
exists z', join x' y' z' /\ relation_power n age z z'.
Proof.
intros n. induction n.
{ intros. simpl in *. subst.
  exists z. split;auto. }
intros.  
apply power_age_age1 in H. simpl in H.
destruct (age1 x) as [x''|] eqn:Ex.
2:{ inversion H. }
apply power_age_age1 in H0. simpl in H0.
destruct (age1 y) as [y''|] eqn:Ey.
2:{ inversion H0. }
pose proof @age1_join _ _ _ _ _ _ _ _ H1 Ex.
destruct H2 as [y''' [z'' [H3 [? ?]]]].
assert (y'' = y''').
{ hnf in H4. congruence. } subst y'''.
Search age join.
exists z''. split.
* auto.
* eapply IHn;try eassumption;apply power_age_age1;auto.
Qed. *)


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


Ltac unfold_Byte_const :=
unfold Byte.max_unsigned in *;
unfold Byte.modulus in *;
unfold two_power_pos in *;
unfold Byte.wordsize in *; simpl in *;
repeat (unfold Int.modulus in *; unfold Int.wordsize in *;
unfold Wordsize_32.wordsize in *; unfold Int.half_modulus in *;
unfold two_power_nat, two_power_pos in *;
unfold Int.max_unsigned, Int.min_signed, Int.max_signed,
Int.zwordsize in *; simpl in *).


Lemma Byte_unsigned_inj: forall i1 i2,
Byte.unsigned i1 = Byte.unsigned i2 -> i1 = i2.
Proof.
intros.
eapply Byte.same_bits_eq; intros.
destruct i1, i2. simpl in *. unfold Byte.testbit.
unfold Byte.unsigned. simpl. rewrite H. reflexivity.
Qed.

Lemma Byte_unsigned_inj_32: forall ia1 ia2 ib1 ib2,
Byte.unsigned ia1 + Byte.unsigned ia2 * 256
 = Byte.unsigned ib1 + Byte.unsigned ib2 * 256-> 
ia1 = ib1 /\ ia2 = ib2.
Proof.
intros.
assert ((Byte.unsigned ia1 + Byte.unsigned ia2 * 256) mod 256
       = ( Byte.unsigned ib1 + Byte.unsigned ib2 * 256) mod 256).
{ rewrite H. reflexivity. }
rewrite !Z_mod_plus_full in H0.
rewrite (Z.mod_small) in H0. 2:{ apply Byte.unsigned_range. }
rewrite (Z.mod_small) in H0. 2:{ apply Byte.unsigned_range. }
apply Byte_unsigned_inj in H0. split;auto.
assert ( Byte.unsigned ia2 = Byte.unsigned ib2).
{ subst. omega. }
apply Byte_unsigned_inj in H1. auto.
Qed.


Lemma decode_byte_deterministic: forall i1 i2,
decode_val Mint8signed (Byte i1 :: nil) = decode_val Mint8signed (Byte i2 :: nil) ->
i1 = i2.
Proof.
intros. unfold decode_val in *.
simpl in H. apply Vint_inj in H.
unfold decode_int in H.
assert (Ht1: rev_if_be (i1 :: nil) = i1::nil).
{ unfold rev_if_be. 
  destruct (Archi.big_endian);auto. }
assert (Ht2: rev_if_be (i2 :: nil) = i2::nil).
  { unfold rev_if_be. 
    destruct (Archi.big_endian);auto. }
rewrite Ht1, Ht2 in *. clear Ht1. clear Ht2.
{ simpl in H. rewrite !Z.add_0_r in H.
  pose proof Byte.unsigned_range i1.
  pose proof Byte.unsigned_range i2.
  remember (Byte.unsigned i1) as v1.
  remember (Byte.unsigned i2) as v2.
  assert (E: 0 < 8 < Int.zwordsize). 
  { unfold_Byte_const. omega. }
  pose proof Int.eqmod_sign_ext _ ((Int.repr v1)) E as E1.
  pose proof Int.eqmod_sign_ext _ ((Int.repr v2)) E as E2.
  rewrite H in E1. apply Zbits.eqmod_sym in E1.
  pose proof Zbits.eqmod_trans _ _ _ _ E1 E2 as E3.
  apply Zbits.eqmod_mod_eq in E3.
  2:{ unfold_Byte_const. omega. }
  rewrite !Int.unsigned_repr_eq in E3.
  unfold_Byte_const.
  assert (v1 = v2).
  { rewrite (Z.mod_small v1 4294967296) in E3; try omega.
    rewrite (Z.mod_small v2 4294967296) in E3; try omega.
    rewrite (Z.mod_small v2 256) in E3; try omega.
    rewrite (Z.mod_small v1 256) in E3; try omega.
  }
  apply Byte_unsigned_inj. rewrite <- Heqv1, <- Heqv2. omega.
}
Qed.


Lemma decode_byte_deterministic_unsigned: forall i1 i2,
decode_val Mint8unsigned (Byte i1 :: nil) = 
decode_val Mint8unsigned (Byte i2 :: nil) ->
i1 = i2.
Proof.
intros. unfold decode_val in *.
simpl in H. apply Vint_inj in H.
unfold decode_int in H.
assert (Ht1: rev_if_be (i1 :: nil) = i1::nil).
{ unfold rev_if_be. 
  destruct (Archi.big_endian);auto. }
assert (Ht2: rev_if_be (i2 :: nil) = i2::nil).
  { unfold rev_if_be. 
    destruct (Archi.big_endian);auto. }
rewrite Ht1, Ht2 in *. clear Ht1. clear Ht2.
{ simpl in H. rewrite !Z.add_0_r in H.
  pose proof Byte.unsigned_range i1.
  pose proof Byte.unsigned_range i2.
  remember (Byte.unsigned i1) as v1.
  remember (Byte.unsigned i2) as v2.
  assert (E: 0 <= 8 < Int.zwordsize). 
  { unfold_Byte_const. omega. }
  pose proof Int.eqmod_zero_ext _ ((Int.repr v1)) E as E1.
  pose proof Int.eqmod_zero_ext _ ((Int.repr v2)) E as E2.
  rewrite H in E1. apply Zbits.eqmod_sym in E1.
  pose proof Zbits.eqmod_trans _ _ _ _ E1 E2 as E3.
  apply Zbits.eqmod_mod_eq in E3.
  2:{ unfold_Byte_const. omega. }
  rewrite !Int.unsigned_repr_eq in E3.
  unfold_Byte_const.
  assert (v1 = v2).
  { rewrite (Z.mod_small v1 4294967296) in E3; try omega.
    rewrite (Z.mod_small v2 4294967296) in E3; try omega.
    rewrite (Z.mod_small v2 256) in E3; try omega.
    rewrite (Z.mod_small v1 256) in E3; try omega.
  }
  apply Byte_unsigned_inj. rewrite <- Heqv1, <- Heqv2. omega.
}
Qed.

Lemma Int_unsign_ext_inj_byte: forall ia1 ia2 ib1 ib2,
Int.zero_ext 16 (Int.repr (int_of_bytes ((ia1 :: ia2 :: nil)))) =
Int.zero_ext 16 (Int.repr (int_of_bytes ((ib1 :: ib2 :: nil)))) ->
ia1 :: ia2 :: nil = ib1 :: ib2 :: nil.
Proof.
intros. 
{ simpl in H. rewrite !Z.add_0_r in H.
  pose proof Byte.unsigned_range ia1.
  pose proof Byte.unsigned_range ia2.
  pose proof Byte.unsigned_range ib1.
  pose proof Byte.unsigned_range ib2.
  remember (Byte.unsigned ia1 + Byte.unsigned ia2 * 256) as v1.
  remember (Byte.unsigned ib1 + Byte.unsigned ib2 * 256) as v2.
  assert (E: 0 <=  16 < Int.zwordsize). 
  { unfold_Byte_const. omega. }
  pose proof Int.eqmod_zero_ext _ ((Int.repr v1)) E as E1.
  pose proof Int.eqmod_zero_ext _ ((Int.repr v2)) E as E2.
  rewrite H in E1. apply Zbits.eqmod_sym in E1.
  pose proof Zbits.eqmod_trans _ _ _ _ E1 E2 as E3.
  apply Zbits.eqmod_mod_eq in E3.
  2:{ unfold_Byte_const. omega. }
  rewrite !Int.unsigned_repr_eq in E3.
  unfold_Byte_const.
  assert (v1 = v2).
  { rewrite (Z.mod_small v1 4294967296) in E3; try omega.
    rewrite (Z.mod_small v2 4294967296) in E3; try omega.
    rewrite (Z.mod_small v2 65536) in E3; try omega.
    rewrite (Z.mod_small v1 65536) in E3; try omega.
  } 
  rewrite Heqv1, Heqv2 in H4.
  apply Byte_unsigned_inj_32 in H4.
  destruct H4;subst. auto.
}
Qed.


Lemma Int_sign_ext_inj_byte: forall ia1 ia2 ib1 ib2,
Int.sign_ext 16 (Int.repr (int_of_bytes ((ia1 :: ia2 :: nil)))) =
Int.sign_ext 16 (Int.repr (int_of_bytes ((ib1 :: ib2 :: nil)))) ->
ia1 :: ia2 :: nil = ib1 :: ib2 :: nil.
Proof.
intros. 
{ simpl in H. rewrite !Z.add_0_r in H.
  pose proof Byte.unsigned_range ia1.
  pose proof Byte.unsigned_range ia2.
  pose proof Byte.unsigned_range ib1.
  pose proof Byte.unsigned_range ib2.
  remember (Byte.unsigned ia1 + Byte.unsigned ia2 * 256) as v1.
  remember (Byte.unsigned ib1 + Byte.unsigned ib2 * 256) as v2.
  assert (E: 0 <  16 < Int.zwordsize). 
  { unfold_Byte_const. omega. }
  pose proof Int.eqmod_sign_ext _ ((Int.repr v1)) E as E1.
  pose proof Int.eqmod_sign_ext _ ((Int.repr v2)) E as E2.
  rewrite H in E1. apply Zbits.eqmod_sym in E1.
  pose proof Zbits.eqmod_trans _ _ _ _ E1 E2 as E3.
  apply Zbits.eqmod_mod_eq in E3.
  2:{ unfold_Byte_const. omega. }
  rewrite !Int.unsigned_repr_eq in E3.
  unfold_Byte_const.
  assert (v1 = v2).
  { rewrite (Z.mod_small v1 4294967296) in E3; try omega.
    rewrite (Z.mod_small v2 4294967296) in E3; try omega.
    rewrite (Z.mod_small v2 65536) in E3; try omega.
    rewrite (Z.mod_small v1 65536) in E3; try omega.
  } 
  rewrite Heqv1, Heqv2 in H4.
  apply Byte_unsigned_inj_32 in H4.
  destruct H4;subst. auto.
}
Qed.


Lemma resource_at_expand_share: forall 
(r1 r2 r : rmap) (sh : share)
(p: preds) l k
(rsh: readable_share sh),
join r1 r2 r -> 
r1 @ l = YES sh rsh k p ->
exists sh' (rsh':readable_share sh'),
join_sub sh sh' /\
r @ l = YES sh' rsh' k p.
Proof.
intros.
pose proof resource_at_join _ _ _ l H.
inv H1; try congruence.
- exists sh3, rsh3.
  rewrite H0 in H3. inv H3.
  split;auto. exists sh2. auto.
- exists sh3, rsh3.
  rewrite H0 in H3. inv H3.
  split;auto. exists sh2. auto.
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

(* TODO: IMPORTANT LEMMA *)

Definition join_sub_share sh1 res :=
match res with
| YES sh _ _ _ | NO sh _ => join_sub sh1 sh
| _ => True
end.

Definition share_of res:= 
match res with
| YES sh _ _ _ | NO sh _ => sh
| _ => Share.top
end.


Lemma join_rem_nsh rall sh1 sh2 
(nsh:  ~ readable_share (share_of rall))
(JS1:join_sub sh1 (share_of rall)) (JS2:join_sub sh2 (share_of rall)) :
~ readable_share (Share.glb (share_of rall) (Share.comp (Share.lub sh1 sh2))).
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


Lemma join_rem_single rall sh1 
(nsh:  ~ readable_share (share_of rall))
(JS1:join_sub sh1 (share_of rall)) :
~ readable_share (Share.glb (share_of rall) (Share.comp sh1)).
Admitted.


Definition join_rem_of sh1 sh2 rall
(JS1:join_sub sh1 (share_of rall))
(JS2:join_sub sh2 (share_of rall)) :=
match rall with
| YES sh rsh k p =>
    let sh' := Share.glb sh (Share.comp (Share.lub sh1 sh2)) in
    match (dec_readable sh') with
    | left rsh' => YES sh' rsh' k p
    | right nsh' => NO sh' nsh'
    end
| NO sh nsh =>
    let sh' := Share.glb (share_of rall) 
        (Share.comp (Share.lub sh1 sh2)) in
    match (dec_readable (share_of rall)) with
    | left rsh' => NO Share.bot bot_unreadable
    | right nsh' =>
        NO sh' (join_rem_nsh rall sh1 sh2 nsh' JS1 JS2)
    end
| PURE k p => PURE k p
end.

Definition join_rem_single_of sh1 rall
(JS1:join_sub sh1 (share_of rall)) :=
match rall with
| YES sh rsh k p =>
    let sh' := Share.glb sh (Share.comp sh1) in
    match (dec_readable sh') with
    | left rsh' => YES sh' rsh' k p
    | right nsh' => NO sh' nsh'
    end
| NO sh nsh =>
    let sh' := Share.glb (share_of rall) 
        (Share.comp sh1) in
    match (dec_readable (share_of rall)) with
    | left rsh' => NO Share.bot bot_unreadable
    | right nsh' =>
        NO sh' (join_rem_single rall sh1 nsh' JS1)
    end
| PURE k p => PURE k p
end.

Local Open Scope pred_derives.


Notation "'ALL' x .. y , P " :=
  (allp (fun x => .. (allp (fun y => P%pred)) ..)) (at level 65, x binder, y binder, right associativity) : pred.


Inductive cut_resource_rmap_exp (sh:share) l (len:Z) (bl: list memval): rmap -> rmap -> Prop :=
| cut_resource_exp_intro: forall r_mapsto r1 r2 (Hl: Z.of_nat (Datatypes.length bl) = len),
  (((ALL y, jam (adr_range_dec l len)
      (fun l' => yesat NoneP (VAL (nth (Z.to_nat (snd l' - snd l)) bl Undef)) sh l') noat y) && noghost) r_mapsto)%pred ->
  join r_mapsto r1 r2 ->
  cut_resource_rmap_exp sh l len bl r1 r2.

Inductive cut_nonlock_rmap_exp (sh:share) l (len:Z) (bl: list memval): rmap -> rmap -> Prop :=
| cut_nonlock_exp_intro: forall r_mapsto r1 r2 (Hl: Z.of_nat (Datatypes.length bl) = len),
(((ALL y, jam (adr_range_dec l len) (fun i : address => shareat i sh && nonlockat i) noat y) && noghost) r_mapsto)%pred ->
join r_mapsto r1 r2 ->
cut_nonlock_rmap_exp sh l len bl r1 r2.




(* Inductive cut_resource_rmap (sh:share) l (len:Z): rmap -> rmap -> Prop :=
| cut_resource_intro: forall (bl: list memval) r_mapsto r1 r2 (Hl: Z.of_nat (Datatypes.length bl) = len),
  ((ALL y, jam (adr_range_dec l len)
      (fun l' => yesat NoneP (VAL (nth (Z.to_nat (snd l' - snd l)) bl Undef)) sh l') noat y) && noghost) r_mapsto ->
  join r_mapsto r1 r2 ->
  cut_resource_rmap sh l len r1 r2. *)

Inductive cut_resource_rmap (sh:share) l (len:Z): rmap -> rmap -> Prop :=
| cut_resource_intro: forall (bl: list memval) r1 r2,
cut_resource_rmap_exp sh l len bl r1 r2 ->
  cut_resource_rmap sh l len r1 r2.

Inductive cut_nonlock_rmap (sh:share) l (len:Z): rmap -> rmap -> Prop :=
| cut_nonlock_intro: forall (bl: list memval) r1 r2,
cut_nonlock_rmap_exp sh l len bl r1 r2 ->
cut_nonlock_rmap sh l len r1 r2.
  

(* Inductive cut_resource_rmap (sh:share) ls: rmap -> rmap -> Prop :=
| cut_resource_intro: forall (b: memval) r_mapsto r1 r2,
  ((ALL y, jam (fun l' => in_dec EqDec_address l' ls)
      (fun l' => yesat NoneP (VAL b) sh l') noat y) && noghost) r_mapsto ->
  join r_mapsto r1 r2 ->
  cut_resource_rmap sh ls r1 r2. *)
(* TODO: b in fact can be any *)

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


(* Lemma cut_resource_rmap_unique_rev: forall sh l len r1 r2 r,
cut_resource_rmap sh l len r r1 ->
cut_resource_rmap sh l len r r2 ->
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
Qed. *)

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


Lemma cut_resource_join: forall sh1 sh2 lbase len r1 r2 r
(rsh1: readable_share sh1) (rsh2: readable_share sh2),
cut_resource_rmap sh1 lbase len r1 r ->
cut_resource_rmap sh2 lbase len r2 r ->
exists r3, cut_resource_rmap (Share.lub sh1 sh2) lbase len r3 r  /\
join_sub r3 r1.
Proof.
  intros.
  inversion H as [b1 ? ? H']. subst.
  inversion H0 as [b2 ? ? H0']. subst.
  inversion H' as [r_mapsto1 ? ? Hl1 [Hm1 Hg1] HJ1];subst.
  inversion H0' as [r_mapsto2 ? ? Hl0 [Hm2 Hg2] HJ2];subst.
  assert (rsh:readable_share (Share.lub sh1 sh2)).
  { apply readable_share_lub. auto. }
  assert (JS1: forall l, adr_range lbase (Z.of_nat (Datatypes.length b1)) l -> join_sub sh1 (share_of (r @ l))).
  { intros. pose proof resource_at_join _ _ _ l HJ1 as Hl1.
    pose proof Hm1 l as Hml1. hnf in Hml1.
    if_tac in Hml1;try tauto.
    - destruct Hml1. rewrite H3 in Hl1.
      inv Hl1;simpl in *;auto.
      { exists sh3. auto. }
      { exists sh3. auto. }
  }
  assert (JS2: forall l, adr_range lbase (Z.of_nat (Datatypes.length b1)) l -> join_sub sh2 (share_of (r @ l))).
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
  split.
  * apply cut_resource_intro with (bl:=b1).
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
            assert (join_sub sh1 (share_of (r@l))).
            { apply JS1. auto. }
            pose proof proof_irr (JS1 l H1) H2. rewrite H3. clear H3.
            clear JS1.
            assert (join_sub sh2 (share_of (r@l))).
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
  * assert (JS3: forall l, adr_range lbase (Z.of_nat (Datatypes.length b1)) l 
      -> join_sub (Share.glb (share_of (r1 @ l)) (Share.comp sh2)) (share_of (r1 @ l))).
    { intros. exists (Share.glb (share_of (r1 @ l)) sh2).
      split.
      - rewrite (Share.glb_commute _ sh2). rewrite Share.glb_assoc. rewrite <- (Share.glb_assoc _ sh2).
        rewrite (Share.glb_commute _ sh2). rewrite Share.comp2. rewrite (Share.glb_commute Share.bot).
        rewrite !Share.glb_bot. reflexivity.
      - rewrite <- Share.distrib1. rewrite (Share.lub_commute _ sh2). rewrite Share.comp1.
        rewrite Share.glb_top. reflexivity.
    }
    exists (squash (level r, (
    (fun l => match (adr_range_dec lbase (Z.of_nat (Datatypes.length b1)) l) with
              | left i => join_rem_single_of (Share.glb (share_of (r1 @ l)) (Share.comp sh2)) (r1 @ l) (JS3 l i)
              | right _ => identity_resource_of (r @ l)
              end,
    ghost_of r1)))).
    apply join_unsquash. constructor.
    + rewrite !unsquash_squash. simpl.
      replace (level r) with (level r1).
      rewrite rmap_level_eq. constructor;auto.
      apply join_level in HJ1. tauto.
    + rewrite !unsquash_squash. simpl. constructor.
      { unfold join. unfold Join_pi. intros l.
        pose proof resource_at_join _ _ _ l HJ1 as Hl1.
        pose proof resource_at_join _ _ _ l HJ2 as Hl2.
        pose proof Hm1 l as Hml1. pose proof Hm2 l as Hml2.
        hnf in Hml1. hnf in Hml2.
        simpl. unfold compose.
        destruct (adr_range_dec lbase (Z.of_nat (Datatypes.length b1)) l).
        * simpl. 
          assert (join_sub sh1 (share_of (r@l))).
          { apply JS1. auto. }
          pose proof proof_irr (JS1 l a) H1. rewrite H2. clear H2.
          clear JS1.
          assert (join_sub sh2 (share_of (r@l))).
          { apply JS2. auto. }
          pose proof proof_irr (JS2 l a) H2. rewrite H3. clear H3.
          clear JS2.
          assert (join_sub (Share.glb (share_of (r1 @ l)) (Share.comp sh2))
          (share_of (r1 @ l))).
          { apply JS3. auto. }
          pose proof proof_irr (JS3 l a) H3. rewrite H4. clear H4.
          clear JS3.
          unfold join_rem_of. unfold join_rem_single_of.
          destruct (r@l) eqn:E;simpl.
          + destruct (dec_readable);try contradiction.
            destruct Hml1. rewrite H4 in Hl1. inv Hl1.
          + destruct Hml1 as [rsha Hml1], Hml2 as [rshb Hml2].
            rewrite Hml1 in Hl1. rewrite Hml2 in Hl2.
            assert (p = (SomeP (rmaps.ConstType unit) (fun _ : list Type => tt))).
            { inversion Hl1; try congruence;auto. }
            subst p.
            destruct (r1@l) eqn:E';simpl.
            - destruct (dec_readable sh0);try contradiction.
              destruct dec_readable;simpl.
              destruct Hml1. Admitted.
(* 
      }
      { simpl.
        replace (level r) with (level r_mapsto1).
        2:{ apply join_level in HJ1. tauto. }
        rewrite ghost_of_approx.
        replace (level r_mapsto1) with (level r1).
        2:{ apply join_level in HJ1. omega. }
        rewrite ghost_of_approx. apply ghost_of_join.
        auto. } *)


(* Lemma cut_resource_sub: forall sh' sh lbase len r1 r,
  join_sub sh' sh ->
  cut_resource_rmap sh lbase len r1 r ->
  exists r2, cut_resource_rmap sh' lbase len r2 r.
Proof.
  intros.
  inversion H0 as [b1 ? ? H']. subst.
  inversion H' as [r_mapsto1 ? ? Hl1 [Hm1 Hg1] HJ1];subst.
  destruct H as [sh_rem H].
  exists (squash (level r, (
    (fun l => if (adr_range_dec lbase (Z.of_nat (Datatypes.length b1)) l) 
              then match (dec_readable sh_rem) with
              | left rsh => YES sh_rem rsh (VAL (nth (Z.to_nat (snd l - snd lbase)) b1 Undef)) NoneP 
              | right nsh =>  NO sh_rem nsh
              end
              else (r @ l)),
    ghost_of r1))).
  apply cut_resource_intro with (bl:=b1).
  apply cut_resource_exp_intro with (r_mapsto:=squash (level r, (
    (fun l => if (adr_range_dec lbase (Z.of_nat (Datatypes.length b1)) l) 
              then match (dec_readable sh') with
              | left rsh => YES sh' rsh (VAL (nth (Z.to_nat (snd l - snd lbase)) b1 Undef)) NoneP 
              | right nsh =>  NO sh' nsh
              end
              else identity_resource_of (r @ l)),
    ghost_of r_mapsto1)));auto;[split|].
  - simpl. intros. if_tac.
    +  intros. split.
   intros.
  
  ) *)





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


Lemma address_mapsto_join: forall sh1 sh2 r1_maps r1_rem r v1 r2_maps r2_rem v2 m b i,
readable_share sh1 -> readable_share sh2 ->
join r1_maps r1_rem r -> 
join r2_maps r2_rem r -> 
address_mapsto m v1 sh1 (b, Ptrofs.unsigned i) r1_maps ->
address_mapsto m v2 sh2 (b, Ptrofs.unsigned i) r2_maps ->
v1 = v2 /\ exists r_maps r_rem, join r_maps r_rem r /\
address_mapsto m v1 (Share.lub sh1 sh2) (b, Ptrofs.unsigned i) r_maps /\
join_sub r_rem r1_rem /\ join_sub r_rem r2_rem.
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
destruct H5 as [r_rem [H5 Ht]]. pose proof H5 as H5'.
inv H5. inv H6.
exists r_mapsto, r_rem. split;auto. split.
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
+ split;auto.
  pose proof cut_resource_join _ _ _ _ _ _ _ H0 H H4 H3.
  destruct H6 as [r_rem' [H6 Ht']].
  rewrite Share.lub_commute in H6.
  rewrite (cut_resource_rmap_unique _ _ _ _ _ _ H6 H5') in *.
  (* use unique + symetric property to avoid redundant proof *)
  auto.
Qed.


(* Lemma address_mapsto_sub: forall sh' sh r1_maps r1_rem r v1 m b i,
join_sub sh' sh ->
join r1_maps r1_rem r -> 
address_mapsto m v1 sh (b, Ptrofs.unsigned i) r1_maps ->
exists r_maps r_rem, join r_maps r_rem r /\
address_mapsto m v1 sh' (b, Ptrofs.unsigned i) r_maps.
Proof.
  intros. *)




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
    tauto.
  }
Qed.

(* Lemma address_mapsto_precise_weak: forall (ch : memory_chunk) (v1 v2 : val) (sh : Share.t) 
  (l : AV.address) (w w1 w2 : rmap),
  address_mapsto ch v1 sh l w1 ->
  address_mapsto ch v2 sh l w2 -> joins w1 w -> joins w2 w -> w1 = w2.
Proof.
  intros.
  destruct H1 as [wa1 H1], H2 as [wa2 H2].
  apply rmap_ext.
  - admit.
  - intros. apply resource_at_join with (loc:=l0) in H1.
    apply resource_at_join with (loc:=l0) in H2.
    destruct H as [bm1 [[E1 E2] E3]], H0 as [bm2 [[E4 E5] E6]].
    specialize (E2 l0). specialize (E5 l0).
    hnf in E2. hnf in E5. if_tac in E2.
    + destruct E2. destruct E5. rewrite H0 in *. rewrite H3 in *.
      f_equal.
    hnf in H. *)



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
  exists (Share.lub sh1 sh2).
  if_tac.
  2:{ exfalso. apply H1. apply readable_share_lub. auto. }
  exists r_maps, r_rem. split;auto.
  split.
  - right. split. { simpl. auto. } exists v1. tauto.
  - intros v'. destruct E2 as [E2 [E3 E4]]. intros r_rem' r_maps' r'.
    intros. split.
    + assert (H5: exists v', address_mapsto m v' (Share.lub sh1 sh2) (b, Ptrofs.unsigned i) r_maps').
      { destruct H4.
        - destruct H4. exists v'. auto.
        - destruct H4. destruct H5. exists x. auto. }
      clear H4 v'.  destruct H5 as [v' H4].
      assert (exists r_maps1' r_maps2',
        join r_maps1' r_maps2' r_maps' /\
        address_mapsto m v' sh1 (b, Ptrofs.unsigned i) r_maps1'
      ) by admit.
      destruct H5 as [r_maps1' [r_maps2' [H5 H6]]].
      assert (exists r_maps2,
        join r1_maps r_maps2 r_maps /\
        ghost_of r_maps2 = ghost_of  r_maps2'
      ) by admit.
      destruct H7 as [r_maps2 [H8 H9]].
      assert (level r_rem = level r_rem') by admit.
      apply join_comm in Ea1.
      assert (r_maps2' = r_maps2).
      { apply rmap_ext.
        - admit.
        - intros. hnf in H6. destruct H6 as [bm1 [[H8a H8b] H8c]].
          destruct Eb1 as [bm2 [[H10a H10b] H10c]].
          apply resource_at_join with (loc:=l) in H5.
          apply resource_at_join with (loc:=l) in H8.
          specialize (H10b l). hnf in H10b.
          specialize (H8b l). hnf in H8b. if_tac in H10b.
          + 
            destruct H8b. destruct H10b. assert (x=x0). { apply proof_irr. }
            subst x0. rewrite H11 in H8. rewrite H10 in H5.
            inv H5; inv H8; try solve [
            pose proof join_writable_readable RJ Hsh1w;
            pose proof join_writable_readable RJ0 Hsh1w; tauto].
            destruct H4 as [bm3 [[H4a H4b] H4c]].
            specialize (H4b l). hnf in H4b. if_tac in H4b;try tauto.
            destruct H4b. rewrite H5 in H17. inv H17.
            destruct E2 as [bm4 [[E2a E2b] E2c]]. specialize (E2b l).
            hnf in E2b. if_tac in E2b;try tauto. destruct E2b.
            rewrite H12 in H18. inv H18. assert (sh3 = sh5).
            { eapply join_canc;apply join_comm;eassumption. }
            subst. f_equal. apply proof_irr.
          + simpl in H8b. apply H8b in H5. rewrite H5.
            apply H10b in H8. rewrite H8.
          simpl in H8b. hnf in H8b.
          admit.
      }
      subst r_maps2'. apply join_comm in H3.
      pose proof join_assoc H5 H3. destruct X as [r_0 [HJ1 HJ2]].
      eapply Ec1 with (y:=r_maps1') (b0:=Vundef).
      3:{ right. split;auto. { simpl. auto. } exists v'. auto. }
      2:{ apply join_comm. apply HJ2. }
      Search necR resource_at.
      Search




  split;auto.
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
