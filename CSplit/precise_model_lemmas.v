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
Require Import Csplit.model_lemmas.

Local Open Scope pred_derives.

Lemma join_top_bot_top:
  forall sh1 sh2,
    join Share.top sh1 sh2 ->
    sh2 = Share.top /\ sh1 = Share.bot.
  intros. split.
  - eapply juicy_mem_lemmas.join_top; eauto. 
  - apply not_nonunit_bot.
    intro. apply join_comm in H. 
    destruct H.
    rewrite Share.glb_top in H. subst.
    contradiction (H0 Share.bot); auto.
Qed.

Lemma address_mapsto_join_cancel:
  forall r r_maps r1_rem r2_rem m v loc,
    join r_maps r1_rem r ->
    join r_maps r2_rem r ->
    address_mapsto m v Tsh loc r_maps ->
    r1_rem = r2_rem.
Proof.
  intros r r_maps r1_rem r2_rem m v loc HJ1 HJ2 Ha.
  unfold address_mapsto in Ha.
  destruct Ha as [bl [[[Hl [Hd Hal]] Ha] Hng]].

  apply rmap_ext.
  - apply eq_trans with (level r_maps).
    apply juicy_mem.rmap_join_eq_level.
    exists r. apply join_comm. assumption.
    apply juicy_mem.rmap_join_eq_level.
    exists r. assumption.
  - intro l.
    pose proof resource_at_join r_maps r1_rem r l HJ1 as HJR1.
    pose proof resource_at_join r_maps r2_rem r l HJ2 as HJR2.
    pose proof Ha l.
    unfold jam in H. hnf in H. if_tac in H.
    + destruct H as [Hr ?].
      unfold yesat_raw in H. simpl in H.
      rewrite H in HJR1, HJR2.
      inv HJR1; inv HJR2;
        apply join_top_bot_top in RJ;
        apply join_top_bot_top in RJ0;
        destruct RJ as [-> ->];
        destruct RJ0 as [-> ->].
      * f_equal. apply proof_irr.
      * exfalso; apply bot_unreadable; auto.
      * exfalso; apply bot_unreadable; auto.
      * exfalso; apply bot_unreadable; auto.
    + unfold noat in H.
      simpl in H.
      pose proof @join_unit1_e _ _ _ _ _ _ H HJR1.
      pose proof @join_unit1_e _ _ _ _ _ _ H HJR2.
      rewrite H1, H2. reflexivity.
  - pose proof ghost_of_join r_maps r1_rem r HJ1 as HJG1.
    pose proof ghost_of_join r_maps r2_rem r HJ2 as HJG2.
    unfold noghost in Hng.
    simpl in Hng.
    pose proof @join_unit1_e _ _ _ _ _ _ Hng HJG1.
    pose proof @join_unit1_e _ _ _ _ _ _ Hng HJG2.
    rewrite H, H0. reflexivity.
Qed.

Lemma precise_address_mapsto:
  forall m v loc Q R,
    (address_mapsto m v Tsh loc * Q) &&
    (address_mapsto m v Tsh loc * R)
    |-- address_mapsto m v Tsh loc * (Q && R).
Proof.
  intros. intro r.
  intros [[r1_maps [r1_rem [HJ1 [Ha1 HQ]]]]
          [r2_maps [r2_rem [HJ2 [Ha2 HR]]]]].
  assert (r1_maps = r2_maps).
  { pose proof address_mapsto_precise m v Tsh loc
      r r1_maps r2_maps Ha1 Ha2.
    apply H.
    exists r1_rem; assumption.
    exists r2_rem; assumption. }
  subst r2_maps.
  assert (r1_rem = r2_rem).
  { eapply address_mapsto_join_cancel; eassumption. }
  subst r2_rem.

  exists r1_maps, r1_rem.
  split; [assumption |].
  split; [assumption |].
  split; assumption.
Qed.

Lemma precise_mapsto:
  forall t p v Q R,
    (mapsto Tsh t p v * Q) &&
    (mapsto Tsh t p v * R)
    |-- mapsto Tsh t p v * (Q && R).
Proof.
  intros. unfold mapsto.
  specialize writable_share_top; intro.
  pose proof writable_readable_share H.
  destruct (access_mode t);
    try solve [rewrite FF_sepcon; rewrite FF_and; auto].
  destruct (type_is_volatile t);
    try solve [rewrite FF_sepcon; rewrite FF_and; auto].
  destruct p; try solve [rewrite FF_sepcon; rewrite FF_and; auto].
  if_tac; try tauto. clear H1.
  intro r.
  intros [E1 E2].
  destruct E1 as [r1_maps [r1_rem [Ea1 [Eb1 Ec1]]]].
  destruct E2 as [r2_maps [r2_rem [Ea2 [Eb2 Ec2]]]].
  destruct (Val.eq v Vundef).
  - subst.
    destruct Eb1 as [? | Eb1].
    { destruct H1. exfalso. eapply tc_val_Vundef. apply H1. }
    destruct Eb2 as [? | Eb2].
    { destruct H1. exfalso. eapply tc_val_Vundef. apply H1. }
    destruct Eb1 as [_ [v1 Eb1]].
    destruct Eb2 as [_ [v2 Eb2]].
    pose proof address_mapsto_join_value _ _ _ _ _ _ _ _ _ _ _
      Ea1 Ea2 Eb1 Eb2.
    subst.
    pose proof precise_address_mapsto
      m v2 (b, Ptrofs.unsigned i) Q R r.
    destruct H1 as [r_maps ?].
    { split.
      exists r1_maps, r1_rem. split; auto.
      exists r2_maps, r2_rem. split; auto. }
    destruct H1 as [r_rem [? [? ?]]].
    exists r_maps, r_rem.
    split; auto.
    split; auto.
    right; split; [reflexivity |].
    exists v2; auto.
  - destruct Eb1 as [Eb1 | ?]; [| destruct H1; intuition].
    destruct Eb2 as [Eb2 | ?]; [| destruct H1; intuition].
    destruct Eb1 as [? Eb1].
    destruct Eb2 as [? Eb2].
    pose proof precise_address_mapsto
      m v (b, Ptrofs.unsigned i) Q R r.
    destruct H3 as [r_maps ?].
    { split.
      exists r1_maps, r1_rem. split; auto.
      exists r2_maps, r2_rem. split; auto. }
    destruct H3 as [r_rem [? [? ?]]].
    exists r_maps, r_rem.
    split; auto.
    split; auto.
    left; split; auto.
Qed.

Lemma mapsto_same_value:
  forall t p v1 v2,
    v1 <> Vundef ->
    v2 <> Vundef ->
    (mapsto Tsh t p v1 * TT) &&
    (mapsto Tsh t p v2 * TT)
    |-- !! (v1 = v2).
Proof.
  intros.
  unfold mapsto.
  specialize writable_share_top; intro.
  pose proof writable_readable_share H1.
  destruct (access_mode t);
    try solve [rewrite FF_sepcon; rewrite FF_and; auto].
  destruct (type_is_volatile t);
    try solve [rewrite FF_sepcon; rewrite FF_and; auto].
  destruct p; try solve [rewrite FF_sepcon; rewrite FF_and; auto].
  if_tac; try tauto. clear H3.
  intro r.
  intros [E1 E2].
  destruct E1 as [r1_maps [r1_rem [Ea1 [Eb1 _]]]].
  destruct E2 as [r2_maps [r2_rem [Ea2 [Eb2 _]]]].
  destruct Eb1; [| destruct H3; intuition].
  destruct Eb2; [| destruct H4; intuition].
  destruct H3, H4.
  apply (address_mapsto_join_value _ _ _ _ _ _ _ _ _ _ _
    Ea1 Ea2 H5 H6).
Qed.
