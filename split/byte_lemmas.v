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
intros.  unfold decode_val in *.
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
