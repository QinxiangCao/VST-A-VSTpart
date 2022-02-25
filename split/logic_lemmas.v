Require Import VST.veric.mpred.
Require Import VST.veric.compcert_rmaps.
Require Import Split.model_lemmas.
Require Import VST.veric.seplog.
Require Import VST.msl.seplog.
(* Require Import VST.floyd.proofauto. *)
Require Import VST.veric.expr.
Require Import VST.veric.lift.
Import Ctypes LiftNotation.
Local Open Scope logic.


(* Lemma exp_rewrite: forall (T:Type) (H: ageable.ageable T) B x, 
@predicates_hered.exp T H B x = @exp (predicates_hered.pred T) 
  (algNatDed T) B x.
Proof.
  reflexivity.
Qed.

Lemma allp_rewrite: forall (T:Type) (H: ageable.ageable T) B x, 
@predicates_hered.allp T H B x = @allp (predicates_hered.pred T) 
  (algNatDed T) B x.
Proof.
  reflexivity.
Qed.

Lemma andp_rewrite: (forall (T:Type) (H: ageable.ageable T) x y, 
@predicates_hered.andp T H x y = @andp (predicates_hered.pred T) 
    (algNatDed T) x y).
Proof.
    reflexivity.
Qed.


Lemma imp_rewrite: (forall (T:Type) (H: ageable.ageable T) x y, 
@predicates_hered.imp T H x y = @imp (predicates_hered.pred T) 
    (algNatDed T) x y).
Proof.
    reflexivity.
Qed.

Lemma prop_rewrite: (forall (T:Type) (H: ageable.ageable T) x,  
@predicates_hered.prop T H x = @prop (predicates_hered.pred T) 
  (algNatDed T) x).
Proof.
  reflexivity.
Qed.

Lemma derives_rewrite: forall P Q,
  predicates_hered.derives P Q ->
  @derives
  (@predicates_hered.pred compcert_rmaps.RML.R.rmap
     compcert_rmaps.RML.R.ag_rmap) Nveric P Q.
Proof.
  intros.
  auto.
Qed. *)


Lemma func_at_unique1_lift: forall
  fsig1 cc1 A1 P1 Q1 NEP1 NEQ1
  fsig2 cc2 A2 P2 Q2 NEP2 NEQ2 l,
  func_at (mk_funspec fsig1 cc1 A1 P1 Q1 NEP1 NEQ1) l &&
  func_at (mk_funspec fsig2 cc2 A2 P2 Q2 NEP2 NEQ2) l
  |-- !! (fsig1 = fsig2 /\ cc1 = cc2 /\ A1 = A2).
Proof.
  intros.  intro r. intros. destruct H.
  eapply func_at_unique1.
  - apply H.
  - apply H0.
Qed.

(* Lemma func_at_unique2_logic: forall
fsig cc A P1 Q1 NEP1 NEQ1
P2 Q2 NEP2 NEQ2 l ts x vl,
func_at (mk_funspec fsig cc A P1 Q1 NEP1 NEQ1) l &&
func_at (mk_funspec fsig cc A P2 Q2 NEP2 NEQ2) l 
|--  
  func_at (mk_funspec fsig cc A P1 Q1 NEP1 NEQ1) l &&
  func_at (mk_funspec fsig cc A P2 Q2 NEP2 NEQ2) l &&
  (|> ((P2 ts x : environ -> mpred) vl <--> P1 ts x vl)) &&
     (|> ((Q2 ts x : environ -> mpred) vl <--> Q1 ts x vl))
.
intros.
intro r. intros.
destruct H. pose proof H0 as H0'.
 eapply func_at_unique2 in H0. 2:{ apply H. }
 destruct H0.
 pose proof H0 ts x vl.
 pose proof H1 ts x vl.
rewrite <- later_unfash in H2, H3.
clear H0 H1.
assert (
  (|> ! (P2 ts x vl <=> P1 ts x vl)) |-- 
  (|> (P2 ts x vl <--> P1 ts x vl)))%pred.
Check log_normalize.later_derives.
Search box laterM.
apply semax.unfash_fash.
assert (
  (|> ! (Q2 ts x vl <=> Q1 ts x vl)) |-- 
  (|> (Q2 ts x vl <--> Q1 ts x vl))).
apply later_derives.
apply semax.unfash_fash.
split;auto. split;auto.
split;auto.
Qed.

Lemma func_at_unique2_logic': forall
fsig cc A P1 Q1 NEP1 NEQ1
P2 Q2 NEP2 NEQ2 l ts x vl,
func_at (mk_funspec fsig cc A P1 Q1 NEP1 NEQ1) l &&
func_at (mk_funspec fsig cc A P2 Q2 NEP2 NEQ2) l 
|--  
  func_at (mk_funspec fsig cc A P1 Q1 NEP1 NEQ1) l &&
  func_at (mk_funspec fsig cc A P2 Q2 NEP2 NEQ2) l &&
  (|> ((P2 ts x : environ -> mpred) vl <--> P1 ts x vl)) &&
     (|> ((Q2 ts x : environ -> mpred) vl <--> Q1 ts x vl))
.
Proof.
  intros. Locate derives.
  pose proof func_at_unique2_logic fsig. cc A P1 Q1 NEP1 NEQ1
  P2 Q2 NEP2 NEQ2 l ts x vl as E.
  rewrite !andp_rewrite in E.
  apply E.
Qed. *)


Lemma typ_of_params_eq_inv:
forall argsig1 argsig2,
 type_of_params argsig1 = type_of_params argsig2 ->
 (snd (split argsig1)) = (snd (split argsig2)).
Proof.
  intros. generalize dependent argsig2.
  induction argsig1;intros.
  - destruct argsig2. auto. 
      simpl in H. destruct p. inv H.
  - destruct argsig2.
    + simpl in H. destruct a. inv H.
    + simpl in H. destruct a, p. inv H.
      apply IHargsig1 in H2.
      rewrite !semax_call.snd_split in *.
      simpl. rewrite H2. reflexivity.
Qed.





