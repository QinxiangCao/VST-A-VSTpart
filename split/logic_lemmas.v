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
Require Import VST.veric.SeparationLogic.
Require Import VST.floyd.SeparationLogicFacts.

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



Lemma derives_rewrite: forall P Q,
  predicates_hered.derives P Q ->
  @derives
  (@predicates_hered.pred compcert_rmaps.RML.R.rmap
     compcert_rmaps.RML.R.ag_rmap) Nveric P Q.
Proof.
  intros.
  auto.
Qed. *)


(* Lemma func_at_unique1_lift: forall
  fsig1 cc1 A1 P1 Q1 NEP1 NEQ1
  fsig2 cc2 A2 P2 Q2 NEP2 NEQ2 l,
  func_at (mk_funspec fsig1 cc1 A1 P1 Q1 NEP1 NEQ1) l &&
  func_at (mk_funspec fsig2 cc2 A2 P2 Q2 NEP2 NEQ2) l
  |-- !! (fsig1 = fsig2 /\ cc1 = cc2 /\ A1 = A2).
Proof.
  intros. intros. destruct H.
  eapply func_at_unique1.
  - apply H.
  - apply H0.
Qed. *)

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


Lemma derives_rewrite: forall P Q,
  predicates_hered.derives P Q ->
  @derives
  (@predicates_hered.pred compcert_rmaps.RML.R.rmap
     compcert_rmaps.RML.R.ag_rmap) _ P Q.
Proof.
  intros.
  auto.
Qed.


Lemma func_ptr_der_logic: forall  argsig1 argsig2 retsig cc A1 A2 P1 P2 R1 R2 NEP1 NER1 NEP2 NER2 v,
(` (func_ptr (mk_funspec (argsig2, retsig) cc A2 P2 R2 NEP2 NER2))) v &&
 (` (func_ptr (mk_funspec (argsig1, retsig) cc A1 P1 R1 NEP1 NER1))) v
|--
!! (argsig1 = argsig2) &&
(EX (blk_fun: block) (gA : rmaps.TypeTree)
      (gP1 gP2 gR1 gR2 : forall ts : list Type,
      functors.MixVariantFunctor._functor
        (rmaps.dependent_type_functor_rec ts (AssertTT gA)) mpred)  NEgP1 NEgP2 NEgR1 NEgR2,
      (lift1 seplog.prop (( (fun rho => (v rho = Vptr blk_fun Ptrofs.zero)) ))) &&
      (`(seplog.func_at (mk_funspec (argsig1, retsig) cc gA gP1 gR1 NEgP1 NEgR1) (blk_fun, 0)) ) &&
      (`(seplog.func_at (mk_funspec (argsig1, retsig) cc gA gP2 gR2 NEgP2 NEgR2) (blk_fun, 0)) ) &&
      (`(seplog.funspec_sub_si (mk_funspec (argsig1, retsig) cc gA gP1 gR1 NEgP1 NEgR1)
                      (mk_funspec (argsig1, retsig) cc A1 P1 R1 NEP1 NER1))) &&
      (`(seplog.funspec_sub_si (mk_funspec (argsig1, retsig) cc gA gP2 gR2 NEgP2 NEgR2)
                      (mk_funspec (argsig1, retsig) cc A2 P2 R2 NEP2 NER2)))).
Proof.
  intros. intro r.
  apply derives_rewrite. intro w.
  intros. simpl in H.
  pose proof func_ptr_der _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H.
  destruct H0. hnf in H0. subst. split;try reflexivity.
  destruct H1 as [blk_fun [gA [gP1 [gP2 [gR1 [gR2 [NEgP1 [NEgP2 [NEgR1 [NEgR2 E]]]]]]]]]].
  exists blk_fun, gA, gP2, gP1, gR2, gR1, NEgP2, NEgP1, NEgR2, NEgR1.
  destruct E. destruct H0. destruct H0. destruct H0.
  split;[split;[split|]|];auto. split;auto.
Qed.


Lemma prop_rewrite: (forall (T:Type) (H: ageable.ageable T) x,  
@predicates_hered.prop T H x = @prop (predicates_hered.pred T) 
  (algNatDed T) x).
Proof.
  reflexivity.
Qed.

Lemma funspec_rewrite_logic: forall (CS: compspecs) Delta argsig bl retsig cc gA 
  (gP gR: forall ts : list Type, functors.MixVariantFunctor._functor (rmaps.dependent_type_functor_rec ts (AssertTT gA)) mpred) 
  NEgP NEgR A 
  (P R: forall ts : list Type, functors.MixVariantFunctor._functor (rmaps.dependent_type_functor_rec ts (AssertTT A)) mpred) 
  NEP NEQ Q ret,
local (tc_environ Delta) &&
tc_exprlist Delta (snd (split argsig)) bl &&
` (funspec_sub_si
     (mk_funspec (argsig, retsig) cc gA gP gR NEgP NEgR)
     (mk_funspec (argsig, retsig) cc A P R NEP NEQ)) &&
|> (EX ts x, (` (P ts x : environ -> mpred))
          (make_args' (argsig, retsig) (@expr.eval_exprlist CS (snd (split argsig)) bl)) *
    oboxopt Delta ret (maybe_retval (R ts x) retsig ret -* Q))
|-- |> (EX ts' x',
  (` (gP ts' x': environ -> mpred))
    (make_args' (argsig, retsig) (@expr.eval_exprlist CS (snd (split argsig)) bl)) *
    oboxopt Delta ret (maybe_retval (gR ts' x') retsig ret -* (Q))).
Proof.
  intros.
  eapply derives_trans.
  { apply andp_right.
    { apply andp_left1. apply now_later. }
    { apply andp_left2. apply derives_refl. }
  }
  rewrite <- later_andp. apply later_derives.
  intros. normalize. intro r.
  apply derives_rewrite. intro w.
  intros. destruct H.
  destruct H. destruct H.
  unfold local in H. unfold lift1 in H.
  pose proof funspec_rewrite CS gA gP gR NEgP NEgR argsig retsig cc A P R NEP NEQ r bl ret ts x  Q Delta H.
  specialize (H3 w). apply H3.
  split;auto. split;auto.
Qed.

Lemma func_ptr_self_logic: forall gs fs v blk,
  local (fun rho => v rho = Vptr blk Ptrofs.zero) &&
  ` (funspec_sub_si gs fs) &&
  ` (func_at gs (blk, 0)) |--
  ` (func_ptr gs) v.
Proof.
  intros.
  unfold local. unfold lift1.
  unfold liftx. simpl. unfold lift.
  intros r.
  apply derives_rewrite. intro w.
  intros. destruct H. destruct H.
  pose proof func_ptr_self gs fs _ _ H w.
  apply H2. split;auto.
Qed.