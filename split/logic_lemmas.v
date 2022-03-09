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



Lemma allp_rewrite: forall (T:Type) (H: ageable.ageable T) B x, 
@predicates_hered.allp T H B x = @allp (predicates_hered.pred T) 
(algNatDed T) B x.
Proof.
reflexivity.
Qed.



Lemma func_at_unique2_logic: forall
fsig cc A P1 Q1 NEP1 NEQ1
P2 Q2 NEP2 NEQ2 (l: address),
`(func_at (mk_funspec fsig cc A P1 Q1 NEP1 NEQ1) l) &&
`(func_at (mk_funspec fsig cc A P2 Q2 NEP2 NEQ2) l)
|--  (( (|> (ALL ts x (vl: environ -> environ),  `(P2 ts x : environ -> mpred) vl <--> `(P1 ts x: environ -> mpred) vl)))) &&
      (( (|> (ALL ts x (vl: environ -> environ),  `(Q2 ts x : environ -> mpred) vl <--> `(Q1 ts x: environ -> mpred) vl)))).
Proof.
  intros.
  eapply derives_trans with (Q:=
    ((ALL ts x vl,   (|> (`(P2 ts x : environ -> mpred) vl <--> `(P1 ts x: environ -> mpred) vl)))) &&
        ((ALL ts x vl,  (|> ( `(Q2 ts x : environ -> mpred) vl <--> `(Q1 ts x: environ -> mpred) vl))))
  ).
  2:{ apply andp_derives.
  + rewrite later_allp. apply allp_derives.
    intros ts. rewrite later_allp. apply allp_derives.
    intros x. rewrite later_allp. apply allp_derives.
    intros vl. apply derives_refl.
  + rewrite later_allp. apply allp_derives.
    intros ts. rewrite later_allp. apply allp_derives.
    intros x. rewrite later_allp. apply allp_derives.
    intros vl. apply derives_refl.
  }
  apply andp_right.
  { apply allp_right. intros ts.
    apply allp_right. intros x.
    apply allp_right. intros vl.
    intro r.
    apply derives_rewrite.
    intros rho. intros [E1 E2].
    pose proof func_at_unique2 _ _ _ _ _ _ NEP1 NEQ1 _ _  NEP2 NEQ2 _ E1 E2.
    destruct H.
    specialize (H ts x (vl r)). auto.
  }
  { apply allp_right. intros ts.
    apply allp_right. intros x.
    apply allp_right. intros vl.
    intro r.
    apply derives_rewrite.
    intros rho. intros [E1 E2].
    pose proof func_at_unique2 _ _ _ _ _ _ NEP1 NEQ1 _ _  NEP2 NEQ2 _ E1 E2.
    destruct H.
    specialize (H0 ts x (vl r)). auto.
  }
Qed.

Lemma func_ptr_der_logic: forall Delta argsig1 argsig2 retsig cc A1 A2 P1 P2 R1 R2 NEP1 NER1 NEP2 NER2 v,
(` (func_ptr (mk_funspec (argsig2, retsig) cc A2 P2 R2 NEP2 NER2))) v &&
 (` (func_ptr (mk_funspec (argsig1, retsig) cc A1 P1 R1 NEP1 NER1))) v &&
 `(precise_fun_at_ptr Delta) v
|--
!! (argsig1 = argsig2) &&
(EX (blk_fun: block) (gA : rmaps.TypeTree)
      (gP1 gP2 gR1 gR2 : forall ts : list Type,
      functors.MixVariantFunctor._functor
        (rmaps.dependent_type_functor_rec ts (AssertTT gA)) mpred)  NEgP1 NEgP2 NEgR1 NEgR2,
      seplog.prop (precise_funspec Delta (mk_funspec (argsig1, retsig) cc gA gP2 gR2 NEgP2 NEgR2)) &&
      (lift1 seplog.prop (( (fun rho => (v rho = Vptr blk_fun Ptrofs.zero))))) &&
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
  pose proof func_ptr_der _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H.
  destruct H0. hnf in H0. subst. split;try reflexivity.
  destruct H1 as [blk_fun [gA [gP1 [gP2 [gR1 [gR2 [NEgP1 [NEgP2 [NEgR1 [NEgR2 E]]]]]]]]]].
  exists blk_fun, gA, gP2, gP1, gR2, gR1, NEgP2, NEgP1, NEgR2, NEgR1.
  destruct E. destruct H0. destruct H0. destruct H0.
  split;[split;[split|]|];auto. split;auto.
  destruct H0.
  split;auto.
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