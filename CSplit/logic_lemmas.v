Require Import VST.veric.mpred.
Require Import VST.veric.compcert_rmaps.
Require Import Csplit.model_lemmas.
Require Import VST.veric.seplog.
Require Import VST.msl.seplog.
(* Require Import VST.floyd.proofauto. *)
Require Import VST.veric.expr.
Require Import VST.veric.lift.
Import Ctypes LiftNotation.
Require Import VST.veric.SeparationLogic.
Require Import VST.floyd.SeparationLogicFacts.

Local Open Scope logic.

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


Lemma derives_rewrite2: forall P Q,
@derives
(@predicates_hered.pred compcert_rmaps.RML.R.rmap
   compcert_rmaps.RML.R.ag_rmap) _ P Q ->
  predicates_hered.derives P Q.
Proof.
  intros.
  auto.
Qed.


Lemma andp_rewrite: (forall (T:Type) (H: ageable.ageable T) x y, 
@predicates_hered.andp T H x y = @andp (predicates_hered.pred T) 
(algNatDed T) x y).
Proof.
reflexivity.
Qed.


Lemma allp_rewrite: forall (T:Type) (H: ageable.ageable T) B x, 
@predicates_hered.allp T H B x = @allp (predicates_hered.pred T) 
(algNatDed T) B x.
Proof.
reflexivity.
Qed.


Lemma sepcon_rewrite: forall A B,
predicates_sl.sepcon A B = sepcon A B.
Proof.
intros. reflexivity.
Qed.

(* Lemma rewrite_funpost: forall gP1 ts x vl Delta ret gR1 retsig ret Q rho r,
(|> ((fun x0 : environ => gP1 ts x (vl x0)) *
oboxopt Delta ret
  (fun rho : environ =>
   maybe_retval (gR1 ts x) retsig ret rho -* Q rho))) rho r ->
(|> ((` (gP1 ts x)) (vl rho) rho *
  oboxopt Delta ret
    (fun rho0 : environ =>
    maybe_retval (gR1 ts x) retsig ret rho0 -* Q rho0) rho))%pred r. *)

Lemma func_at_unique_rewrite_logic : forall Delta argsig retsig cc A gP1
gP2 gR1 gR2 NEgP1 NEgP2 NEgR1 NEgR2 address (vl: environ -> environ) ret Q,
(`(func_at (mk_funspec (argsig, retsig) cc A gP2 gR2 NEgP2 NEgR2) address))  &&
(`(func_at (mk_funspec (argsig, retsig) cc A gP1 gR1 NEgP1 NEgR1) address)) &&
(|> (EX ts x, (((`(gP1 ts x : environ -> mpred)) vl)) * oboxopt Delta ret (fun rho => wand (maybe_retval (gR1 ts x) retsig ret rho) (Q rho))))
|-- (|> (EX ts x, ((`(gP2 ts x: environ -> mpred)) vl) * oboxopt Delta ret (fun rho => wand ((maybe_retval (gR2 ts x) retsig ret) rho) (Q rho)))).
Proof.
  intros. intro rho.
  unfold liftx. unfold_lift.
  apply derives_rewrite.
  intro r. intros E.
  destruct E. destruct H.
  pose proof func_at_unique_rewrite Delta argsig retsig cc A gP1
  gP2 gR1 gR2 NEgP1 NEgP2 NEgR1 NEgR2 address vl ret Q rho r.
  simpl. 

  unfold liftx in H2. unfold_lift in H2.
  apply H2.
  split;auto. split;auto.
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