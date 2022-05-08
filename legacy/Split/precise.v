Require Import AClight.AClight.
Require Export VST.veric.base.
Require Export VST.veric.SeparationLogic.
Require Export VST.msl.Extensionality.
Require Export compcert.lib.Coqlib.
Require Export VST.msl.Coqlib2 VST.veric.coqlib4 VST.floyd.coqlib3.
Require Export VST.veric.juicy_extspec.
Require Import VST.veric.NullExtension.
Require Export VST.floyd.jmeq_lemmas.
Require Export VST.floyd.find_nth_tactic.
Require Export VST.floyd.val_lemmas.
Require Export VST.floyd.assert_lemmas.
Require Import VST.veric.semax_lemmas.
Require VST.floyd.SeparationLogicAsLogicSoundness.
Require Import VST.floyd.SeparationLogicFacts.
Require Import VST.floyd.SeparationLogicAsLogic.
Export SeparationLogicAsLogicSoundness.MainTheorem.CSHL_Sound.DeepEmbedded.
Require Import VST.floyd.proofauto.
Import Ctypes LiftNotation.
Local Open Scope logic.
Require Import Split.vst_ext.
Require Import Split.model_lemmas.
Require Import Split.logic_lemmas.


Definition precise_pre_post A P Q : Prop :=
    forall (R1 R2:
     forall ts : list Type,
     functors.MixVariantFunctor._functor
       (rmaps.dependent_type_functor_rec ts (AssertTT A)) mpred),
     (EX ts1 a1, ((P ts1 a1) * ((Q ts1 a1) -* R1 ts1 a1) :functors.MixVariantFunctor._functor
     (functors.MixVariantFunctorGenerator.ffunc
        (functors.MixVariantFunctorGenerator.fconst environ)
        functors.MixVariantFunctorGenerator.fidentity) mpred )) &&
     (EX ts2 a2, ((P ts2 a2) * ((Q ts2 a2) -* R2 ts2 a2) :functors.MixVariantFunctor._functor
     (functors.MixVariantFunctorGenerator.ffunc
        (functors.MixVariantFunctorGenerator.fconst environ)
        functors.MixVariantFunctorGenerator.fidentity) mpred )) |--
     (EX ts a, ((P ts a) * ((Q ts a) -* (R1 ts a && R2 ts a)) : functors.MixVariantFunctor._functor
     (functors.MixVariantFunctorGenerator.ffunc
        (functors.MixVariantFunctorGenerator.fconst environ)
        functors.MixVariantFunctorGenerator.fidentity) mpred)).
    
Definition precise_pre_post' A P Q : Prop :=
    forall (R1 R2:
    forall ts : list Type,
    functors.MixVariantFunctor._functor
        (rmaps.dependent_type_functor_rec ts (AssertTT A)) mpred) ts1 a1 ts2 a2,
    ( ((P ts1 a1) * ((Q ts1 a1) -* R1 ts1 a1) :functors.MixVariantFunctor._functor
    (functors.MixVariantFunctorGenerator.ffunc
        (functors.MixVariantFunctorGenerator.fconst environ)
        functors.MixVariantFunctorGenerator.fidentity) mpred )) &&
    (((P ts2 a2) * ((Q ts2 a2) -* R2 ts2 a2) :functors.MixVariantFunctor._functor
    (functors.MixVariantFunctorGenerator.ffunc
        (functors.MixVariantFunctorGenerator.fconst environ)
        functors.MixVariantFunctorGenerator.fidentity) mpred )) |--
    (EX ts a, ((P ts a) * ((Q ts a) -* (R1 ts a && R2 ts a)) : functors.MixVariantFunctor._functor
    (functors.MixVariantFunctorGenerator.ffunc
        (functors.MixVariantFunctorGenerator.fconst environ)
        functors.MixVariantFunctorGenerator.fidentity) mpred)).

Lemma precise_pp_to_pp' : forall A P Q,
precise_pre_post A P Q -> precise_pre_post' A P Q.
Proof.
    intros.
    hnf. intros. eapply derives_trans.
    2:{ apply H. }
    Exists ts1 a1. Exists ts2 a2. solve_andp.
Qed.

    (* If traditional precise for P then always hold for Q R
        If with permission:
            graph ~ P && graph ~ Q && graph ~ R

            find examples in permission, and prove that they are precise.

            readony permission & partial permission
            SPLAY tree
            
    *)

Definition precise_funspec (f:funspec) : Prop :=
match f with
| mk_funspec fsig cc A P Q _ _ =>
forall (R1 R2:
    forall ts : list Type,
    functors.MixVariantFunctor._functor
    (rmaps.dependent_type_functor_rec ts (AssertTT A)) mpred),
    (EX ts1 a1, ((P ts1 a1) * ((Q ts1 a1) -* R1 ts1 a1) :functors.MixVariantFunctor._functor
    (functors.MixVariantFunctorGenerator.ffunc
    (functors.MixVariantFunctorGenerator.fconst environ)
    functors.MixVariantFunctorGenerator.fidentity) mpred )) &&
    (EX ts2 a2, ((P ts2 a2) * ((Q ts2 a2) -* R2 ts2 a2) :functors.MixVariantFunctor._functor
    (functors.MixVariantFunctorGenerator.ffunc
    (functors.MixVariantFunctorGenerator.fconst environ)
    functors.MixVariantFunctorGenerator.fidentity) mpred )) |--
    (EX ts a, ((P ts a) * ((Q ts a) -* (R1 ts a && R2 ts a)) : functors.MixVariantFunctor._functor
    (functors.MixVariantFunctorGenerator.ffunc
    (functors.MixVariantFunctorGenerator.fconst environ)
    functors.MixVariantFunctorGenerator.fidentity) mpred))
end.

Definition all_precise_fun (Delta:tycontext) : Prop := 
forall x phi, 
(glob_specs Delta) ! x =  Some phi ->
precise_funspec phi.



Lemma obox_sepcon2: forall Delta i P Q,
closed_wrt_vars (eq i) P -> 
obox Delta i (P * Q) |-- P * obox Delta i Q.
Proof.
intros.
unfold obox.

Locate closed_wrt_vars.

Search closed_wrt_vars obox.

Locate obox_closed.

Check closed_wrt_subst.


Search wand sepcon.

Search sepcon allp.
Locate allp_sepcon2.

  
Search obox.


Abort.


Lemma obox_andp: forall Delta i P Q,
  obox Delta i P && obox Delta i Q |-- obox Delta i (P && Q).
Proof.
  intros.
  unfold obox.
  apply allp_right.
  intros v.
  eapply derives_trans.
  { apply andp_derives.
    - apply (allp_left _ v). apply derives_refl.
    - apply (allp_left _ v). apply derives_refl.
  }
  destruct ((temp_types Delta) ! i); [| apply TT_right].
  apply (proj1 (imp_andp_adjoint _ _ _)).
  normalize.
  unfold TT.
  rewrite !log_normalize.prop_imp by auto.
  rewrite subst_andp.
  auto.
Qed.

Lemma obox_andp2: forall Delta i P Q,
   obox Delta i (P && Q) |-- obox Delta i P && obox Delta i Q.
Proof.
  intros.
  unfold obox. apply andp_right.
  - apply allp_derives. intros.
    destruct ((temp_types Delta) ! i); [| apply TT_right].
    apply (proj1 (imp_andp_adjoint _ _ _)).
    normalize. unfold TT.
    rewrite !log_normalize.prop_imp by auto.
    rewrite subst_andp. solve_andp.
  - apply allp_derives. intros.
    destruct ((temp_types Delta) ! i); [| apply TT_right].
    apply (proj1 (imp_andp_adjoint _ _ _)).
    normalize. unfold TT.
    rewrite !log_normalize.prop_imp by auto.
    rewrite subst_andp. solve_andp.
Qed.

Lemma precise_funspec_ret: forall Delta A P R arglist retsig ret Q1 Q2 ts1 x1 ts2 x2,
precise_pre_post A P R ->
(retsig = Tvoid <-> ret = None) ->
( (` (P ts1 x1)) arglist * oboxopt Delta ret (maybe_retval (R ts1 x1) retsig ret -* Q1)) &&
((` (P ts2 x2)) arglist * oboxopt Delta ret (maybe_retval (R ts2 x2) retsig ret -* Q2))
|-- EX ts x,
((` (P ts x)) arglist * oboxopt Delta ret (maybe_retval (R ts x) retsig ret -* Q1 && Q2 ):functors.MixVariantFunctor._functor
(functors.MixVariantFunctorGenerator.ffunc
 (functors.MixVariantFunctorGenerator.fconst environ)
 functors.MixVariantFunctorGenerator.fidentity) mpred).
Proof.
intros.
pose proof precise_pp_to_pp' _ _ _ H as H'.
specialize (H' (fun _ _ => Q1) (fun _ _ => Q2) ts1 x1 ts2 x2). simpl in H'.


destruct ret eqn:Eret.
- (* ret = Some i *)
  destruct ((temp_types Delta) ! i) eqn:Eguard.
  { (* temp_types Delta ! i = Some t *)
    assert (temp_guard Delta i). { hnf. rewrite Eguard. intros C. inv C. }
    assert ((` (P ts1 x1)) arglist = obox Delta i (fun rho => (` (P ts1 x1)) arglist rho)).
    { pose proof obox_closed Delta i (fun rho : environ => (` (P ts1 x1)) arglist rho) H1.
      rewrite H2;auto. admit. }
    assert ((` (P ts2 x2)) arglist = obox Delta i (fun rho => (` (P ts2 x2)) arglist rho)).
    { pose proof obox_closed Delta i (fun rho : environ => (` (P ts2 x2)) arglist rho) H1.
      rewrite H3;auto. admit. }
    unfold oboxopt.
    rewrite H2. rewrite H3.
    eapply derives_trans.
    { apply andp_derives;apply obox_sepcon. }
    eapply derives_trans.
    { apply obox_andp. }
    admit.
  }
  { (* temp_types Delta ! i = None *)
    unfold oboxopt. unfold obox. rewrite Eguard.
    unfold temp_types in Eguard.
    Exists ts1 x1. solve_andp.
  }
- (* ret = None *)
  unfold oboxopt. unfold maybe_retval.
  replace (retsig) with (Tvoid). 2:{ symmetry. apply H0. auto. }

Admitted.