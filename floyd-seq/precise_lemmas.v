Require Import VST.msl.seplog.
Require Import VST.veric.mpred.
Require Import VST.veric.seplog.
Require Import VST.veric.lift.
Require Import VST.veric.semax_call.
Require Import VST.floyd.SeparationLogicFacts.
Require Import Csplit.model_lemmas.
Require Import Csplit.strong.
Require Import Csplit.precise_model_lemmas.
Require Import FloydSeq.proofauto.

Local Open Scope logic.

(* Lemmas in [precise_rel1] will be tried first when constructing relations *)
Create HintDb precise_rel discriminated.
Create HintDb precise_rel1 discriminated.
Create HintDb precise_pred discriminated.

Create HintDb precise_spec discriminated.

Lemma distrib_wand_andp {A} {ND: NatDed A} {SL: SepLog A}:
  forall (P Q1 Q2: A),
    P -* (Q1 && Q2) = (P -* Q1) && (P -* Q2).
Proof.
  intros. apply pred_ext.
  - apply andp_right; apply wand_derives; solve_andp.
  - rewrite <- wand_sepcon_adjoint.
    rewrite sepcon_comm.
    eapply derives_trans;
      [apply distrib_sepcon_andp |].
    apply andp_derives; apply wand_frame_elim.
Qed.

Definition precise_pred {A} {ND: NatDed A} {SL: SepLog A} (P: A) :=
  forall Q R, (P * Q) && (P * R) |-- P * (Q && R).

Lemma precise_emp {A} {ND: NatDed A} {SL: SepLog A} {CA: ClassicalSep A}:
  precise_pred emp.
Proof.
  unfold precise_pred. intros.
  normalize.
Qed.

Lemma andp_prop_precise {A} {ND: NatDed A} {SL: SepLog A}:
  forall (P: Prop) (Q: A),
    precise_pred Q ->
    precise_pred (!! P && Q).
Proof.
  unfold precise_pred. intros.
  normalize.
Qed.

Lemma precise_extract_prop {A} {ND: NatDed A} {SL: SepLog A}:
  forall (P: Prop) (Q: A),
    (P -> precise_pred Q) ->
    precise_pred (!! P && Q).
Proof.
  unfold precise_pred. intros.
  normalize.
Qed.

Lemma precise_extract_prop' {A} {ND: NatDed A} {SL: SepLog A}:
  forall (P: Prop) (Q: A),
    (P -> precise_pred (!! P && Q)) ->
    precise_pred (!! P && Q).
Proof.
  unfold precise_pred. intros.
  assert_PROP P. normalize.
  auto.
Qed.

Lemma sepcon_precise {A} {ND: NatDed A} {SL: SepLog A}:
  forall (P Q: A),
    precise_pred P ->
    precise_pred Q ->
    precise_pred (P * Q).
Proof.
  unfold precise_pred. intros.
  eapply derives_trans.
  rewrite sepcon_assoc. rewrite sepcon_assoc.
  apply H. rewrite sepcon_assoc.
  apply sepcon_derives; auto.
Qed.

Lemma exp_precise_rel {A} {ND: NatDed A} {SL: SepLog A}:
  forall {T} (f: T -> A) (R: T -> T -> Prop),
    ( forall x1 x2,
        (f x1 * TT) && (f x2 * TT)
        |-- !! R x1 x2 ) ->
    ( forall x1 x2,
        R x1 x2 -> f x1 = f x2 ) ->
    ( forall x, precise_pred (f x) ) ->
    precise_pred (exp f).
Proof.
  intros.
  unfold precise_pred. intros.
  normalize.
  assert_PROP (f x0 = f x).
  { apply derives_trans with (!! R x0 x).
    - eapply derives_trans; [| apply H].
      apply andp_derives; apply sepcon_derives; auto.
    - apply prop_derives; auto. }
  rewrite H2. Exists x.
  apply H1.
Qed.

Lemma exp_precise {A} {ND: NatDed A} {SL: SepLog A}:
  forall {T} (f: T -> A),
    ( forall x1 x2,
        (f x1 * TT) && (f x2 * TT)
        |-- !! (x1 = x2) ) ->
    ( forall x, precise_pred (f x) ) ->
    precise_pred (exp f).
Proof.
  intros.
  eapply exp_precise_rel with eq; auto.
  intros. congruence.
Qed.

Lemma environ_precise {A} {ND: NatDed A} {SL: SepLog A}:
  forall (P: environ -> A) (r: environ),
    precise_pred P ->
    precise_pred (P r).
Proof.
  unfold precise_pred. intros.
  apply (H (fun _ => Q) (fun _ => R) r).
Qed.

Lemma liftx_precise {A} {ND: NatDed A} {SL: SepLog A}:
  forall (P: environ -> A) (env: environ -> environ),
    precise_pred P ->
    precise_pred (liftx P env).
Proof.
  intros. unfold_lift.
  unfold precise_pred.
  simpl. intros.
  apply environ_precise. assumption.
Qed.

Lemma precise_mapsto_logic {CS: compspecs}:
  forall t p v,
    precise_pred (mapsto Tsh t p v).
Proof.
  unfold precise_pred. intros.
  apply precise_mapsto.
Qed.

Lemma precise_data_at_value_nonvolatile {CS: compspecs}:
  forall t p v,
    type_is_by_value t = true ->
    type_is_volatile t = false ->
    precise_pred (data_at Tsh t v p).
Proof.
  unfold precise_pred. intros.
  assert_PROP (field_compatible t [] p).
  { unfold data_at, field_at. entailer!. }
  destruct t; try inv H;
  match goal with
  | |- context [data_at Tsh ?t ?v ?p] =>
      rewrite <- (mapsto_data_at' Tsh t v v p ltac:(auto) H0 H1);
      auto; apply precise_mapsto
  end.
Qed.

Lemma data_at_same_value {CS: compspecs}:
  forall t p v1 v2,
    repinject t v1 <> Vundef ->
    repinject t v2 <> Vundef ->
    type_is_volatile t = false ->
    (data_at Tsh t v1 p * TT) &&
    (data_at Tsh t v2 p * TT)
    |-- !! (v1 = v2).
Proof.
  intros.
  assert_PROP (field_compatible t [] p).
  { unfold data_at, field_at. entailer!. }
  destruct t; try (exfalso; apply H; reflexivity);
  match goal with
  | |- context [(data_at Tsh ?t ?v1 ?p * TT) && (data_at Tsh ?t ?v2 ?p * TT)] =>
      rewrite <- (mapsto_data_at' Tsh t v1 v1 p ltac:(auto) H1 H2); auto;
      rewrite <- (mapsto_data_at' Tsh t v2 v2 p ltac:(auto) H1 H2); auto;
      apply mapsto_same_value; auto
  end.
Qed.

Lemma precise_funspec_equiv:
  forall (Delta : tycontext) (f : funspec),
    precise_funspec Delta f <->
    precise_funspec_logic Delta f.
Proof.
  split; intros.
  - apply precise_funspec_is_precise_logic.
    assumption.
  - unfold precise_funspec.
    unfold precise_funspec_logic in H.
    destruct f. intros.
    specialize (H bl Q1 Q2 ret H0 H1 r).
    eapply predicates_hered.derives_trans.
    { eapply predicates_hered.derives_trans.
      2:{ apply H. }
      apply predicates_hered.derives_refl. }
    { apply predicates_hered.derives_refl. }
Qed.

(* Lemma precise_funspec_same_logic: forall Delta ret P R Q1 Q2,
  precise_pred P ->
  (P * oboxopt Delta ret (fun rho => R rho -* Q1 rho)) &&
  (P * oboxopt Delta ret (fun rho => R rho -* Q2 rho))
  |-- P * oboxopt Delta ret (fun rho => R rho -* Q1 rho && Q2 rho).
Proof.
  intros. eapply derives_trans.
  apply H. apply sepcon_derives. apply derives_refl.
  destruct ret; simpl oboxopt.
  - eapply derives_trans. apply obox_andp.
    unfold obox. apply allp_right. intro v.
    apply allp_left with v.
    destruct (temp_types Delta) ! i; auto.
    apply imp_derives; auto.
    apply subst_derives. simpl. intro r.
    rewrite distrib_wand_andp. auto.
  - simpl. intro r.
    rewrite distrib_wand_andp. auto.
Qed.

Lemma precise_funspec_same_logic': forall Delta ret P R Q1 Q2 r,
  precise_pred P ->
  (P r * oboxopt Delta ret (fun rho => R rho -* Q1 rho) r) &&
  (P r * oboxopt Delta ret (fun rho => R rho -* Q2 rho) r)
  |-- P r * oboxopt Delta ret (fun rho => R rho -* Q1 rho && Q2 rho) r.
Proof.
  intros.
  apply (precise_funspec_same_logic Delta ret P R Q1 Q2 H r).
Qed. *)

Lemma distrib_wand_andp_postcond: forall (A: Type) (x: A)
    (Delta: tycontext) (ret: option ident)
    (fsig: funsig)
    (Q: A -> environ -> mpred)
    (Q1 Q2: environ -> mpred), 
  oboxopt Delta ret
    (fun rho =>
      maybe_retval (Q x) (snd fsig) ret rho -* Q1 rho) &&
  oboxopt Delta ret
    (fun rho =>
      maybe_retval (Q x) (snd fsig) ret rho -* Q2 rho)
  |--
  oboxopt Delta ret
    (fun rho =>
      maybe_retval (Q x) (snd fsig) ret rho -* Q1 rho && Q2 rho).
Proof.
  intros. destruct ret; unfold oboxopt.
  - eapply derives_trans; [apply obox_andp |].
    unfold obox. apply allp_derives. intro v.
    destruct (temp_types Delta) ! i.
    + apply imp_derives; [apply derives_refl |].
      apply subst_derives.
      simpl. intro.
      rewrite distrib_wand_andp. apply derives_refl.
    + apply derives_refl.
  - intro r. rewrite distrib_wand_andp.
    apply derives_refl.
Qed.

Lemma globals_only_env_set:
  forall rho i v,
    globals_only (env_set rho i v) = globals_only rho.
Proof.
  intros. destruct rho.
  unfold env_set, globals_only.
  reflexivity.
Qed.

Definition precise_spec1a (A: Type) (R: A -> A -> Prop)
    (P: A -> environ -> mpred): Prop :=
  forall (x1 x2: A), (P x1 * TT) && (P x2 * TT) |-- !! (R x1 x2).

Definition precise_spec1b (A: Type) (R: A -> A -> Prop)
    (P: A -> environ -> mpred): Prop :=
  forall (x1 x2: A), R x1 x2 -> P x1 = P x2.

Definition precise_spec2 (A: Type)
    (P: A -> environ -> mpred): Prop :=
  forall (x: A) (r: environ), precise_pred (P x r).

Lemma precise_funspec_intro:
  forall (A: Type) (R: A -> A -> Prop)
      (P Q: A -> environ -> mpred)
      (fsig: funsig) (cc: calling_convention)
      (Delta: tycontext),
    precise_spec1a A R P ->
    precise_spec1b A R P ->
    precise_spec1b A R Q ->
    precise_spec2 A P ->
    precise_funspec_logic Delta
      (NDmk_funspec fsig cc A P Q).
Proof.
  unfold NDmk_funspec,
    precise_spec1a, precise_spec1b, precise_spec2.
  simpl. intros.
  Intros ts1 x1 ts2 x2.
  Exists ts1 x1.
  unfold_lift.
  assert_PROP (R x1 x2).
  { apply derives_trans with (
      (P x1 (make_args' fsig bl x) * TT) &&
      (P x2 (make_args' fsig bl x) * TT)
    ).
    - apply andp_derives.
      apply sepcon_derives; auto.
      apply sepcon_derives; auto.
    - apply H.
  }
  pose proof H0 x1 x2 H5.
  pose proof H1 x1 x2 H5.
  rewrite H6. rewrite H7.

  pose proof H2 x2 (make_args' fsig bl x)
    (oboxopt Delta ret
      (fun rho =>
        maybe_retval (Q x2) (snd fsig) ret rho -* Q1 rho) x)
    (oboxopt Delta ret
      (fun rho =>
        maybe_retval (Q x2) (snd fsig) ret rho -* Q2 rho) x).
  eapply derives_trans; [apply H8 |].

  apply sepcon_derives. apply derives_refl.
  apply (distrib_wand_andp_postcond
    A x2 Delta ret fsig Q Q1 Q2 x).
Qed.

Lemma canon_extract_prop:
  forall (p: Prop) P L S Q,
    (p -> PROPx P (LOCALx L (SEPx S)) |-- Q) ->
    PROPx (p :: P) (LOCALx L (SEPx S)) |-- Q.
Proof.
  unfold PROPx. intros.
  simpl fold_right. normalize.
  eapply derives_trans; [| apply (H H0)].
  normalize.
Qed.

Lemma local_sametemp_eq:
  forall P1 L1 S1 P2 L2 S2 x v1 v2 Q,
    ( v1 = v2 ->
      (PROPx P1 (LOCALx L1 (SEPx S1)) * TT) &&
      (PROPx P2 (LOCALx L2 (SEPx S2)) * TT)
      |-- Q ) ->
    (PROPx P1 (LOCALx (temp x v1 :: L1) (SEPx S1)) * TT) &&
    (PROPx P2 (LOCALx (temp x v2 :: L2) (SEPx S2)) * TT)
    |-- Q.
Proof.
  intros.
  apply derives_trans with (
    !! (v1 = v2) &&
    ((PROPx P1 (LOCALx L1 (SEPx S1)) * TT) &&
    (PROPx P2 (LOCALx L2 (SEPx S2)) * TT))
  ).
  2: { apply derives_extract_prop. apply H. }
  clear H.
  apply andp_right.
  - unfold PROPx, LOCALx.
    unfold local, lift1.
    simpl. intro r. unfold_lift.
    normalize.
  - apply andp_derives.
    + apply sepcon_derives; auto.
      unfold PROPx, LOCALx.
      apply andp_derives; auto.
      apply andp_derives; auto.
      unfold local, lift1.
      simpl. intro r. unfold_lift.
      normalize.
    + apply sepcon_derives; auto.
      unfold PROPx, LOCALx.
      apply andp_derives; auto.
      apply andp_derives; auto.
      unfold local, lift1.
      simpl. intro r. unfold_lift.
      normalize.
Qed.

Lemma fold_right_sepcon_TT pl:
  fold_right sepcon TT pl = fold_right_sepcon pl * TT.
Proof.
  induction pl; simpl.
  - normalize.
  - rewrite IHpl. rewrite sepcon_assoc.
    reflexivity.
Qed.

Lemma precise_rel_only_sep:
  forall S1 S2 Q,
    ( fold_right sepcon TT S1 &&
      fold_right sepcon TT S2
      |-- !! Q ) ->
    (PROPx nil (LOCALx nil (SEPx S1)) * TT) &&
    (PROPx nil (LOCALx nil (SEPx S2)) * TT)
    |-- !! Q.
Proof.
  intros.
  unfold PROPx, LOCALx, SEPx. normalize.
  intro r. simpl. do 2 rewrite <- fold_right_sepcon_TT.
  apply H.
Qed.

Lemma precise_ignore_same_sep:
  forall s S1 S2 Q,
    ( fold_right sepcon TT S1 &&
      fold_right sepcon TT S2
      |-- Q ) ->
    fold_right sepcon TT (s :: S1) &&
    fold_right sepcon TT (s :: S2)
    |-- Q.
Proof.
  intros.
  eapply derives_trans; [| apply H].
  apply andp_derives; simpl.
  - rewrite fold_right_sepcon_TT.
    pull_left TT. rewrite <- sepcon_assoc.
    apply sepcon_derives; auto.
  - rewrite fold_right_sepcon_TT.
    pull_left TT. rewrite <- sepcon_assoc.
    apply sepcon_derives; auto.
Qed.

Lemma precise_extract_prop_from_sep {CS: compspecs}:
  forall s1 s2 p S1 S2 Q,
    ( (s1 * TT) && (s2 * TT) |-- !! p ) ->
    ( p ->
      fold_right sepcon TT S1 &&
      fold_right sepcon TT S2
      |-- Q ) ->
    fold_right sepcon TT (s1 :: S1) &&
    fold_right sepcon TT (s2 :: S2)
    |-- Q.
Proof.
  intros.
  assert_PROP p.
  { simpl fold_right.
    eapply derives_trans; [| apply H; auto].
    apply andp_derives.
    - apply sepcon_derives; auto.
    - apply sepcon_derives; auto. }
  pose proof H0 H1.
  eapply derives_trans; [| apply H2].
  apply andp_derives; simpl.
  - rewrite fold_right_sepcon_TT.
    pull_left TT. rewrite <- sepcon_assoc.
    apply sepcon_derives; auto.
  - rewrite fold_right_sepcon_TT.
    pull_left TT. rewrite <- sepcon_assoc.
    apply sepcon_derives; auto.
Qed.

Lemma data_at_tint_samevalue {CS: compspecs}:
  forall i s p n1 n2,
    (data_at Tsh (Tint i s noattr) (Vint n1) p * TT) &&
    (data_at Tsh (Tint i s noattr) (Vint n2) p * TT)
    |-- !! (Vint n1 = Vint n2).
Proof.
  intros.
  apply data_at_same_value; simpl.
  intro. discriminate H.
  intro. discriminate H.
  destruct i, s; reflexivity.
Qed.

Lemma data_at_tptr_samevalue {CS: compspecs}:
  forall t p v1 v2,
    is_pointer_or_null v1 ->
    is_pointer_or_null v2 ->
    (data_at Tsh (tptr t) v1 p * TT) &&
    (data_at Tsh (tptr t) v2 p * TT)
    |-- !! (v1 = v2).
Proof.
  intros.
  apply data_at_same_value; simpl.
  intro; subst; inv H.
  intro; subst; inv H0.
  reflexivity.
Qed.

Definition z_equiv (n1 n2: Z): Prop :=
  Int.repr n1 = Int.repr n2.

Arguments z_equiv n1 n2: simpl never.

Lemma z_equiv_refl: forall n, z_equiv n n.
Proof.
  intros. reflexivity.
Qed.

Lemma z_equiv_symm:
  forall n1 n2,
    z_equiv n1 n2 -> z_equiv n2 n1.
Proof.
  intros. unfold z_equiv in *.
  congruence.
Qed.

Lemma z_equiv_trans:
  forall n1 n2 n3,
    z_equiv n1 n2 ->
    z_equiv n2 n3 ->
    z_equiv n1 n3.
Proof.
  intros. unfold z_equiv in *.
  congruence.
Qed.

Hint Resolve z_equiv_refl z_equiv_symm z_equiv_trans: core.

Lemma z_equiv_Vint_eq:
  forall n1 n2,
    z_equiv n1 n2 ->
    Vint (Int.repr n1) = Vint (Int.repr n2).
Proof.
  intros.
  unfold z_equiv in H. rewrite H.
  reflexivity.
Qed.

Lemma Vint_eq_z_equiv:
  forall n1 n2,
    Vint (Int.repr n1) = Vint (Int.repr n2) ->
    z_equiv n1 n2.
Proof.
  intros.
  unfold z_equiv. apply Vint_injective.
  assumption.
Qed.

Hint Resolve Vint_eq_z_equiv: core.

Lemma data_at_tint_sameloc_eq {CS: compspecs}:
  forall P1 P2 Q i s p n1 n2,
    ( z_equiv n1 n2 ->
      fold_right sepcon TT P1 &&
      fold_right sepcon TT P2
      |-- Q ) ->
    fold_right sepcon TT (data_at Tsh (Tint i s noattr) (Vint (Int.repr n1)) p :: P1) &&
    fold_right sepcon TT (data_at Tsh (Tint i s noattr) (Vint (Int.repr n2)) p :: P2)
    |-- Q.
Proof.
  intros.
  eapply precise_extract_prop_from_sep.
  - apply data_at_tint_samevalue.
  - intros. apply H. unfold z_equiv.
    apply Vint_injective. assumption.
Qed.

Lemma data_at_tptr_sameloc_eq {CS: compspecs}:
  forall P1 P2 Q t p v1 v2,
    ( is_pointer_or_null v1 /\ is_pointer_or_null v2 ) ->
    ( v1 = v2 ->
      fold_right sepcon TT P1 &&
      fold_right sepcon TT P2
      |-- Q ) ->
    fold_right sepcon TT (data_at Tsh (tptr t) v1 p :: P1) &&
    fold_right sepcon TT (data_at Tsh (tptr t) v2 p :: P2)
    |-- Q.
Proof.
  intros.
  eapply precise_extract_prop_from_sep.
  - intros.
    apply data_at_tptr_samevalue; intuition.
  - auto.
Qed.

Lemma precise_sep_precise:
  forall P L S,
    precise_pred (fold_right_sepcon S) ->
    precise_pred (PROPx P (LOCALx L (SEPx S))).
Proof.
  intros.
  unfold PROPx, LOCALx, SEPx.
  apply andp_prop_precise.
  unfold local, lift1.
  unfold precise_pred.
  intros Q R r. simpl.
  apply andp_prop_precise; auto.
Qed.

