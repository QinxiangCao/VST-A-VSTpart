Require Import Coq.Classes.Equivalence.
Require Import VST.msl.base.
Require Import VST.msl.simple_CCC.
Require Import VST.msl.seplog.
Require Import VST.msl.log_normalize.
Require Import VST.msl.Coqlib2.
Require Import VST.msl.ramification_lemmas.
Require Import RamifyCoq.msl_ext.log_normalize.

Local Open Scope logic.

Section EnvironBox_EnvironStable.

Context {A Env : Type}.
Context {ND : NatDed A}.
Context {SL : SepLog A}.
Context {CoSL: CorableSepLog A}.

Variable M: Env -> Env -> Prop.
Context {EqM: Equivalence M}.

Definition EnvironBox (P: Env -> A) : Env -> A :=
  fun rho: Env => (ALL rho': Env, !! M rho rho' --> P rho').

Definition EnvironStable (P: Env -> A) : Prop :=
  forall rho rho', M rho rho' -> P rho = P rho'.

Lemma EnvironStable_sepcon: forall P Q,
  EnvironStable P ->
  EnvironStable Q ->
  EnvironStable (P * Q).
Proof.
  unfold EnvironStable.
  intros.
  specialize (H _ _ H1).
  specialize (H0 _ _ H1).
  simpl.
  f_equal; auto.
Qed.

Lemma EnvironBox_EnvironStable: forall P, EnvironStable (EnvironBox P).
(* This lemma is the reason why EqM is required. *)
Proof.
  intros.
  unfold EnvironBox, EnvironStable; intros.
  apply pred_ext; apply allp_right; intro rho''; apply (allp_left _ rho'');
  apply imp_andp_adjoint; normalize; rewrite prop_imp; auto.
  + rewrite H; auto.
  + rewrite <- H; auto.
Qed.

Lemma EnvironBox_T: forall P, EnvironBox P |-- P.
Proof.
  intros P rho.
  apply (allp_left _ rho).
  rewrite prop_imp by reflexivity.
  auto.
Qed.

Lemma EnvironBox_derives: forall P Q, P |-- Q -> EnvironBox P |-- EnvironBox Q.
Proof.
  intros P Q ? rho.
  apply allp_right; intro rho'.
  apply (allp_left _ rho').
  apply imp_andp_adjoint.
  apply derives_extract_prop'; intro.
  rewrite prop_imp by auto.
  auto.
Qed.

Lemma EnvironBox_sepcon: forall P Q, EnvironBox P * EnvironBox Q |-- EnvironBox (P * Q).
Proof.
  intros.
  unfold EnvironBox; simpl; intro rho.
  apply allp_right; intro rho'.
  apply imp_andp_adjoint; normalize.
  apply sepcon_derives; apply (allp_left _ rho'); 
  rewrite prop_imp by auto; auto.
Qed.

Lemma EnvironBox_andp: forall P Q, EnvironBox (P && Q) = EnvironBox P && EnvironBox Q.
Proof.
  intros.
  unfold EnvironBox; apply pred_ext; simpl; intro rho.
  + apply andp_right.
    - apply allp_right; intro rho'.
      apply -> imp_andp_adjoint; normalize.
      apply (allp_left _ rho'); 
      rewrite prop_imp by auto.
      apply andp_left1; auto.
    - apply allp_right; intro rho'.
      apply -> imp_andp_adjoint; normalize.
      apply (allp_left _ rho'); 
      rewrite prop_imp by auto.
      apply andp_left2; auto.
  + apply allp_right; intro rho'.
    apply -> imp_andp_adjoint; normalize.
    apply andp_derives; apply (allp_left _ rho'); 
    rewrite prop_imp by auto; auto.
Qed.

Lemma EnvironStable_allp: forall {T} P, (forall a: T, EnvironStable (P a)) -> EnvironStable (allp P).
Proof.
  intros.
  unfold EnvironStable in *.
  intros.
  simpl.
  apply allp_congr; intro a.
  apply H; auto.
Qed.

Lemma EnvironBox_TT: EnvironBox TT = TT.
Proof.
  intros.
  apply pred_ext.
  + apply TT_right.
  + unfold EnvironBox; intro rho.
    apply allp_right; intro rho'.
    apply imp_andp_adjoint.
    simpl; apply TT_right.
Qed.

Lemma EnvironStable_EnvironBox: forall P, EnvironStable P -> EnvironBox P = P.
Proof.
  intros.
  apply pred_ext; [apply EnvironBox_T |].
  unfold EnvironBox; intro rho.
  apply allp_right; intro rho'.
  apply imp_andp_adjoint; normalize.
  rewrite (H _ _ H0).
  auto.
Qed.

Lemma sepcon_EnvironBox_weaken: forall P Q R R', R |-- R' -> P |-- Q * EnvironBox R -> P |-- Q * EnvironBox R'.
Proof.
  intros.
  eapply derives_trans; [apply H0 |].
  apply sepcon_derives; auto.
  apply EnvironBox_derives; auto.
Qed.

Lemma EnvironBox_corable: forall P, corable P -> corable (EnvironBox P).
Proof.
  intros.
  simpl in H |- *.
  intro.
  unfold EnvironBox.
  auto.
Qed.

Lemma solve_ramify_P: forall (g l g' l' F: Env -> A),
  EnvironStable F ->
  g |-- l * F ->
  F * l' |-- g' ->
  g |-- l * EnvironBox (l' -* g').
Proof.
  intros.
  apply derives_trans with (l * F); auto.
  apply sepcon_derives; auto.
  unfold EnvironBox; simpl; intros rho.
  apply allp_right; intro rho'.
  apply imp_andp_adjoint.
  normalize.
  rewrite (H rho rho' H2).
  apply wand_sepcon_adjoint.
  apply H1.
Qed.

Lemma ramify_P_frame: forall g l g' l' F,
  EnvironStable F ->
  g |-- l * EnvironBox (l' -* g') ->
  g * F |-- l * EnvironBox (l' -* g' * F).
Proof.
  intros.
  apply solve_ramify_P with (EnvironBox (l' -* g') * F).
  + apply EnvironStable_sepcon; auto.
    apply EnvironBox_EnvironStable.
  + rewrite <- sepcon_assoc.
    apply sepcon_derives; auto.
  + rewrite (sepcon_comm _ l'), <- sepcon_assoc.
    apply sepcon_derives; [| auto].
    rewrite sepcon_comm; apply wand_sepcon_adjoint.
    apply EnvironBox_T.
Qed.

Lemma split_ramify_P: forall g1 g2 l1 l2 g1' g2' l1' l2',
  g1 |-- l1 * EnvironBox (l1' -* g1') ->
  g2 |-- l2 * EnvironBox (l2' -* g2') ->
  g1 * g2 |-- (l1 * l2) * EnvironBox (l1' * l2' -* g1' * g2').
Proof.
  intros.
  apply solve_ramify_P with (EnvironBox (l1' -* g1') * EnvironBox (l2' -* g2')).
  + apply EnvironStable_sepcon;
    apply EnvironBox_EnvironStable.
  + rewrite (sepcon_assoc l1), <- (sepcon_assoc l2), (sepcon_comm l2), (sepcon_assoc _ l2), <- (sepcon_assoc l1).
    apply sepcon_derives; auto.
  + apply wand_sepcon_adjoint.
    eapply derives_trans; [apply EnvironBox_sepcon |].
    eapply derives_trans; [apply EnvironBox_T |].
    apply wand_sepcon_wand.
Qed.

Lemma go_lower_ramify_P: forall (g l g' l': A),
  g |-- l * (l' -* g') ->
  @Basics.const A Env g |-- Basics.const l * EnvironBox (Basics.const l' -* Basics.const g').
Proof.
  intros.
  intro rho; unfold EnvironBox, Basics.const; simpl.
  eapply derives_trans; [exact H |].
  apply sepcon_derives; [auto |].
  apply allp_right; intro rho'.
  apply imp_andp_adjoint.
  apply andp_left1.
  auto.
Qed.

Lemma ramify_PQ_reduce0: forall {B} g l (g' l': B -> Env -> A),
  g |-- l * EnvironBox (allp (l' -* g')) ->
  g |-- l * EnvironBox (exp l' -* exp g').
Proof.
  intros.
  eapply derives_trans; [exact H |].
  apply sepcon_derives; [auto |].
  apply EnvironBox_derives.
  apply wand_sepcon_adjoint.
  rewrite exp_sepcon2.
  apply exp_left; intro x; apply (exp_right x).
  apply wand_sepcon_adjoint.
  apply (allp_left _ x).
  simpl.
  auto.
Qed.

Lemma ramify_PQ_reduce1: forall {B} g l g0 l0 (g' l': B -> Env -> A),
  corable l0 ->
  g0 |-- l0 ->
  g |-- l * EnvironBox (allp (l' -* g')) ->
  g0 && g |-- (l0 && l) * EnvironBox (allp (l' -* g')).
Proof.
  intros.
  rewrite corable_andp_sepcon1 by auto.
  apply andp_derives; auto.
Qed.

Lemma ramify_PQ_reduce2: forall {B} g l g0 g' l' g0',
  corable g0 ->
  EnvironStable g0 ->
  (forall x: B, g0 |-- g0' x) ->
  g |-- l * EnvironBox (allp (l' -* g')) ->
  g0 && g |-- l * EnvironBox (allp (l' -* g0' && g')).
Proof.
  intros.
  eapply derives_trans; [apply andp_derives; [apply derives_refl | apply H2] |].
  rewrite <- corable_sepcon_andp1 by auto.
  apply sepcon_derives; [auto |].
  rewrite <- (EnvironStable_EnvironBox g0) at 1 by auto.
  rewrite <- EnvironBox_andp.
  apply EnvironBox_derives.
  apply allp_right; intro x.
  rewrite (andp_comm g0).
  apply imp_andp_adjoint.
  apply (allp_left _ x).
  apply imp_andp_adjoint.
  apply wand_sepcon_adjoint.
  rewrite corable_andp_sepcon2 by auto.
  change ((g0' && g') x) with (g0' x && g' x).
  change ((l' -* g') x) with (l' x -* g' x).
  apply andp_derives; auto.
  apply wand_sepcon_adjoint.
  auto.
Qed.

Lemma ramify_PQ_reduce3: forall {B} g l g' l' g0 l0 p,
  (forall x: B, corable (l0 x)) ->
  (forall x: B, l0 x |-- g0 x) ->
  (forall x: B, l0 x |-- p x) ->
  g |-- l * EnvironBox (allp (p --> (l' -* g'))) ->
  g |-- l * EnvironBox (allp (l0 && l' -* g0 && g')).
Proof.
  intros.
  apply derives_trans with (l * EnvironBox (allp (p --> (l' -* g')))).
  + auto.
  + apply sepcon_derives; auto.
    apply EnvironBox_derives.
    apply allp_right; intro x.
    apply (allp_left _ x).
    change ((l0 && l' -* g0 && g') x) with (l0 x && l' x -* g0 x && g' x).
    change ((p --> (l' -* g')) x) with (p x --> (l' x -* g' x)).
    apply wand_sepcon_adjoint.
    rewrite sepcon_comm, corable_andp_sepcon1, <- corable_sepcon_andp1 by auto.
    eapply derives_trans; [apply sepcon_derives; [apply derives_refl |] |].
    - apply andp_right; [apply andp_left1; apply derives_refl |].
      eapply derives_trans; [apply andp_derives; [apply H1 | apply derives_refl] |].
      apply modus_ponens.
    - rewrite corable_sepcon_andp1 by auto.
      apply andp_derives; auto.
      apply modus_ponens_wand.
Qed.

Lemma solve_ramify_PQ: forall {B} g l p g' l' F,
  EnvironStable F ->
  (forall x: B, corable (p x)) ->
  g |-- l * F ->
  (forall x: B, p x && (F * l' x) |-- g' x) ->
  g |-- l * EnvironBox (allp (p --> (l' -* g'))).
Proof.
  intros.
  apply derives_trans with (l * F); auto.
  apply sepcon_derives; auto.
  unfold EnvironBox; simpl; intros rho.
  apply allp_right; intro rho'.
  apply imp_andp_adjoint.
  normalize.
  rewrite (H rho rho' H3).
  clear rho H3; rename rho' into rho.
  apply allp_right; intro x.
  apply imp_andp_adjoint, wand_sepcon_adjoint.
  rewrite corable_andp_sepcon2 by apply (H0 x rho).
  apply (H2 x rho).
Qed.

Lemma ramify_PQ_frame: forall {B} g l p g' l' F,
  EnvironStable F ->
  (forall x: B, corable (p x)) ->
  g |-- l * EnvironBox (allp (p --> (l' -* g'))) ->
  g * F |-- l * EnvironBox (allp (p --> (l' -* g' * Basics.const F))).
Proof.
  intros.
  eapply derives_trans with (l * EnvironBox (allp (p --> (l' -* g'))) * F).
  + apply sepcon_derives; auto.
  + rewrite sepcon_assoc.
    apply sepcon_derives; auto.
    rewrite <- (EnvironStable_EnvironBox F) at 1 by auto.
    eapply derives_trans; [apply EnvironBox_sepcon |].
    apply EnvironBox_derives.
    apply allp_right; intro x.
    apply wand_sepcon_adjoint.
    apply (allp_left _ x).
    apply wand_sepcon_adjoint.
    change ((p --> (l' -* g' * Basics.const F)) x) with (p x --> (l' x -* g' x * F)).
    change ((p --> (l' -* g')) x) with (p x --> (l' x -* g' x)).
    apply imp_andp_adjoint.
    rewrite andp_comm, <- corable_andp_sepcon1 by auto.
    apply wand_sepcon_adjoint.
    eapply derives_trans; [apply modus_ponens |].
    rewrite wand_wand_comm.
    apply wand_derives; auto.
    apply wand_sepcon_adjoint; auto.
Qed.

Lemma split_ramify_PQ: forall {B} g1 g2 l1 l2 p g1' g2' l1' l2',
  (forall x: B, corable (p x)) ->
  g1 |-- l1 * EnvironBox (allp (p --> (l1' -* g1'))) ->
  g2 |-- l2 * EnvironBox (allp (p --> (l2' -* g2'))) ->
  g1 * g2 |-- (l1 * l2) * EnvironBox (allp (p --> (l1' * l2' -* g1' * g2'))).
Proof.
  intros.
  apply solve_ramify_PQ with (EnvironBox (allp (p --> (l1' -* g1'))) * EnvironBox (allp (p --> (l2' -* g2')))).
  + apply EnvironStable_sepcon;
    apply EnvironBox_EnvironStable.
  + auto.
  + rewrite (sepcon_assoc l1), <- (sepcon_assoc l2), (sepcon_comm l2), (sepcon_assoc _ l2), <- (sepcon_assoc l1).
    apply sepcon_derives; auto.
  + intros x.
    change ((l1' * l2') x) with (l1' x * l2' x).
    rewrite <- (sepcon_assoc _ (l1' x)), (sepcon_assoc _ _ (l1' x)), (sepcon_comm _ (l1' x)), <- (sepcon_assoc _ (l1' x)), (sepcon_assoc _ _ (l2' x)).
    rewrite <- (andp_dup (p x)), andp_assoc.
    rewrite <- corable_sepcon_andp1, <- corable_andp_sepcon1 by auto.
    rewrite <- !corable_sepcon_andp1 by auto.
    apply sepcon_derives.
    - apply wand_sepcon_adjoint; (eapply derives_trans; [apply EnvironBox_T |]).
      apply (allp_left _ x).
      apply wand_sepcon_adjoint.
      rewrite corable_sepcon_andp1, <- corable_andp_sepcon1 by auto.
      (eapply derives_trans; [apply sepcon_derives; [simpl; intros; apply modus_ponens | apply derives_refl] |]).
      apply wand_sepcon_adjoint; apply derives_refl.
    - apply wand_sepcon_adjoint; (eapply derives_trans; [apply EnvironBox_T |]).
      apply (allp_left _ x).
      apply wand_sepcon_adjoint.
      rewrite corable_sepcon_andp1, <- corable_andp_sepcon1 by auto.
      (eapply derives_trans; [apply sepcon_derives; [simpl; intros; apply modus_ponens | apply derives_refl] |]).
      apply wand_sepcon_adjoint; apply derives_refl.
Qed.

Lemma go_lower_ramify_PQ: forall {B} g l (p g' l': B -> A),
  g |-- l * (allp (p --> (l' -* g'))) ->
  Basics.const g |-- Basics.const l *
    EnvironBox (allp ((fun (x: B) (rho: Env) => p x) -->
      ((fun x _ => l' x) -* (fun x _ => g' x)))).
Proof.
  intros.
  intro rho; unfold EnvironBox, Basics.const; simpl.
  eapply derives_trans; [exact H |].
  apply sepcon_derives; [auto |].
  apply allp_right; intro rho'.
  apply imp_andp_adjoint.
  apply andp_left1.
  simpl.
  auto.
Qed.

Lemma reduce_frame_from_ramification: forall F Q, EnvironStable F -> F |-- EnvironBox (Q -* Q * F).
Proof.
  intros.
  unfold EnvironBox.
  simpl; intros rho.
  apply allp_right; intros rho'.
  apply imp_andp_adjoint.
  normalize.
  apply wand_sepcon_adjoint.
  rewrite sepcon_comm.
  specialize (H _ _ H0).
  rewrite H.
  auto.
Qed.

End EnvironBox_EnvironStable.
