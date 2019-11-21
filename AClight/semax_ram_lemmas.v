Require Import RamifyCoq.lib.Ensembles_ext.
Require Import RamifyCoq.lib.Relation_ext.
Require Import RamifyCoq.lib.List_ext.
Require Import RamifyCoq.msl_ext.log_normalize.
Require Import RamifyCoq.floyd_ext.closed_lemmas.
(*Require Import AClight.environ_box_stable. *)
Require Import AClight.ramification_lemmas. (* original msl_ext/ramification_lemmas.v, better to be environ_box_stable.v now*)
Require Import AClight.ramification.
Require Import VST.floyd.base.
Require Import VST.floyd.canon.
Require Import VST.floyd.assert_lemmas.
Require Import VST.floyd.client_lemmas.
Require Import VST.floyd.closed_lemmas.
Require Import VST.floyd.seplog_tactics.
Require Import VST.floyd.local2ptree_denote.
Require Import VST.floyd.call_lemmas.
Require Import VST.floyd.go_lower.
(* Require Import RamifyCoq.floyd_ext.exists_trick. *)

Local Open Scope logic.

Lemma vars_relation_Included: forall P Q, Included P Q -> inclusion _ (vars_relation P) (vars_relation Q).
Proof.
  intros.
  intros ? ? ?.
  unfold vars_relation in *.
  split.
  + unfold Included, Ensembles.In in H.
    destruct H0 as [? _].
    firstorder.
  + exact (proj2 H0).
Qed.


Section SEMAX.

Context {Espec: OracleKind}.
Context {cs: compspecs}.


(*
Lemma semax_ram_unlocalize': forall Delta l g s F P0 P1 P c Q P'
  (frame_sound: g |-- l * (P1 && (P -* P')))
  (frame_closed: Forall (fun s => closed_wrt_modvars s (P1 && (P -* P'))) s),
  corable P0 ->
  corable P1 ->
  semax_ram Delta F (P0 && P1 && P') c Q ->
  semax_ram Delta
   (RAM_FRAME.Build_SingleFrame l g s
     (RAM_FRAME.Build_SingleFrame' (P1 && (P -* P')) frame_sound frame_closed) :: F) (P0 && P) c Q.
Proof.
  intros.
Opaque LiftNatDed' LiftSepLog'.
  simpl.
Transparent LiftNatDed' LiftSepLog'.
  eapply semax_ram_pre; [| eauto].
  rewrite corable_andp_sepcon1 by auto.
  rewrite andp_assoc.
  apply andp_derives; [auto |].
  rewrite corable_sepcon_andp1 by auto. 
  apply andp_derives; [auto |].
  rewrite sepcon_comm.
  apply wand_sepcon_adjoint.
  auto.
Qed.

Lemma corable_PROP_LOCAL: forall P Q R, corable R -> corable (PROPx P (LOCALx Q R)).
Proof.
Opaque LiftNatDed' LiftSepLog' LiftCorableSepLog'.
  intros.
  unfold PROPx, LOCALx.
  apply corable_andp; auto.
  unfold local, lift1.
  apply corable_andp; auto.
  unfold_lift.
Transparent LiftNatDed' LiftSepLog' LiftCorableSepLog'.
  simpl.
  intros.
  auto.
Qed.

Lemma frame_sound_aux: forall g l R P' Q1' R',
  g |-- PROPx P' (LOCALx Q1' TT) ->
  g |-- l * (SEPx R -* SEPx R') ->
  g |-- l * (PROPx P' (LOCALx Q1' TT) && (SEPx R -* SEPx R')).
Proof.
  intros.
  rewrite corable_sepcon_andp1 by (apply corable_PROP_LOCAL; simpl; auto).
  apply andp_right; auto.
Qed.

Lemma frame_closed_aux: forall s R P' Q' Q1' Q2' R',
  split_by_closed s Q' Q1' Q2' ->
  Forall (fun s => closed_wrt_modvars s (SEPx R -* SEPx R')) s ->
  Forall (fun s => closed_wrt_modvars s (PROPx P' (LOCALx Q1' TT) && (SEPx R -* SEPx R'))) s.
Proof.
  intros.
  apply split_by_closed_spec with (P := P') in H.
  destruct H as [? _].
  rewrite Forall_forall in *.
  intros x HH; specialize (H x HH); specialize (H0 x HH).
  auto with closed.
Qed.

Lemma semax_ram_unlocalize_PROP_LOCAL_SEP: forall Delta l g s F P Q R c Ret P' Q' Q1' Q2' R'
  (SPLIT: split_by_closed s Q' Q1' Q2')
  (SEP_frame_sound: g |-- l * (SEPx R -* SEPx R'))
  (SEP_frame_closed: Forall (fun s => closed_wrt_modvars s (SEPx R -* SEPx R')) s)
  (PURE_frame_sound: g |-- PROPx P' (LOCALx Q1' TT)),
  PROPx P (LOCALx Q (SEPx R)) |-- PROPx nil (LOCALx Q2' TT) ->
  semax_ram Delta F (PROPx P' (LOCALx Q' (SEPx R'))) c Ret ->
  semax_ram Delta
   (RAM_FRAME.Build_SingleFrame l g s
     (RAM_FRAME.Build_SingleFrame'
       (PROPx P' (LOCALx Q1' TT) && (SEPx R -* SEPx R'))
       (frame_sound_aux _ _ _ _ _ _ PURE_frame_sound SEP_frame_sound)
       (frame_closed_aux _ _ _ _ _ _ _ SPLIT SEP_frame_closed)) :: F)
   (PROPx P (LOCALx Q (SEPx R))) c Ret.
Proof.
  intros.
  eapply semax_ram_pre with (PROPx nil (LOCALx Q2' (SEPx R))).
  1: rewrite SEPx_sepcon with (Q := Q2'); apply andp_right;
       [eauto | rewrite SEPx_sepcon; apply andp_left2; auto].
  rewrite SEPx_sepcon in H |- *.
  apply semax_ram_unlocalize';
   [ apply corable_PROP_LOCAL; simpl; auto
   | apply corable_PROP_LOCAL; simpl; auto
   |].
  apply split_by_closed_spec with (P := P') in SPLIT.
  rewrite (andp_comm (PROP  ()  (LOCALx Q2' TT))), <- (proj2 SPLIT).
  rewrite SEPx_sepcon in H0; auto.
Qed.

Lemma semax_ram_abduction: forall Delta l g s F P c Q F0
  (frame_sound: g |-- l * F0)
  (frame_closed: Forall (fun s => closed_wrt_modvars s F0) s),
  semax_ram Delta F (P * F0) c Q ->
  semax_ram Delta
    (RAM_FRAME.Build_SingleFrame l g s
      (RAM_FRAME.Build_SingleFrame' F0 frame_sound frame_closed) :: F) P c Q.
Proof.
  intros.
Opaque LiftNatDed' LiftSepLog'.
  simpl.
Transparent LiftNatDed' LiftSepLog'.
  eapply semax_ram_pre; [| eauto]; auto.
Qed.
*)

Lemma revert_exists_left: forall {A} (x : A) P (Q: environ -> mpred),
  (EX  x : A, P x) |-- Q ->
  (P x) |-- Q.
Proof.
  intros.
  eapply derives_trans; [| eauto].
  apply (exp_right x); auto.
Qed.

Lemma revert_prop_left: forall {PureF: Prop},
  PureF -> 
  forall P Q R Post,
  PROPx (PureF :: P) (LOCALx Q (SEPx R)) |-- Post ->
  PROPx P (LOCALx Q (SEPx R)) |-- Post.
Proof.
  intros.
  eapply derives_trans; [| eauto].
  unfold PROPx; simpl; intros; normalize.
Qed.
  
End SEMAX.


Local Open Scope logic.

Inductive RamAssu :=
  | RamAssu_intro: forall A: Prop, A -> RamAssu.

Inductive RamBind :=
  | RamBind_intro: forall A: Type, A -> RamBind.

Delimit Scope RamBind with RamBind.
Delimit Scope RamAssu with RamAssu.
(*
Notation " [ ] " := (@nil RamAssu) : RamAssu.
Notation " [ x ] " := (cons (RamAssu_intro _ x) nil) : RamAssu.
Notation " [ x ; .. ; y ] " := (cons (RamAssu_intro _ x) .. (cons (RamAssu_intro _ y) nil) ..) : RamAssu.
Notation " [ ] " := (@nil RamBind) : RamBind.
Notation " [ x ] " := (cons (RamBind_intro _ x) nil) : RamBind.
Notation " [ x ; .. ; y ] " := (cons (RamBind_intro _ x) .. (cons (RamBind_intro _ y) nil) ..) : RamBind.
*)
Definition Prop_of_RamAssu (p: RamAssu) :=
  match p with
  | RamAssu_intro A _ => A
  end.

(* This is just two copy of fold_right and one copy of map.
   They are defined for more convenient unfolding. *)
Fixpoint fold_right_and_True_RamAssu (l: list RamAssu) :=
  match l with
  | nil => True
  | P :: nil => Prop_of_RamAssu P
  | P :: l0 => Prop_of_RamAssu P /\ fold_right_and_True_RamAssu l0
  end.

Fixpoint fold_right_sepcon_emp (l: list mpred) :=
  match l with
  | nil => emp
  | P :: nil => P
  | P :: l0 => P * fold_right_sepcon_emp l0
  end.

Lemma fold_right_and_True_spec: forall l,
  @eq (environ -> mpred)
    (!! fold_right_and_True_RamAssu l)
    (!! fold_right and True (map Prop_of_RamAssu l)).
Proof.
  intros.
  apply ND_prop_ext.
  destruct l; [tauto |].
  revert r; induction l; intros.
  + simpl.
    tauto.
  + change (fold_right_and_True_RamAssu (r :: a :: l))
      with (Prop_of_RamAssu r /\ fold_right_and_True_RamAssu (a :: l)).
    change (fold_right and True (map Prop_of_RamAssu (r :: a :: l)))
      with (Prop_of_RamAssu r /\ fold_right and True (map Prop_of_RamAssu (a :: l))).
    specialize (IHl a).
    tauto.
Qed.

Lemma fold_right_sepcon_emp_spec: forall l,
  fold_right_sepcon_emp l = fold_right sepcon emp l.
Proof.
  intros.
  destruct l; auto.
  revert m; induction l; intros.
  + simpl.
    symmetry; apply sepcon_emp.
  + change (fold_right_sepcon_emp (m :: a :: l)) with (m * fold_right_sepcon_emp (a::l)).
    change (fold_right sepcon emp (m :: a :: l)) with (m * fold_right sepcon emp (a::l)).
    specialize (IHl a).
    rewrite IHl; auto.
Qed.

Definition compute_frame (assu: list RamAssu) (P: environ -> mpred) :=
  !! (fold_right_and_True_RamAssu assu) --> P.

Lemma compute_frame_sound: forall assu (P Q: environ -> mpred), P |-- compute_frame assu Q -> P |-- Q.
Proof.
  intros.
  eapply derives_trans; [exact H |].
  unfold compute_frame.
  rewrite fold_right_and_True_spec.
  rewrite prop_imp; auto.
  clear.
  induction assu.
  + simpl.
    auto.
  + simpl.
    split; auto.
    destruct a; simpl.
    auto.
Qed.

(*
Inductive NatDed_weaken : forall {A: Type} {NA: NatDed A} (P Q: A), Prop :=
  | weaken_refl: forall {A: Type} {NA: NatDed A} (P: A), NatDed_weaken P P
  | weaken_imp: forall {A: Type} {NA: NatDed A} (P Q: A) (R: Prop), R -> NatDed_weaken P Q -> NatDed_weaken (!! R --> P) Q
  | weaken_allp: forall {A B: Type} {NA: NatDed A} (x: B) (P Q: B -> A), NatDed_weaken P Q -> NatDed_weaken (allp P) (Q x).

Lemma NatDed_weaken_weaken: forall {A: Type} {NA: NatDed A} (P Q: A),
  NatDed_weaken P Q -> P |-- Q.
Proof.
  intros.
  induction H.
  + auto.
  + rewrite prop_imp by auto.
    auto.
  + apply allp_left'.
    auto.
Qed.
*)
Lemma PROPx_andp: forall P Q, PROPx P Q = PROPx P TT && Q.
Proof.
  intros.
  unfold PROPx.
  rewrite andp_TT.
  auto.
Qed.

Lemma LOCALx_andp: forall P Q, LOCALx P Q = LOCALx P TT && Q.
Proof.
  intros.
  unfold LOCALx.
  rewrite andp_TT.
  auto.
Qed.

Lemma SEPx_andp: forall P Q R, PROPx P (LOCALx Q (SEPx R)) = PROPx P (LOCALx Q TT) && SEPx R.
Proof.
  intros.
  unfold PROPx, LOCALx.
  rewrite andp_TT.
  rewrite andp_assoc.
  auto.
Qed.

(* TODO: this can be written in be more elegent way. *)
Inductive split_by_closed:
 statement -> list localdef -> list localdef -> list localdef -> Prop :=
 | split_by_closed_nil: forall s, split_by_closed s nil nil nil
 | split_by_closed_cons_closed: forall s q Q Q1 Q2,
     closed_wrt_modvars s (local (locald_denote q)) ->
     split_by_closed s Q Q1 Q2 ->
     split_by_closed s (q :: Q) (q :: Q1) Q2
 | split_by_closed_cons_unclosed: forall s q Q Q1 Q2,
     split_by_closed s Q Q1 Q2 ->
     split_by_closed s (q :: Q) Q1 (q :: Q2).

Lemma insert_local': forall Q1 Q R,
  local (locald_denote Q1) && (LOCALx Q R) = LOCALx (Q1 :: Q) R.
Proof.
intros. extensionality rho.
unfold LOCALx, local; super_unfold_lift. simpl.
apply pred_ext; autorewrite with gather_prop; normalize;
decompose [and] H; clear H.
Qed.

Lemma split_by_closed_spec: forall s Q Q1 Q2,
  split_by_closed s Q Q1 Q2 ->
  EnvironStable (vars_relation (modifiedvars s)) (LOCALx Q1 TT) /\
  LOCALx Q TT = LOCALx Q1 TT && LOCALx Q2 TT.
Proof.
  intros.
  split.
  + rewrite EnvironStable_var_relation_closed.
    induction H.
    - auto with closed.
    - rewrite <- insert_local'.
      auto with closed.
    - auto.
  + induction H.
    - apply add_andp; auto.
    - rewrite <- !insert_local'.
      rewrite IHsplit_by_closed.
      rewrite andp_assoc; auto.
    - rewrite <- !insert_local'.
      rewrite IHsplit_by_closed.
      rewrite <- !andp_assoc.
      rewrite (andp_comm (local (locald_denote q))); auto.
Qed.

Lemma corable_PROP: forall P, corable (PROPx P TT).
Proof.
Opaque LiftNatDed' LiftSepLog' LiftCorableSepLog'.
  intros.
  unfold PROPx.
  apply corable_andp; auto.
Transparent LiftNatDed' LiftSepLog' LiftCorableSepLog'.
  simpl; auto.
Qed.

Lemma corable_LOCAL: forall P, corable (LOCALx P TT).
Proof.
Opaque LiftNatDed' LiftSepLog' LiftCorableSepLog'.
  intros.
  unfold LOCALx.
  apply corable_andp; [| unfold TT; auto].
  unfold local, lift1.
  unfold_lift.
Transparent LiftNatDed' LiftSepLog' LiftCorableSepLog'.
  simpl.
  intros.
  auto.
Qed.

Definition check_one_var_spec (Q: PTree.t (type * val)) (idv: ident * (type * val)) : Prop :=
   (Q ! (fst idv)) = Some (snd idv).

Lemma local2ptree_soundness'' : forall Q T1 T2 gv,
  local2ptree Q = (T1, T2, nil, gv) ->
  LOCALx Q TT = LOCALx (LocalD T1 T2 gv) TT.
Proof.
  intros.
  eapply local2ptree_soundness in H.
  match goal with |- LOCALx _ ?B = _ =>
    replace B with (SEPx(TT::nil))
  end.
  instantiate (2:=@nil Prop) in H.
  simpl app in H.
  unfold PROPx in H.
  simpl fold_right in H.
  rewrite !prop_true_andp in H by auto. apply H.
  extensionality rho; unfold SEPx; simpl. rewrite sepcon_emp. reflexivity.
Qed.
(*
Lemma solve_LOCALx_entailer: forall {cs: compspecs} P Ptemp Pvar Q Qtemp Qvar GV,
  local2ptree P = (Ptemp, Pvar, nil, GV) ->
  local2ptree Q = (Qtemp, Qvar, nil, GV) ->
  Forall (check_one_var_spec Pvar) (PTree.elements Qvar) ->
  Forall (check_one_temp_spec Ptemp) (PTree.elements Qtemp) ->
  LOCALx P TT |-- LOCALx Q TT.
Proof.
  intros.
  erewrite (local2ptree_soundness'' P) by eauto.
  erewrite (local2ptree_soundness'' Q) by eauto.
  unfold LOCALx, local, lift1; simpl; normalize; intros.
  Search map locald_denote LocalD .
  auto.
  eapply check_specs_lemma'; eauto.
Qed.
*)
Lemma canonical_ram_reduce0: forall {A B C} {NA: NatDed A} (P: C -> B -> A),
  allp (fun x => P (fst x) (snd x)) |-- allp (allp P).
Proof.
  intros.
  eapply derives_trans; [| apply allp_derives; intro; apply derives_refl].
  rewrite allp_uncurry.
  apply derives_refl.
Qed.

Lemma canonical_ram_reduce1: forall {A} QG RG QL RL s QL' RL' QG' RG' (Pure: A -> Prop) QG1' QG2',
  (forall a: A, exists TempG1 TempG2,
    split_by_closed s (QG' a) TempG1 TempG2 /\
    QG1' a = TempG1 /\
    QG2' a = TempG2) ->
  LOCALx QG TT |-- LOCALx QL TT ->
  (forall a: A, LOCALx QG TT |-- LOCALx (QG1' a) TT) ->
  (forall a: A, LOCALx (QL' a) TT |-- LOCALx (QG2' a) TT) ->
  SEPx RG |-- SEPx RL *
    ModBox s (ALL a: A, !! Pure a --> (SEPx (RL' a) -* SEPx (RG' a))) ->
  PROPx nil (LOCALx QG (SEPx RG)) |--
  PROPx nil (LOCALx QL (SEPx RL)) *
    ModBox s (ALL a: A, !! Pure a -->
               (PROPx nil (LOCALx (QL' a) (SEPx (RL' a))) -* 
                  PROPx nil (LOCALx (QG' a) (SEPx (RG' a))))).
Proof.
  intros.
  assert (forall a,
            EnvironStable (vars_relation (modifiedvars s)) (LOCALx (QG1' a) TT) /\
            LOCALx (QG' a) TT = LOCALx (QG1' a) TT && LOCALx (QG2' a) TT).
  1: {
    intro a; clear - H.
    destruct (H a) as [? [? [? [? ?]]]].
    subst.
    apply split_by_closed_spec; auto.
  }
  pose proof (fun a => (proj1 (H4 a))).
  pose proof (fun a => (proj2 (H4 a))).
  clear H H4.
  rewrite !(PROPx_andp _ (LOCALx _ _)).
  rewrite !(LOCALx_andp _ (SEPx _)).

  rewrite corable_andp_sepcon1 by apply corable_PROP.
  apply andp_derives; auto.
  rewrite corable_andp_sepcon1 by apply corable_LOCAL.
  apply andp_right; [apply andp_left1; auto |].

  eapply sepcon_EnvironBox_weaken with
   (allp 
     ((fun a: A => LOCALx (QG1' a) TT) && 
      (fun a: A => LOCALx (QL' a) TT --> LOCALx (QG2' a) TT) && 
      (fun a: A => 
       (!!Pure a --> (SEPx (RL' a) -* SEPx (RG' a)))))).
  1: {
    apply allp_derives; intro a.
    change
     (((fun a0 : A => LOCALx (QG1' a0) TT) &&
        (fun a0 : A => LOCALx (QL' a0) TT --> LOCALx (QG2' a0) TT) &&
        (fun a0 : A => !!Pure a0 --> (SEPx (RL' a0) -* SEPx (RG' a0)))) a)
    with
     (LOCALx (QG1' a) TT &&
      (LOCALx (QL' a) TT --> LOCALx (QG2' a) TT) &&
      (!!Pure a --> (SEPx (RL' a) -* SEPx (RG' a)))).
    rewrite !(PROPx_andp _ (LOCALx _ _)).
    rewrite !(LOCALx_andp _ (SEPx _)).
    rewrite H6.
    unfold PROPx; simpl fold_right.
    fold (@TT (environ -> mpred) _); rewrite !TT_andp.
    rewrite <- imp_andp_adjoint.
    apply derives_extract_prop'; intro; rewrite prop_imp by auto.
    rewrite !andp_assoc.
    eapply derives_trans; [| apply wand_corable_andp; apply corable_LOCAL].
    apply andp_derives; auto.
    apply corable_andp_wand_corable_andp; apply corable_LOCAL.
  }

  rewrite !allp_andp.
  rewrite !@EnvironBox_andp.
  rewrite andp_assoc, corable_sepcon_andp1
    by (apply EnvironBox_corable, @corable_allp; intro; apply corable_LOCAL).
  apply andp_derives.
  1: {
    rewrite @EnvironStable_EnvironBox.
    + apply allp_right; intro a; auto.
    + apply vars_relation_Equivalence.
    + apply EnvironStable_allp; auto.
  }

  rewrite corable_sepcon_andp1
    by (apply EnvironBox_corable, @corable_allp; intro;
        apply corable_imp; apply corable_LOCAL).
  apply andp_right.
  1: {
    apply derives_trans with TT; [apply TT_right |].
    rewrite <- (@EnvironBox_TT _ _ _ (vars_relation (modifiedvars s))) at 1.
    apply EnvironBox_derives.
    apply allp_right; intro a.
    apply imp_andp_adjoint.
    apply andp_left2; auto.
   }      

   auto.
Qed.

Lemma canonical_ram_reduce2: forall {A: Type} s G L L' G' (Pure: A -> Prop),
  fold_right_sepcon_emp G |--
    fold_right_sepcon_emp L *
     (ALL a: A, !! Pure a -->
        (fold_right_sepconx (L' a) -* fold_right_sepconx (G' a))) ->
  SEPx G |-- SEPx L * ModBox s (ALL a: A, !! Pure a --> (SEPx (L' a) -* SEPx (G' a))).
Proof.
  intros.
  apply sepcon_EnvironBox_weaken with
   (ALL  a : A , !!Pure a --> (SEPx (L' a) -* SEPx (G' a))).
  1: {
    apply allp_derives; intro a.
    auto.
  }

  intro rho; unfold SEPx at 1 2; simpl.

  fold (ModBox s); rewrite go_lower_ModBox.

  rewrite !fold_right_sepcon_emp_spec in H.
  eapply derives_trans; [exact H |].
  apply sepcon_derives; [apply derives_refl |].
  apply allp_right; intro rho'.
  apply imp_andp_adjoint; apply derives_extract_prop'; intro.
  apply allp_derives; intro a.
  rewrite !fold_right_sepconx_eq.
  unfold SEPx.
  auto.
Qed.
(*
Lemma destruct_pointer_val_VP: forall x,
  pointer_val_val x <> nullval \/
  isptr (pointer_val_val x) ->
  isptr (pointer_val_val x) /\ exists b i, x = ValidPointer b i.
Proof.
  intros.
  destruct x; try simpl in H; try tauto.
  split; simpl; auto.
  exists b, i; auto.
Qed.

Lemma destruct_pointer_val_NP: forall x,
  pointer_val_val x = nullval \/
  ~ isptr (pointer_val_val x) ->
  x = NullPointer.
Proof.
  intros.
  destruct x; try simpl in H; try tauto.
  inversion H; try tauto.
  inversion H0.
Qed.

Ltac destruct_pointer_val x :=
  first [
    let H := fresh "H" in
    assert (isptr (pointer_val_val x) /\ exists b i, x = ValidPointer b i) by (apply (destruct_pointer_val_VP x); tauto);
    destruct H as [?H [?b [?i ?H]]]
  | assert (x = NullPointer) by (apply (destruct_pointer_val_NP x); tauto)].
*)

Ltac pose_PROPx P :=
  match P with
  | ?Pr :: ?P0 => first [assert Pr as _ by assumption | assert Pr; [auto |]];
                  [.. | pose_PROPx P0]
  | nil => idtac
  end.

Lemma solve_LOCALx_entailer: forall L1 L2,
  PROPx nil (LOCALx L1 (SEPx (TT :: nil))) |-- PROPx nil (LOCALx L2 (SEPx (TT::nil))) ->
  LOCALx L1 TT |-- LOCALx L2 TT.
Proof.
  intros.
  unfold PROPx, SEPx, fold_right_sepcon in H.
  normalize in H.
Qed.

Ltac solve_LOCALx_entailer_tac :=
  apply solve_LOCALx_entailer; go_lower; auto.
(****************
Ltac localize L :=
  match goal with
  | |- semax ?Delta ?Pre ?c ?Post =>
         change (semax Delta Pre c Post) with (semax_ram Delta nil Pre c Post);
         abbreviate_RamFrame
  | |- semax_ram ?Delta _ ?Pre ?c ?Post => idtac
  end;
  match L with
  | PROPx ?P (LOCALx ?Q (SEPx ?R)) =>
         match goal with
         | |- semax_ram _ _ (PROPx _ (LOCALx ?Q_Goal (SEPx _))) _ _ =>
                first [
                  assert (LOCALx Q_Goal TT |-- LOCALx Q TT) as _ by solve_LOCALx_entailer_tac |
                  pose proof I as WARNING___New_local_part_should_be_a_subset_of_the_original_one]
         end;
         pose_PROPx P; [.. |
         apply semax_ram_localize with (PROPx nil (LOCALx Q (SEPx R))); eexists;
         abbreviate_RamFrame]
  end.
****************)
Ltac solve_split_by_closed :=
  repeat first
    [ apply split_by_closed_nil
    | apply split_by_closed_cons_closed; [solve [repeat constructor; auto with closed] |]
    | apply split_by_closed_cons_unclosed].

Ltac super_solve_split :=
  let a := fresh "a" in
  intro a; eexists; eexists;
  split; [solve_split_by_closed | split];
  match goal with
  | |- _ = ?r => super_pattern r a; apply eq_refl
  end.

Inductive RamUnit: Type :=
  | RamTT: RamUnit.

Lemma allp_unit': forall {A: Type} {NA: NatDed A} (P: A), allp (fun _: RamUnit => P) |-- P.
Proof.
  intros.
  (* rewrite allp_unit. *)
  apply (allp_left _ RamTT).
  apply derives_refl.
Qed.

Lemma remove_allp_RamUnit: forall P Q R: mpred, P |-- Q * R -> P |-- Q * ALL _ : RamUnit, R.
Proof.
  intros.
  eapply sepcon_weaken; [| eauto].
  apply allp_right; auto.
Qed.

Ltac construct_frame_bind bind :=
  match bind with
  | RamBind_intro _ ?x :: ?bind0 => 
      match goal with
      | |- _ |-- ?r =>
          super_pattern r x;
          apply (allp_left' x);
          construct_frame_bind bind0
      end
  | nil =>
      apply allp_unit'
  end.

(*
   Solve this goal:
   ? |--
     PROPx nil (LOCALx QL' (SEPx RL')) -*
       PROPx nil (LOCALx QG' (SEPx RG'))
*)
Ltac construct_frame assu bind :=
  apply (compute_frame_sound assu);
  unfold compute_frame, fold_right_and_True_RamAssu, Prop_of_RamAssu;
  construct_frame_bind bind.
(****************
Ltac unlocalize' G' assu bind :=
  clear_RamFrame_abbr;
  match G' with
  | PROPx ?PG' (LOCALx ?QG' (SEPx ?RG')) =>
         pose_PROPx PG';
         [ ..
         | eapply semax_ram_unlocalize' with (P' := PROPx nil (LOCALx QG' (SEPx RG')));
           [ construct_frame assu bind
           | ]
         ]
  end;
  gather_current_goal_with_evar.

Tactic Notation "unlocalize" constr(G') "using" constr(assu) "binding" constr(bind) :=
  unlocalize' G' assu bind.         
                                    
Tactic Notation "unlocalize" constr(G') "using" constr(assu) :=
  unlocalize' G' assu []%RamBind.   
                                    
Tactic Notation "unlocalize" constr(G') "binding" constr(bind) :=
  unlocalize' G' []%RamAssu bind.

Tactic Notation "unlocalize" constr(G') :=
  unlocalize' G' []%RamAssu []%RamBind.
****************)
Ltac canonical_ram_reduce0 :=
  match goal with
  | |- _ |-- allp (allp (allp _)) =>
            (eapply derives_trans; [| apply allp_derives'; canonical_ram_reduce0]);
            canonical_ram_reduce0
  | |- _ |-- allp (allp _) => apply canonical_ram_reduce0
  | |- _ |-- _ => apply derives_refl
  end.

Ltac simplify_ramif :=
  eapply sepcon_EnvironBox_weaken; [canonical_ram_reduce0 | cbv beta];
  
  match goal with
  | |- _ |-- _ * EnvironBox _ (allp ?Frame) =>
    let a := fresh "a" in
    let F := fresh "F" in
      eapply @sepcon_EnvironBox_weaken; 
      [ apply @allp_derives; intro a;
        match goal with
        | |- _ |-- !! ?Pure -->
             (PROPx _ (LOCALx ?QL' (SEPx ?RL')) -*
              PROPx _ (LOCALx ?QG' (SEPx ?RG'))) =>
            try super_pattern Pure a;
            try super_pattern QL' a;
            try super_pattern QG' a;
            try super_pattern RL' a;
            try super_pattern RG' a
        end;
        match goal with
        | |- _ |-- ?Right => super_pattern Right a; apply derives_refl
        end
      |]
  end;

  eapply canonical_ram_reduce1;
    [ super_solve_split
    | solve_LOCALx_entailer_tac
    | intro; solve_LOCALx_entailer_tac
    | intro; solve_LOCALx_entailer_tac
    | ];

  match goal with
  | |- _ |-- _ * ModBox _ (allp ?Frame) =>
    let a := fresh "a" in
    let F := fresh "F" in
      eapply @sepcon_EnvironBox_weaken; 
      [ apply @allp_derives; intro a;
        match goal with
        | |- _ |-- !! ?Pure --> (SEPx ?RL' -* SEPx ?RG') =>
            try super_pattern Pure a;
            try super_pattern RL' a;
            try super_pattern RG' a
        end;
        match goal with
        | |- _ |-- ?Right => super_pattern Right a; apply derives_refl
        end
      |]
  end;

  eapply canonical_ram_reduce2;
  unfold fold_right_sepcon_emp;

  try
   (let a := fresh "a" in
    eapply @sepcon_weaken; 
    [ apply @allp_derives; intro a;
      match goal with
      | |- ?Left |-- !! True --> ?F =>
          let ll := fresh "l" in
          set (ll := Left); rewrite (@prop_imp mpred _ True F I); subst ll;
          super_pattern F a; apply derives_refl
      end
    |]);

  try apply remove_allp_RamUnit.
(*
Lemma pointer_val_val_is_pointer_or_null: forall x,
  is_pointer_or_null (pointer_val_val x).
Proof.
  intros.
  destruct x; simpl; auto.
Qed.

Hint Resolve pointer_val_val_is_pointer_or_null.
*)
