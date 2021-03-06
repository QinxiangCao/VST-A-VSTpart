Require Import RamifyCoq.lib.Ensembles_ext.
Require Import RamifyCoq.lib.Relation_ext.
Require Import RamifyCoq.lib.List_ext.
Require Import RamifyCoq.msl_ext.log_normalize.
Require Import RamifyCoq.floyd_ext.closed_lemmas.
Require Import AClight.environ_box_stable.
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

Lemma canonical_ram_reduce0: forall {A B C} {NA: NatDed A} (P: C -> B -> A),
  allp (fun x => P (fst x) (snd x)) |-- allp (allp P).
Proof.
  intros.
  eapply derives_trans; [| apply allp_derives; intro; apply derives_refl].
  rewrite allp_uncurry.
  apply derives_refl.
Qed.

Lemma canonical_ram_reduce1: forall {A} Delta QG RG QL RL s QL' RL' QG' RG' (Pure: A -> Prop) QG1' QG2',
  (forall a: A, exists TempG1 TempG2,
    split_by_closed s (QG' a) TempG1 TempG2 /\
    QG1' a = TempG1 /\
    QG2' a = TempG2) ->
  ENTAIL Delta, LOCALx QG TT |-- LOCALx QL TT ->
  (forall a: A, ENTAIL Delta, LOCALx QG TT |-- LOCALx (QG1' a) TT) ->
  (forall a: A, ENTAIL Delta, LOCALx (QL' a) TT |-- LOCALx (QG2' a) TT) ->
  SEPx RG |-- SEPx RL *
    ModBox s (ALL a: A, !! Pure a --> (SEPx (RL' a) -* SEPx (RG' a))) ->
  ENTAIL Delta,
  PROPx nil (LOCALx QG (SEPx RG)) |--
  PROPx nil (LOCALx QL (SEPx RL)) *
    ModBox s (local (tc_environ Delta) -->
               (ALL a: A, !! Pure a -->
                 (PROPx nil (LOCALx (QL' a) (SEPx (RL' a))) -* 
                    PROPx nil (LOCALx (QG' a) (SEPx (RG' a)))))).
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
  rewrite <- andp_assoc, (andp_comm (local _)), andp_assoc.
  apply andp_derives; auto.
  rewrite corable_andp_sepcon1 by apply corable_LOCAL.
  apply andp_right; [rewrite <- andp_assoc; apply andp_left1; auto |].

  eapply sepcon_EnvironBox_weaken' with
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
  match goal with
  | |- _ |-- _ * EnvironBox _ (?TC --> (?A && ?B && ?C)) =>
    eapply sepcon_EnvironBox_weaken with
        (A && (TC --> B) && C)
  end.
  {
    rewrite <- imp_andp_adjoint.
    repeat apply andp_right.
    + solve_andp.
    + rewrite imp_andp_adjoint.
      solve_andp.
    + solve_andp.
  }
  rewrite !@EnvironBox_andp.
  rewrite andp_assoc, corable_sepcon_andp1
    by (apply EnvironBox_corable, @corable_allp; intro; apply corable_LOCAL).
  apply andp_right.
  1: {
    rewrite <- andp_assoc.
    apply andp_left1.
    rewrite @EnvironStable_EnvironBox.
    + apply allp_right; intro a; auto.
    + apply vars_relation_Equivalence.
    + apply EnvironStable_allp; auto.
  }

  rewrite corable_sepcon_andp1.
  2: {
    apply EnvironBox_corable, corable_imp.
    + apply corable_local.
    + apply @corable_allp; intro.
      apply corable_imp; apply corable_LOCAL.
  }
  rewrite <-andp_assoc.
  apply andp_derives.
  1: {
    apply derives_trans with TT; [apply TT_right |].
    rewrite <- (@EnvironBox_TT _ _ _ (vars_relation (modifiedvars s))) at 1.
    apply EnvironBox_derives.
    rewrite <- imp_andp_adjoint.
    apply allp_right; intro a.
    rewrite <- imp_andp_adjoint.
    rewrite andp_assoc.
    apply andp_left2; auto.
   }
   
   auto.
Qed.

Lemma canonical_ram_reduce2: forall {A: Type} s G L L' G' (Pure: A -> Prop),
  fold_right_sepconx G |--
    fold_right_sepconx L *
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

  rewrite !fold_right_sepconx_eq in H.
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

Lemma solve_LOCALx_entailer: forall Delta L1 L2,
  ENTAIL Delta, PROPx nil (LOCALx L1 (SEPx (TT :: nil))) |-- PROPx nil (LOCALx L2 (SEPx (TT::nil))) ->
  ENTAIL Delta, LOCALx L1 TT |-- LOCALx L2 TT.
Proof.
  intros.
  unfold PROPx, SEPx, fold_right_sepcon in H.
  normalize in H.
Qed.

Ltac solve_LOCALx_entailer_tac :=
  apply solve_LOCALx_entailer; go_lower;
  first [ apply andp_right; [apply prop_right |]; auto
        | apply prop_right; auto].

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

Inductive generalize_EX_wand: (environ -> mpred) -> (environ -> mpred) -> (environ -> mpred) -> Prop :=
| generalize_EX_wand_done: forall Pr LP LQ SP SQ,
    generalize_EX_wand (PROPx Pr (LOCALx LP (SEPx SP)))
                       (PROPx Pr (LOCALx LQ (SEPx SQ)))
                       (!! (fold_right and True Pr) -->
                          ((PROPx nil (LOCALx LP (SEPx SP))) -*
                           (PROPx nil (LOCALx LQ (SEPx SQ)))))
| generalize_EX_wand_step': forall A (P Q R: A -> environ -> mpred),
    (forall a, generalize_EX_wand (P a) (Q a) (R a)) ->
    generalize_EX_wand (exp P) (exp Q) (allp R).

Lemma generalize_EX_wand_step: forall A (P Q R: A -> environ -> mpred),
  (forall a, exists R', generalize_EX_wand (P a) (Q a) R' /\ R' = R a) ->
  generalize_EX_wand (exp P) (exp Q) (allp R).
Proof.
  intros.
  apply generalize_EX_wand_step'.
  intros.
  destruct (H a) as [? [? ?]].
  subst.
  auto.
Qed.

Lemma generalize_EX_wand_spec: forall P Q R,
  generalize_EX_wand P Q R -> R |-- P -* Q.
Proof.
  intros.
  induction H.
  + unfold PROPx.
    simpl fold_right.
    apply wand_sepcon_adjoint.
    normalize.
    unfold TT.
    rewrite prop_imp by auto.
    apply wand_sepcon_adjoint.
    auto.
  + apply wand_sepcon_adjoint.
    Intros y.
    Exists y.
    apply wand_sepcon_adjoint.
    apply allp_left with y.
    apply H0.
Qed.

Ltac generalize_EX_wand_rec_tac :=
  first
    [ simple apply generalize_EX_wand_step;
      let a := fresh "a" in
      intro a;
      eexists;
      split;
      [ generalize_EX_wand_rec_tac
      | match goal with
        | |- ?t = _ => super_pattern t a; reflexivity
        end
      ]
    | simple apply generalize_EX_wand_done
    ].

Ltac generalize_EX_wand_tac :=
  eapply generalize_EX_wand_spec;
  generalize_EX_wand_rec_tac.

Ltac simplify_ramif :=
  match goal with
  | |- context [_ || ?P -* _] => unify P (FF: environ -> mpred)
  end;
  rewrite orp_FF;
  eapply sepcon_EnvironBox_weaken'; [generalize_EX_wand_tac |];
  match goal with
  | |- _ |-- _ * EnvironBox _ (_ --> (?P --> ?Q)) => 
      apply sepcon_EnvironBox_weaken' with (allp (fun _: unit => P --> Q));
        [rewrite allp_unit; apply derives_refl |]
  | |- _ => rewrite !allp_uncurry' (* TODO: this line can be buggy *)
  end;

  match goal with
  | |- _ |-- _ * EnvironBox _ (_ --> allp ?Frame) =>
    let a := fresh "a" in
    let F := fresh "F" in
      eapply @sepcon_EnvironBox_weaken'; 
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
    | intro; cbv beta; solve_LOCALx_entailer_tac
    | intro; cbv beta; solve_LOCALx_entailer_tac
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
  unfold fold_right_sepconx;


  try
   (let a := fresh "a" in
    eapply @sepcon_weaken; 
    [ apply @allp_derives; intro a;
      match goal with
      | |- ?Left |-- !! fold_right and True nil --> ?F =>
          let ll := fresh "l" in
          set (ll := Left); rewrite (@prop_imp mpred _ True F I); subst ll;
          super_pattern F a; apply derives_refl
      end
    |]);

  try rewrite allp_unit. (** TODO: allp curry is necessary here *)
