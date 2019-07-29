Require Export VST.floyd.proofauto.
Require Import AClight.revert.

(* Two layers : (1) intro and revert (2) multi-cond *)

(********************* Part I : intro and revert ***********************)

(*Local *) Ltac semax_seq_evar :=
  let Post_name := fresh "Post" in
  evar (Post_name : assert);
  let Post := Post_name in
  first [
    simple apply semax_seq with Post
  | fail 1 "Fail in simple apply semax_seq with Post"
  ];
  only 2: (subst Post_name; abbreviate_semax).

(*Local *)Ltac repeat_Intros :=
  Intros; (* Intros Props *)
  repeat lazymatch goal with
  | |- semax _ (EX x, _) _ _ =>
    first [
      let x := fresh x in Intros x
    | fail 2 "Fail in Intros"
    ]
  | _ =>
    (* This is for existential variables inside SEP. This case occurs in testing with proofs from VST
     * but I don't know whether we still need this for VST-A. *)
    let x := fresh "x" in Intros x
  end.

Ltac forwardE :=
  repeat apply -> seq_assoc;
  lazymatch goal with
  | |- semax _ _ Sbreak _ =>
    repeat_Intros; forward
  | |- semax _ _ Scontinue _ =>
    repeat_Intros; forward
  | |- semax _ _ (Sreturn _) _ =>
    repeat_Intros; forward
  | |- semax _ _ (Ssequence Sbreak _) _ =>
    repeat_Intros; forward
  | |- semax _ _ (Ssequence Scontinue _) _ =>
    repeat_Intros; forward
  | |- semax _ _ (Ssequence (Sreturn _) _) _ =>
    repeat_Intros; forward
  | |- semax _ _ (Ssequence _ _) _ =>
    semax_seq_evar; [
      (* first statement *)
      repeat_Intros;
      forward;
      entail_evar_post
    | (* following statements *)
      abbreviate_semax
    ]
  | |- semax _ _ _ _ =>
    repeat_Intros; forward
  end.


(********************* Part II : multiple condition ***********************)

Lemma semax_orp:
  forall {Espec: OracleKind} {cs: compspecs},
    forall Delta P1 P2 c Q,
      semax Delta P1 c Q ->
      semax Delta P2 c Q ->
      semax Delta (orp P1 P2) c Q.
Proof.
  intros.
  rewrite orp_is_exp. Intros x.
  destruct x; auto.
Qed.

Lemma semax_overridePost_orp1:
  forall {Espec: OracleKind} {cs: compspecs},
    forall Delta P c Q1 Q2 Q',
      semax Delta P c (overridePost Q1 Q') ->
      semax Delta P c (overridePost (Q1 || Q2) Q').
Proof.
  intros.
  eapply semax_post1. 2 : rewrite overridePost_overridePost; eauto.
  rewrite overridePost_normal'. apply orp_right1. auto.
Qed.

Lemma semax_overridePost_orp2:
  forall {Espec: OracleKind} {cs: compspecs},
    forall Delta P c Q1 Q2 Q',
      semax Delta P c (overridePost Q2 Q') ->
      semax Delta P c (overridePost (Q1 || Q2) Q').
Proof.
  intros.
  eapply semax_post1. 2 : rewrite overridePost_overridePost; eauto.
  rewrite overridePost_normal'. apply orp_right2. auto.
Qed.

Lemma semax_orp_parallel:
  forall {Espec: OracleKind} {cs: compspecs},
    forall Delta P1 P2 c Q1 Q2 Q',
      semax Delta P1 c (overridePost Q1 Q') ->
      semax Delta P2 c (overridePost Q2 Q') ->
      semax Delta (orp P1 P2) c (overridePost (orp Q1 Q2) Q').
Proof.
  intros.
  apply semax_orp.
  - apply semax_overridePost_orp1. auto.
  - apply semax_overridePost_orp2. auto.
Qed.

Hint Rewrite orp_FF FF_orp : remove_FF_precondition.

Ltac remove_FF_precondition :=
  lazymatch goal with
  | |- semax ?Delta ?P ?c ?Q =>
    let Q_name := fresh "Q" in
    set (Q_name := Q);
    repeat rewrite orp_FF;
    repeat rewrite FF_orp;
    subst Q_name
  end.

Ltac forwardM :=
  remove_FF_precondition;
  lazymatch goal with
  | |- semax _ ?P _ _ =>
    first [
      has_evar P;
      fail 1 "Precondition should not have evar"
    | idtac
    ]
  end;
  repeat apply -> seq_assoc;
  lazymatch goal with
  | |- semax _ _ (Ssequence _ _) _ =>
    simple eapply semax_seq; [
      repeat eapply semax_orp_parallel;
      lazymatch goal with
      | |- semax _ _ _ (overridePost ?Post _) =>
        is_evar Post;
        let Post_name := fresh "Post" in
        evar (Post_name : assert);
        unify Post Post_name;
        fold Post_name;
        forwardE;
        entail_evar_post
      end
    | abbreviate_semax
    ]
  | |- semax _ _ _ _ =>
    repeat simple eapply semax_orp;
    forwardE;
    first [
      lazymatch goal with
      | |- ENTAIL _, _ |-- ?Post =>
        is_var Post;
        revert_exp_and_Prop;
        subst Post;
        repeat first [
          lazymatch goal with
          | |- _ |-- ?Post =>
            is_evar Post;
            fail 1 (* break *)
          end
        | simple apply orp_right2
        ];
        simple apply orp_right1;
        apply derives_refl
      end
    | idtac
    ]
  end.

Lemma typed_test_normalize : forall {cs: compspecs} Delta P Q R (typed_test : type -> val -> Prop) b v,
  ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |-- local (liftx (eq v) (eval_expr b)) ->
    ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) && local (liftx (typed_test (typeof b)) (eval_expr b))
    |-- PROPx (typed_test (typeof b) v :: P) (LOCALx Q (SEPx R)).
Proof.
  intros.
  eapply ENTAIL_trans with(
    local (liftx (eq v) (eval_expr b)) && (PROPx P (LOCALx Q (SEPx R)) && local (liftx (typed_test (typeof b)) (eval_expr b)))
  ).
  - apply andp_right; auto.
    eapply ENTAIL_trans with (PROPx P (LOCALx Q (SEPx R))). {
      apply andp_left2. apply andp_left1. auto.
    }
    auto.
  - rewrite <- insert_prop.
    forget (PROPx P (LOCALx Q (SEPx R))) as PQR.
    apply andp_right. 2 : {
      apply andp_left2. apply andp_left2. apply andp_left1. auto.
    }
    go_lowerx. subst v. apply prop_right. auto.
Qed.

Ltac normalize_typed_test :=
  match goal with
  | |- ENTAIL ?Delta, (PROPx ?P (LOCALx ?Q (SEPx ?R))) && local (liftx (?typed_test (typeof ?b)) (eval_expr ?b)) |-- ?Post =>
    let HRE := fresh in let v := fresh "v" in
    evar (v: val);
    do_compute_expr Delta P Q R b v HRE;
    simpl in v; (* this may simpl user definition in LOCAL *)
    simple eapply ENTAIL_trans;
    only 1 : (simple apply typed_test_normalize; exact HRE); (* I think I need to add "with v" here,
                                    but it does't work, however it works without "with v" *)
    subst v;
    let HRE := fresh in
    apply derives_extract_PROP; intro HRE;
    do_repr_inj HRE;
    try rewrite Int.signed_repr in HRE by rep_omega;
    simple apply andp_left2;
    simple eapply revert_Prop;
      only 1 : exact HRE;
    simple apply derives_refl
  end.

Ltac normalizeE_typed_test :=
  let Post_name := fresh "Post" in
  evar (Post_name : assert);
  match goal with
  | |- ENTAIL _, _ |-- ?Post =>
    unify Post Post_name
  end;
  fold Post_name;
  repeat_Intros;
  simple eapply ENTAIL_trans; [
    normalize_typed_test
  | entail_evar_post
  ].

Ltac normalizeM_typed_test :=
  autorewrite with remove_FF_precondition;
  repeat rewrite distrib_orp_andp;
  repeat apply orp_derives;
  normalizeE_typed_test.

Ltac forwardM_cond :=
  simple eapply semax_pre;
  only 1 : normalizeM_typed_test.

Lemma semax_ifthenelse' : forall {CS : compspecs} {Espec : OracleKind},
  forall Delta (P : assert) b c d R,
    bool_type (typeof b) = true ->
    ENTAIL Delta, P |-- tc_expr Delta (Eunop Onotbool b tint) ->
    semax Delta (P && local (liftx (typed_true (typeof b)) (eval_expr b))) c R ->
    semax Delta (P && local (liftx (typed_false (typeof b)) (eval_expr b))) d R ->
    semax Delta P (Sifthenelse b c d) R.
Proof.
  intros.
  eapply semax_pre.
    2 : apply semax_ifthenelse; eassumption.
  apply andp_right; auto.
Qed.


Ltac forwardM_if :=
  autorewrite with remove_FF_precondition;
  repeat apply -> seq_assoc;
  lazymatch goal with
  | |- semax _ _ (Sifthenelse _ _ _) _ =>
    idtac
  | |- semax _ _ (Ssequence (Sifthenelse _ _ _) _) _ =>
    semax_seq_evar
  end;
  only 1 : (
    simple apply semax_ifthenelse'; [
      reflexivity
    | entailer
    | forwardM_cond
    | forwardM_cond
    ]
  ).

Ltac forward := forwardM.
Ltac forward_if := forwardM_if.
