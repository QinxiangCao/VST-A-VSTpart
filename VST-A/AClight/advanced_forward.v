Require Export VST.floyd.proofauto.
(* Require Import AClight.AClight. *)

(* Two layers : (1) intro and revert (2) multi-cond *)

(********************* Part I : intro and revert ***********************)

Lemma derives_add_Prop_left : forall (P0 : Prop) P Q R Post,
  P0 ->
  (PROPx (P0 :: P) (LOCALx Q (SEPx R))) |-- Post ->
  (PROPx P (LOCALx Q (SEPx R))) |-- Post.
Proof.
  intros.
  eapply derives_trans. 2 : apply H0.
  clear H0.
  apply andp_prop_derives.
  - simpl. tauto.
  - auto.
Qed.

Lemma exp_left_revert : forall A (P: A -> environ -> mpred) Q,
  exp P |-- Q -> (forall a, P a |-- Q).
Proof.
  intros.
  eapply derives_trans. 2 : apply  H.
  eapply exp_right. apply derives_refl.
Qed.

(*Local *)  Ltac entail_evar_post :=
  simple apply andp_left2;
  lazymatch goal with
  | |- _ |-- ?Post =>
    repeat match goal with
    | x : ?T |- _ =>
      first [
        assert_fails constr_eq x Post
      | fail 2 (* break *)
      ];
      ignore (T : Prop);
      refine (derives_add_Prop_left _ _ _ _ _ x _);
      clear x
    end;
    repeat match goal with
    | x : ?T |- _ =>
      first [
        assert_fails constr_eq x Post
      | fail 2 (* break *)
      ];
      first [
        subst x
      | revert x;
        refine (exp_left_revert T (fun x => _) _ _)
      | fail 3 "Fail to revert existentail variables"
      ]
    end;
    subst Post;
    apply derives_refl
  end.

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
  | |- semax _ _ (Ssequence (Sbreak _)) _ =>
    repeat_Intros; forward
  | |- semax _ _ (Ssequence (Scontinue _)) _ =>
    repeat_Intros; forward
  | |- semax _ _ (Ssequence ((Sreturn _) _)) _ =>
    repeat_Intros; forward
  | |- semax _ _ (Ssequence _ _) _ =>
    semax_seq_evar; [
      (* first statement *)
      repeat_Intros;
      forward;
      entail_evar_post
    | ]
  | |- semax _ _ _ _ => (* single statement *)
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

Lemma semax_orp_parallel:
  forall {Espec: OracleKind} {cs: compspecs},
    forall Delta P1 P2 c Q1 Q2 Qbrk Qcon Qret,
      semax Delta P1 c (Build_ret_assert Q1 Qbrk Qcon Qret) ->
      semax Delta P2 c (Build_ret_assert Q2 Qbrk Qcon Qret) ->
      semax Delta (orp P1 P2) c (Build_ret_assert (orp Q1 Q2) Qbrk Qcon Qret).
Proof.
  intros.
  apply semax_orp.
  - eapply semax_post1. 2 : eauto.
    change (ENTAIL Delta, Q1 |-- Q1 || Q2).
    apply orp_right1. auto.
  - eapply semax_post1. 2 : eauto.
    change (ENTAIL Delta, Q2 |-- Q1 || Q2).
    apply orp_right2. auto.
Qed.

Ltac forwardM :=
  repeat rewrite orp_FF;
  repeat rewrite FF_orp;
  repeat apply -> seq_assoc;
  lazymatch goal with
  | |- semax _ (orp _ _) (Ssequence _ _) _ =>
    semax_seq_evar; [
      repeat simple eapply semax_orp_parallel;
      forwardE;
      entail_evar_post
    | abbreviate_semax
    ]
  | |- semax _ _ _ _ =>
    repeat simple eapply semax_orp_parallel;
    forwardE
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
    simple eapply derives_add_Prop_left;
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
  repeat rewrite FF_orp;
  repeat rewrite orp_FF;
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
  repeat rewrite orp_FF;
  repeat rewrite FF_orp;
  repeat apply -> seq_assoc;
  lazymatch goal with
  | |- semax _ _ (Sifthenelse _ _ _) _ =>
    idtac
  | |- semax _ _ (Ssequence (Sifthenelse _ _ _)) _ =>
    simple eapply semax_seq
  end;
  only 1 : (
    simple apply semax_ifthenelse'; [
      reflexivity
    | entailer
    | forwardM_cond
    | forwardM_cond
    ]
  ).
