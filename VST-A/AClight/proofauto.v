Require Export VST.floyd.proofauto.
Require Export AClight.AClight.
Require AClight.advanced_cancel.

(******************** applying Clight-A proof rules ***************************)

(* annotation_apply -> only effects annotation *)
(* apply -> applys proof rule *)

Lemma annotation_apply_dummyassert: forall Q s P,
  (let d := @abbreviate _ s in P) ->
  let d := @abbreviate _ (Ssequence (Sdummyassert Q) s) in P.
Proof.
  intros. assumption.
Qed.

Lemma annotation_apply_seqAssign: forall P s1 s2,
  (let d := @abbreviate _ s2 in P) ->
  (let d := @abbreviate _ (Ssequence s1 s2) in P).
Proof.
  intros. assumption.
Qed.

Lemma apply_seqAssertion:
  forall {Espec: OracleKind} {cs: compspecs},
    forall P' d1 Delta P c Post,
      ENTAIL Delta, P |-- P' ->
      (let d := @abbreviate _ d1 in semax Delta P' c Post) ->
      (let d := @abbreviate _ (Ssequence (Sassert P') d1) in semax Delta P c Post).
Proof.
  intros.
  eapply semax_pre.
  + exact H.
  + exact H0.
Qed.

Lemma apply_seqComplex:
  forall {Espec: OracleKind} {cs: compspecs},
    forall Q s1 s2 Delta P c1 c2 Post,
      (let d := @abbreviate _ (Ssequence s1 Sskip) in semax Delta P c1 (overridePost Q Post)) ->
      (let d := @abbreviate _ s2 in semax Delta Q c2 Post) ->
      (let d := @abbreviate _ (Ssequence s1 (Ssequence (Sassert Q) s2)) in semax Delta P (Clight.Ssequence c1 c2) Post).
Proof.
  intros. eapply semax_seq.
  + exact H.
  + exact H0.
Qed.

Lemma apply_seq:
  forall {Espec: OracleKind} {cs: compspecs},
    forall Q s1 s2 Delta P c1 c2 Post,
      (let d := @abbreviate _ (Ssequence s1 Sskip) in semax Delta P c1 (overridePost Q Post)) ->
      (let d := @abbreviate _ s2 in semax Delta Q c2 Post) ->
      (let d := @abbreviate _ (Ssequence s1 s2) in semax Delta P (Clight.Ssequence c1 c2) Post).
Proof.
  intros. eapply semax_seq.
  + exact H.
  + exact H0.
Qed.

Lemma annotation_apply_if_then:
  forall e d1 d2 d3 (P: Prop),
    (let d := @abbreviate _ d1 in P) ->
    (let d := @abbreviate _ (Ssequence (Sifthenelse e d1 d2) d3) in P).
Proof.
  intros.
  exact H.
Qed.

Lemma annotation_apply_if_else:
  forall e d1 d2 d3 (P: Prop),
    (let d := @abbreviate _ d2 in P) ->
    (let d := @abbreviate _ (Ssequence (Sifthenelse e d1 d2) d3) in P).
Proof.
  intros.
  exact H.
Qed.

Lemma annotation_apply_loop_body:
  forall {Espec: OracleKind} {cs: compspecs},
    forall d1 Inv d2 d3 Delta P c Post,
      (let d := @abbreviate _ d1 in semax Delta P c Post) ->
      (let d := @abbreviate _ (Ssequence (Sloop Inv d1 d2) d3) in semax Delta P c Post).
Proof.
  intros.
  exact H.
Qed.

Lemma annotation_apply_loop_incr:
  forall {Espec: OracleKind} {cs: compspecs},
    forall d1 Inv d2 d3 Delta P c Post,
      (let d := @abbreviate _ d2 in semax Delta P c Post) ->
      (let d := @abbreviate _ (Ssequence (Sloop Inv d1 d2) d3) in semax Delta P c Post).
Proof.
  intros.
  exact H.
Qed.

Lemma apply_given:
  forall {Espec: OracleKind} {cs: compspecs},
    forall {A: Type} d1 Delta P c Post,
      (forall a, let d := @abbreviate _ (d1 a) in semax Delta (P a) c Post) ->
      (let d := @abbreviate _ (Sgiven A d1) in semax Delta (exp P) c Post).
Proof.
  intros.
  Intros a.
  apply H.
Qed.

Lemma annotation_apply_given':
    forall {A: Type} a d1 (P : Prop),
      (let d := @abbreviate _ (d1 a) in P) ->
      (let d := @abbreviate _ (Sgiven A d1) in P).
Proof.
  intros.
  apply H.
Qed.

Ltac apply_dummyassert :=
  match goal with
  | |- let d := @abbreviate _ (Ssequence (Sdummyassert _) _) in _ =>
    refine (annotation_apply_dummyassert _ _ _ _)
  end.

Ltac use_annotation hint :=
  match goal with
  | |- ?P => let d1 := eval hnf in hint in
             change (let d := @abbreviate _ d1 in P)
  end;
  cbv delta [Swhile].

Ltac specialize_annotation d x :=
  revert d;
  match goal with
  | |- let d := @abbreviate _ (Sgiven _ (fun (y:?T) => ?d1)) in _ =>
    refine (annotation_apply_given' x _ _ _)
  end; intro d.

Ltac destruct_and_bind_annotation d :=
  lazymatch goal with
  | |- @semax _ _ _ (match ?p with (a,b) => _ end * _) _ _ =>
    destruct p as [a b];
    lazymatch goal with
    | |- @semax _ _ _ (match ?p with (a,b) => _ end * _) _ _ =>
      destruct_and_bind_annotation d;
      specialize_annotation d b
    | _ =>
      specialize_annotation d a;
      specialize_annotation d b
    end
  end.

Ltac start_function hint :=
  let d := fresh "d" in
  let hint := eval hnf in hint in
  pose (d := @abbreviate statement hint);
  leaf_function;
  match goal with |- semax_body _ _ ?F ?spec =>
    let D := constr:(Clight.type_of_function F) in
    let S := constr:(type_of_funspec (snd spec)) in
    let D := eval hnf in D in let D := eval simpl in D in 
    let S := eval hnf in S in let S := eval simpl in S in 
    tryif (unify D S) then idtac else
    tryif function_types_compatible D S 
    then idtac "Warning: the function-body parameter/return types are not identical to the funspec types, although they are compatible:
Function body:" D "
Function spec:" S
    else
   (fail "Function signature (param types, return type) from function-body does not match function signature from funspec
Function body: " D "
Function spec: " S);
    check_normalized F
  end;
  match goal with |- semax_body ?V ?G ?F ?spec =>
    let s := fresh "spec" in
    pose (s:=spec); hnf in s;
    match goal with
    | s :=  (DECLARE _ WITH _: globals
               PRE  [] main_pre _ nil _
               POST [ tint ] _) |- _ => idtac
    | s := ?spec' |- _ => check_canonical_funspec spec'
    end;
    change (semax_body V G F s); subst s
  end;
  let DependedTypeList := fresh "DependedTypeList" in
  match goal with |- semax_body _ _ _ (pair _ (NDmk_funspec _ _ _ ?Pre _)) =>
    match Pre with
    | (fun x => match _ with (a,b) => _ end) => intros Espec DependedTypeList x
    | (fun i => _) => intros Espec DependedTypeList i; specialize_annotation d i
    end;
    simpl Clight.fn_body; simpl Clight.fn_params; simpl Clight.fn_return
  end;
  simpl functors.MixVariantFunctor._functor in *;
  simpl rmaps.dependent_type_functor_rec;
  clear DependedTypeList;
  lazymatch goal with
  | |- @semax _ _ _ (match ?p with (a,b) => _ end * _) _ _ =>
      destruct_and_bind_annotation d
  | _ => idtac
  end;
  simplify_func_tycontext;
  try expand_main_pre;
  process_stackframe_of;
  repeat change_mapsto_gvar_to_data_at;  (* should really restrict this to only in main,
                                  but it needs to come after process_stackframe_of *)
  repeat rewrite <- data_at__offset_zero;
  try apply start_function_aux1;
  repeat (apply semax_extract_PROP;
              match goal with
              | |- _ ?sh -> _ =>
                 match type of sh with
                 | share => intros ?SH
                 | Share.t => intros ?SH
                 | _ => intro
                 end
               | |- _ => intro
               end);
  first [ eapply eliminate_extra_return'; [ reflexivity | reflexivity | ]
        | eapply eliminate_extra_return; [ reflexivity | reflexivity | ]
        | idtac];
  abbreviate_semax;
  lazymatch goal with 
  | |- semax ?Delta (PROPx _ (LOCALx ?L _)) _ _ => check_parameter_vals Delta L
  | _ => idtac
  end;
  try match goal with DS := @abbreviate (PTree.t funspec) PTree.Leaf |- _ =>
     clearbody DS
  end;
  start_function_hint;
  unfold Clight.Swhile, Sfor in *;
  revert d.

Ltac old_assert_PROP P :=
  assert_PROP P.

Ltac assert_prop P :=
  lazymatch goal with
  | |- let d := @abbreviate statement _ in _ =>
    let d := fresh d in
    intro d; old_assert_PROP P; only 2: revert d
  | _ => old_assert_PROP P
  end.

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

Local Ltac entail_evar_post :=
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

Local Ltac apply_seqComplex :=
  lazymatch goal with |- let d := @abbreviate _ _ in _ =>
    let d := fresh d in
    intro d; repeat apply -> seq_assoc; revert d;
    first [
      refine (apply_seqComplex _ _ _ _ _ _ _ _ _ _)
    | apply <- semax_seq_skip; refine (apply_seqComplex _ _ _ _ _ _ _ _ _ _)
    ];
    [ intro d; abbreviate_semax; revert d
    | intro d; abbreviate_semax; revert d
    ]
  end.

Local Ltac apply_seq_evar :=
  lazymatch goal with |- let d := @abbreviate _ _ in _ =>
    let d := fresh d in
    let Post_name := fresh "Post" in
    evar (Post_name : assert);
    let Post := Post_name in
    intro d; repeat apply -> seq_assoc; revert d;
    first [
      refine (apply_seq Post _ _ _ _ _ _ _ _ _)
    | apply <- semax_seq_skip; refine (apply_seq Post _ _ _ _ _ _ _ _ _)
    ];
    [ intro d; abbreviate_semax; revert d
    | subst Post; intro d; abbreviate_semax; Intros; revert d
    ]
  end.

Tactic Notation "forwardD" :=
  repeat apply_dummyassert;
  (* Intro Props *)
  lazymatch goal with
  | |- let d := @abbreviate _ _ in _ =>
    let d := fresh d in
    intro d; Intros; revert d
  end;
  lazymatch goal with
  (* given *)
  | |- let d := @abbreviate _ (Sgiven _ (fun x => _)) in _ =>
      refine (apply_given _ _ _ _ _ _);
      first
      [ intro x
      | let old_x := fresh x in rename x into old_x; intro x]
  (* unnamed variable *)
  | |- let d := @abbreviate _ _ in semax _ (EX x:?T, _) _ _ =>
      let d := fresh d in
      intro d;
      first [
        let x := fresh x in Intros x
      | fail 1 "Fail in Intros"
      ];
      revert d
  (* if with postcondition *)
  | |- let d := @abbreviate _ (Ssequence (Sifthenelse _ _ _) (Ssequence (Sassert ?P) _)) in _ =>
      apply_seqComplex
  (* loop with postcondition *)
  | |- let d := @abbreviate _ (Ssequence (Sloop _ _ _) (Ssequence (Sassert ?P) _)) in _ =>
      apply_seqComplex
  (* if *)
  | |- let d := @abbreviate _ (Ssequence (Sifthenelse _ _ _) Sskip) in _ =>
      let d := fresh d in
      intro d; forward_if;
      [ ..
      | revert d; refine (annotation_apply_if_then _ _ _ _ _ _)
      | revert d; refine (annotation_apply_if_else _ _ _ _ _ _)]
  (* loop single inv *)
  | |- let d := @abbreviate _ (Ssequence (Sloop (LISingle ?Inv) _ _) Sskip) in _ =>
      let d := fresh d in
      intro d; forward_loop Inv;
      [ ..
      | revert d; refine (annotation_apply_loop_body _ _ _ _ _ _ _ _ _)]
  (* loop double inv *)
  | |- let d := @abbreviate _ (Ssequence (Sloop (LIDouble ?Inv1 ?Inv2) _ _) Sskip) in _ =>
      let d := fresh d in
      intro d; forward_loop Inv1 continue: Inv2;
      [ ..
      | revert d; refine (annotation_apply_loop_body _ _ _ _ _ _ _ _ _)
      | revert d; refine (annotation_apply_loop_incr _ _ _ _ _ _ _ _ _)]
  (* { *) (* These two rules must come after rules for if and loop *)
  (* if without postcondition *)
  | |- let d := @abbreviate _ (Ssequence (Sifthenelse _ _ _) _) in _ =>
      apply_seq_evar
  (* loop  without postcondition *)
  | |- let d := @abbreviate _ (Ssequence (Sloop _ _ _) _) in _ =>
      apply_seq_evar
  (* } *)
  (* assert *)
  | |- let d := @abbreviate _ (Ssequence (Sassert ?P) _) in
       semax _ _ _ _ =>
      refine (apply_seqAssertion P _ _ _ _ _ _ _)
  (* sequence *)
  | |- let d := @abbreviate _ (Ssequence _ _) in
       semax _ _ _ _ =>
      let d := fresh d in
      intro d;
      forward;
      revert d;
      refine (annotation_apply_seqAssign _ _ _ _)
  (* skip *)
  | |- let d := @abbreviate _ Sskip in _ =>
      intros _;
      (* skip in annotation may or may not correspond to a skip in program *)
      lazymatch goal with
      | |- semax _ _ Clight.Sskip _ =>
          forward
      | _ =>
          idtac
      end;
      lazymatch goal with
      | |- ENTAIL _, _ |-- ?Post =>
        tryif (assert_succeeds (subst Post; lazymatch goal with |- _ |-- ?Post => is_evar Post end)) then
          entail_evar_post
        else
          idtac
      | |- _ |-- _ => idtac
      | _ => fail "Resulting goal is not an entailment"
      end
  | |- _ =>
      fail "Annotation unsupported by VST-A"
  (*
  | |- let d := @abbreviate _ _ in _ |-- _ =>
      intro d; clear d
  (* entailment *)
  | |- let d := @abbreviate _ _ in ENTAIL _, _ |-- ?Post =>
      intros _;
      (* solve if Post is an evar; otherwise remain for user *)
      tryif (assert_succeeds (subst Post; lazymatch goal with |- _ |-- ?Post => is_evar Post end)) then
        entail_evar_post
      else
        idtac
  | |- let d := @abbreviate _ _ in
       semax _ _ _ _ =>
      intros _;
      forward; abbreviate_semax;
      (* solve if Post is an evar; otherwise leave to user *)
      lazymatch goal with
      | |- ENTAIL _, _ |-- ?Post =>
        tryif (assert_succeeds (subst Post; lazymatch goal with |- _ |-- ?Post => is_evar Post end)) then
          entail_evar_post
        else
          idtac
      | _ => idtac
      end
  *)
  end.

Ltac verify :=
  repeat
  match goal with
  | |- let d := @abbreviate statement _ in _ =>
      forwardD
  end.

Export AClight.advanced_cancel.
