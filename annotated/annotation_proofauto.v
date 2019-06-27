Require Export VST.floyd.proofauto.
Require Export annotated_Clight.

(********** annotation handling lemmas ****************************************)

Lemma decorate_C_skip: forall P,
  P ->
  let d := @abbreviate _ Sskip in P.
Proof.
  intros. assumption.
Qed.

Lemma decorate_C_dummyassert: forall Q s P,
  (let d := @abbreviate _ s in P) ->
  let d := @abbreviate _ (Ssequence (Sdummyassert Q) s) in P.
Proof.
  intros. assumption.
Qed.

Lemma decorate_C_sequence1: forall P s1 s2,
  (let d := @abbreviate _ (Ssequence s1 Sskip) in P) ->
  (let d := @abbreviate _ (Ssequence s1 s2) in P).
Proof.
  intros. assumption.
Qed.

Lemma decorate_C_sequence: forall P s1 s2,
  (let d := @abbreviate _ s2 in P) ->
  (let d := @abbreviate _ (Ssequence s1 s2) in P).
Proof.
  intros. assumption.
Qed.

Lemma decorate_C_step: forall P (s1: statement),
  P ->
  (let d := @abbreviate _ s1 in P).
Proof.
  intros. assumption.
Qed.

Lemma decorate_C_assert:
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

Lemma decorate_C_assert2:
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

Lemma decorate_C_assert3:
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

Lemma decorate_C_if_then:
  forall e d1 d2 d3 (P: Prop),
    (let d := @abbreviate _ d1 in P) ->
    (let d := @abbreviate _ (Ssequence (Sifthenelse e d1 d2) d3) in P).
Proof.
  intros.
  exact H.
Qed.

Lemma decorate_C_if_else:
  forall e d1 d2 d3 (P: Prop),
    (let d := @abbreviate _ d2 in P) ->
    (let d := @abbreviate _ (Ssequence (Sifthenelse e d1 d2) d3) in P).
Proof.
  intros.
  exact H.
Qed.

Lemma decorate_C_if_after:
  forall e d1 d2 d3 (P: Prop),
    (let d := @abbreviate _ d3 in P) ->
    (let d := @abbreviate _ (Ssequence (Sifthenelse e d1 d2) d3) in P).
Proof.
  intros.
  exact H.
Qed.

Lemma decorate_C_while_body:
  forall {Espec: OracleKind} {cs: compspecs},
    forall b d1 Inv d2 Delta P c Post,
      (let d := @abbreviate _ d1 in semax Delta P c Post) ->
      (let d := @abbreviate _ (Ssequence (Swhile Inv b d1) d2) in semax Delta P c Post).
Proof.
  intros.
  exact H.
Qed.

Lemma decorate_C_while_after:
  forall {Espec: OracleKind} {cs: compspecs},
    forall b d1 Inv d2 Delta P c Post,
      (let d := @abbreviate _ d2 in semax Delta P c Post) ->
      (let d := @abbreviate _ (Ssequence (Swhile Inv b d1) d2) in semax Delta P c Post).
Proof.
  intros.
  exact H.
Qed.

Lemma decorate_C_loop_body:
  forall {Espec: OracleKind} {cs: compspecs},
    forall d1 Inv d2 d3 Delta P c Post,
      (let d := @abbreviate _ d1 in semax Delta P c Post) ->
      (let d := @abbreviate _ (Ssequence (Sloop Inv d1 d2) d3) in semax Delta P c Post).
Proof.
  intros.
  exact H.
Qed.

Lemma decorate_C_loop_incr:
  forall {Espec: OracleKind} {cs: compspecs},
    forall d1 Inv d2 d3 Delta P c Post,
      (let d := @abbreviate _ d2 in semax Delta P c Post) ->
      (let d := @abbreviate _ (Ssequence (Sloop Inv d1 d2) d3) in semax Delta P c Post).
Proof.
  intros.
  exact H.
Qed.

Ltac fill_decorate_C_loop_after d1 d3 :=
  match d1 with
  | Sbreak => refine d3
  | Ssequence ?d1 ?d2 =>
      first [fill_decorate_C_loop_after d1 d3 | fill_decorate_C_loop_after d2 d3]
  | Sgiven ?A ?d1 =>
    match d1 with
    | (fun x => _) =>
        refine (Sgiven2 A _); first [intro x | let x1 := fresh x in rename x into x1; intro x];
        let d2 := eval cbv beta in (d1 x) in fill_decorate_C_loop_after d2 d3
    end
  | Sifthenelse _ ?d1 ?d2 =>
      first [fill_decorate_C_loop_after d1 d3 | fill_decorate_C_loop_after d2 d3]
  | _ => fail
  end.

Ltac fill_decorate_C_loop_after2 :=
  match goal with
  | d := @abbreviate _ (Ssequence (Sloop _ ?d1 ?d2) ?d3) |- _ =>
      fill_decorate_C_loop_after d1 d3
  end.

Lemma decorate_C_loop_after:
  forall {Espec: OracleKind} {cs: compspecs},
    forall (d1 d2: statement) Delta P c Post,
      (let d := @abbreviate _ d1 in semax Delta P c Post) ->
      (let d := @abbreviate _ d2 in semax Delta P c Post).
Proof.
  intros.
  exact H.
Qed.

Definition Intro_tag {A} (x : A) := True.

Lemma decorate_C_given:
  forall {Espec: OracleKind} {cs: compspecs},
    forall {A: Type} d1 Delta P c Post,
      (forall a, Intro_tag a -> let d := @abbreviate _ (d1 a) in semax Delta (P a) c Post) ->
      (let d := @abbreviate _ (Sgiven A d1) in semax Delta (exp P) c Post).
Proof.
  intros.
  Intros a.
  apply H. apply I.
Qed.

Lemma decorate_C_given2:
  forall {Espec: OracleKind} {cs: compspecs},
    forall {A: Type} d1 Delta P c Post,
      (forall a, Intro_tag a -> let d := @abbreviate _ (d1 a) in semax Delta (P a) c Post) ->
      (let d := @abbreviate _ (Sgiven2 A d1) in semax Delta (exp P) c Post).
Proof.
  intros.
  Intros a.
  apply H. apply I.
Qed.

Lemma decorate_C_given':
    forall {A: Type} a d1 (P : Prop),
      (let d := @abbreviate _ (d1 a) in P) ->
      (let d := @abbreviate _ (Sgiven A d1) in P).
Proof.
  intros.
  apply H.
Qed.

Ltac ignore_dummyassert :=
  match goal with
  | |- let d := @abbreviate _ (Ssequence (Sdummyassert _) _) in _ =>
    refine (decorate_C_dummyassert _ _ _ _)
  end.

Lemma delta_derives_refl:
  forall Delta P,
    ENTAIL Delta, P |-- P.
Proof.
  intros. apply andp_left2. apply derives_refl.
Qed.

Lemma delta_derives_refl_and_Props:
  forall Delta P Q R,
    fold_right and True P ->
    ENTAIL Delta, PROPx nil (LOCALx Q (SEPx R)) |-- PROPx P (LOCALx Q (SEPx R)).
Proof.
  intros. apply andp_left2.
  unfold PROPx. apply andp_left2.
  apply andp_right.
  + apply prop_right. assumption.
  + apply derives_refl.
Qed.

Lemma fold_right_and_app_iff_and: forall Pl Ql,
  fold_right and True (Pl ++ Ql) <-> fold_right and True Pl /\ fold_right and True Ql.
Proof.
  intros. induction Pl; simpl; tauto.
Qed.

(* Create a exclusive local definition. *)
Local Definition rev {A} := @rev A.

Lemma fold_right_and_rev_iff: forall Pl,
  fold_right and True (rev Pl) <-> fold_right and True Pl.
Proof.
  intros. induction Pl; simpl.
  + tauto.
  + rewrite fold_right_and_app_iff_and. simpl. tauto.
Qed.

Lemma fold_right_and_rev_extract: forall (P: Prop) Pl,
  P -> fold_right and True (rev Pl) -> fold_right and True (rev (P :: Pl)).
Proof.
  intros *. do 2 rewrite fold_right_and_rev_iff. simpl. auto.
Qed.

Lemma fold_right_and_rev_nil:
  fold_right and True (rev nil).
Proof.
  simpl. auto.
Qed.

Definition Post_infer_tag := True.

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
    refine (decorate_C_given' x _ _ _)
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
  revert d;
  repeat ignore_dummyassert.

Ltac old_assert_PROP P :=
  assert_PROP P.

Ltac assert_prop P :=
  lazymatch goal with
  | |- let d := @abbreviate statement _ in _ =>
    intro d; old_assert_PROP P; only 2: revert d
  | _ => old_assert_PROP P
  end.

Local Ltac clear_all_Intro_tag :=
  repeat match goal with
  | H : Intro_tag _ |- _ => clear H
  end.

Local Ltac entail_evar_post :=
  repeat match reverse goal with
  | H : Intro_tag ?x |- _ =>
    clear H;
    Exists x;
    (* we prefer to use (fun x => _), but x is a term instead of an ident, so we cannot find
     * its name. *)
    instantiate (1 := (fun xx => _)); cbv beta
  end;
  eapply delta_derives_refl_and_Props;
  repeat lazymatch goal with
  | H : _ |- _ =>
    lazymatch type of H with
    | Post_infer_tag =>
        apply fold_right_and_rev_nil
    | ?P =>
        match type of P with
        | Prop =>
            eapply fold_right_and_rev_extract;
            only 1: apply H;
            clear H
        | _ => clear H
        end
    end
  end.

Local Ltac assert_postcondition :=
  lazymatch goal with |- let d := @abbreviate _ _ in _ =>
    intro d; repeat apply -> seq_assoc; revert d;
    first [
      refine (decorate_C_assert2 _ _ _ _ _ _ _ _ _ _)
    | apply <- semax_seq_skip; refine (decorate_C_assert2 _ _ _ _ _ _ _ _ _ _)
    ];
    [ intro d; abbreviate_semax; revert d
    | intro d; abbreviate_semax; revert d
    ]
  end.

Local Ltac assert_evar_postcondition :=
  lazymatch goal with |- let d := @abbreviate _ _ in _ =>
    let Post_name := fresh "Post" in
    evar (Post_name : assert);
    let Post := eval unfold Post_name in Post_name in
    clear Post_name;
    intro d; repeat apply -> seq_assoc; revert d;
    first [
      refine (decorate_C_assert3 Post _ _ _ _ _ _ _ _ _)
    | apply <- semax_seq_skip; refine (decorate_C_assert3 Post _ _ _ _ _ _ _ _ _)
    ];
    [ intro d; abbreviate_semax; revert d;
      clear_all_Intro_tag;
      assert Post_infer_tag by (exact I)
    | intro d; abbreviate_semax; revert d
    ]
  end.

Tactic Notation "forwardD" :=
  simpl rev;
  lazymatch goal with
  (* entailment *)
  | |- let d := @abbreviate _ _ in ENTAIL _, _ |-- ?Post =>
      intro d; clear d;
      (* solve if Post is an evar; otherwise remain for user *)
      tryif is_evar Post then
        entail_evar_post
      else
        idtac
  | |- let d := @abbreviate _ _ in _ |-- _ =>
      intro d; clear d
  (* dummyassert *)
  | |- let d := @abbreviate _ (Ssequence (Sdummyassert _) _) in _ =>
      refine (decorate_C_dummyassert _ _ _ _)
  (* if with postcondition *)
  | |- let d := @abbreviate _ (Ssequence (Sifthenelse _ _ _) (Ssequence (Sassert ?P) _)) in _ =>
      assert_postcondition
  (* if *)
  | |- let d := @abbreviate _ (Ssequence (Sifthenelse _ _ _) Sskip) in _ =>
      intro d; forward_if;
      [ ..
      | revert d; refine (decorate_C_if_then _ _ _ _ _ _)
      | revert d; refine (decorate_C_if_else _ _ _ _ _ _)]
  (* if without postcondition *)
  | |- let d := @abbreviate _ (Ssequence (Sifthenelse _ _ _) _) in _ =>
      assert_evar_postcondition
  (* while case is included in loop *)
  (* | |- let d := @abbreviate _ (Ssequence (Swhile ?Inv _ _) _) in
       (* semax _ _ (Clight.Ssequence (Clight.Swhile _ _) _) _ => *)
       _ =>
      intro d; forward_while Inv;
      [ ..
      | revert d; refine (decorate_C_while_body _ _ _ _ _ _ _ _ _)
      | revert d; refine (decorate_C_while_after _ _ _ _ _ _ _ _ _)] *)
  (* loop with postcondition *)
  | |- let d := @abbreviate _ (Ssequence (Sloop _ _ _) (Ssequence (Sassert ?P) _)) in _ =>
      assert_postcondition
  (* loop single inv *)
  | |- let d := @abbreviate _ (Ssequence (Sloop (LISingle ?Inv) _ _) Sskip) in _ =>
      intro d; forward_loop Inv;
      [ ..
      | revert d; refine (decorate_C_loop_body _ _ _ _ _ _ _ _ _)]
  (* loop double inv *)
  | |- let d := @abbreviate _ (Ssequence (Sloop (LIDouble ?Inv1 ?Inv2) _ _) Sskip) in _ =>
      intro d; forward_loop Inv1 continue: Inv2;
      [ ..
      | revert d; refine (decorate_C_loop_body _ _ _ _ _ _ _ _ _)
      | revert d; refine (decorate_C_loop_incr _ _ _ _ _ _ _ _ _)]
  (* loop  without postcondition *)
  | |- let d := @abbreviate _ (Ssequence (Sloop _ _ _) _) in _ =>
      let Post_name := fresh "Post" in
      evar (Post_name : assert);
      let Post := eval unfold Post_name in Post_name in
      clear Post_name;
      intro d; repeat apply -> seq_assoc; revert d;
      intro d; apply semax_seq with Post;
      [ abbreviate_semax; revert d;
        refine (decorate_C_sequence1 _ _ _ _);
        clear_all_Intro_tag;
        assert Post_infer_tag by (exact I)
      | abbreviate_semax;
        let d1 := fresh "d" in
        set (d1 := ltac: (fill_decorate_C_loop_after2));
        revert d;
        refine (decorate_C_loop_after d1 _ _ _ _ _ _); subst d1
      ]
  (* given *)
  | |- let d := @abbreviate _ (Sgiven _ (fun x => _)) in _ =>
      refine (decorate_C_given _ _ _ _ _ _);
      first
      [ intro x
      | let old_x := fresh x in rename x into old_x; intro x];
      intros ? d;
      Intros;
      revert d
      ;repeat ignore_dummyassert
  | |- let d := @abbreviate _ (Sgiven2 _ (fun x => _)) in _ =>
      refine (decorate_C_given2 _ _ _ _ _ _);
      let xx := fresh x in
      intro xx;
      intros ? d;
      Intros;
      revert d
  (* assert *)
  | |- let d := @abbreviate _ (Ssequence (Sassert ?P) _) in
       semax _ _ _ _ =>
      refine (decorate_C_assert P _ _ _ _ _ _ _)
  | |- let d := @abbreviate _ (Ssequence _ _) in
       semax _ _ (Clight.Ssequence _ _) _ =>
      intro d;
      forward;
      revert d;
      refine (decorate_C_sequence _ _ _ _)
  | |- let d := @abbreviate _ _ in
       semax _ _ _ _ =>
      intro d;
      forward;
      (* solve if Post is an evar; otherwise remain for user *)
      try lazymatch goal with |- ENTAIL _, _ |-- ?Post =>
        tryif is_evar Post then
          entail_evar_post
        else
          idtac
      end
  end.

Tactic Notation "forwardD" constr(a) :=
  lazymatch goal with
  | |- let d := @abbreviate _ (Sgiven _ (fun (x:?T) => _)) in
       semax _ _ _ _ =>
      first
      [ ignore (a : T)
      | fail 1 a "must have type" T
      ];
      refine (decorate_C_given' a _ _ _)
  end.
