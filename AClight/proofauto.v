Require Export VST.floyd.proofauto.
Require Export AClight.AClight.
Require Export AClight.advanced_cancel.
Require Export AClight.revert.
Require Export AClight.advanced_forward.
Require Export AClight.ramification.
Require Export AClight.localization.
Require Export AClight.semax_ram_lemmas.

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

Lemma apply_impAssertion:
    forall P' d1 Delta P Q,
      ENTAIL Delta, P |-- P' ->
      (let d := @abbreviate _ d1 in ENTAIL Delta, P' |-- Q) ->
      (let d := @abbreviate _ (Ssequence (Sassert P') d1) in ENTAIL Delta, P |-- Q).
Proof.
  intros.
  eapply ENTAIL_trans.
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

Lemma annotation_apply_if_after:
  forall e d1 d2 d3 (P: Prop),
    (let d := @abbreviate _ d3 in P) ->
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

Lemma annotation_apply_loop_after:
  forall {Espec: OracleKind} {cs: compspecs},
    forall d1 Inv d2 d3 Delta P c Post,
      (let d := @abbreviate _ d3 in semax Delta P c Post) ->
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

Lemma apply_impGiven:
  forall {A: Type} d1 Delta P Q,
    (forall a, let d := @abbreviate _ (d1 a) in ENTAIL Delta, (P a) |-- Q) ->
    (let d := @abbreviate _ (Sgiven A d1) in ENTAIL Delta, (exp P) |-- Q).
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

Local Opaque FF.

Lemma FF_ENTAIL:
  forall Delta Q,
    ENTAIL Delta, FF |-- Q.
Proof.
  intros. rewrite andp_FF. apply FF_left.
Qed.

Hint Resolve FF_ENTAIL : core.

Lemma apply_localize:
  forall {Espec: OracleKind} {cs: compspecs},
    forall Delta G L L' G' G'brk G'con G'ret snum s c,
      (let d := @abbreviate _ s in semax Delta L c (normal_ret_assert L')) ->
      (ENTAIL Delta, G |-- L * ramification.ModBox c (local (tc_environ Delta) --> (L' -* G'))) ->
      (let d := @abbreviate _ (Ssequence (Slocal L snum s G') Sskip) in semax Delta G c
      {| RA_normal := G';
         RA_break := G'brk;
         RA_continue := G'con;
         RA_return := G'ret |}).
Proof.
  intros.
  apply semax_post with (normal_ret_assert G').
  { simpl RA_normal; auto. }
  { simpl RA_break; auto. }
  { simpl RA_continue; auto. }
  { simpl RA_return; auto. }
  eapply ramification.semax_ramification_P'; eauto.
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
  | |- @semax _ _ _ (Clight_seplog.close_precondition _ _ match ?p with (a,b) => _ end * _) _ _ =>
    destruct p as [a b];
    lazymatch goal with
    | |- @semax _ _ _ (Clight_seplog.close_precondition _ _ match ?p with (a,b) => _ end * _) _ _ =>
      destruct_and_bind_annotation d;
      specialize_annotation d b
    | _ =>
      specialize_annotation d a;
      specialize_annotation d b
    end
  | |- @semax _ _ _ ((match ?p with (a,b) => _ end) eq_refl * _) _ _ =>
    destruct p as [a b];
    lazymatch goal with
    | |- @semax _ _ _ ((match ?p with (a,b) => _ end) eq_refl * _) _ _ =>
      destruct_and_bind_annotation d;
      specialize_annotation d b
    | _ =>
      specialize_annotation d a;
      specialize_annotation d b
    end
  | |- @semax _ _ _ (Clight_seplog.close_precondition _ _ ((match ?p with (a,b) => _ end) eq_refl) * _) _ _ =>
    destruct p as [a b];
    lazymatch goal with
    | |- @semax _ _ _ (Clight_seplog.close_precondition _ _ ((match ?p with (a,b) => _ end) eq_refl) * _) _ _ =>
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
 match goal with |- semax_body ?V ?G ?F ?spec =>
    check_normalized F;
    let s := fresh "spec" in
    pose (s:=spec); hnf in s; cbn zeta in s; (* dependent specs defined with Program Definition often have extra lets *)
   repeat lazymatch goal with
    | s := (_, NDmk_funspec _ _ _ _ _) |- _ => fail
    | s := (_, mk_funspec _ _ _ _ _ _ _) |- _ => fail
    | s := (_, ?a _ _ _ _) |- _ => unfold a in s
    | s := (_, ?a _ _ _) |- _ => unfold a in s
    | s := (_, ?a _ _) |- _ => unfold a in s
    | s := (_, ?a _) |- _ => unfold a in s
    | s := (_, ?a) |- _ => unfold a in s
    end;
    lazymatch goal with
    | s :=  (_,  WITH _: globals
               PRE  [] main_pre _ nil _
               POST [ tint ] _) |- _ => idtac
    | s := ?spec' |- _ => check_canonical_funspec spec'
   end;
   change (semax_body V G F s); subst s
 end;
 let DependedTypeList := fresh "DependedTypeList" in
 unfold NDmk_funspec;
 match goal with |- semax_body _ _ _ (pair _ (mk_funspec _ _ _ ?Pre _ _ _)) =>
   split; [split3; [check_parameter_types' | check_return_type
          | try (apply compute_list_norepet_e; reflexivity);
             fail "Duplicate formal parameter names in funspec signature"  ]
         |];
   simpl functors.MixVariantFunctor._functor in *;
   match Pre with
   | (fun _ x => match _ with (a,b) => _ end) => intros Espec DependedTypeList x (* preventing destructing too early and losing track of WITH-variables *)
   | (fun _ i => _) => intros Espec DependedTypeList i; specialize_annotation d i
   end;
   simpl Clight.fn_body; simpl Clight.fn_params; simpl Clight.fn_return
 end;
 try match goal with |- semax _ (fun rho => ?A rho * ?B rho) _ _ =>
     change (fun rho => ?A rho * ?B rho) with (A * B)
  end;
 simpl functors.MixVariantFunctor._functor in *;
 simpl rmaps.dependent_type_functor_rec;
 clear DependedTypeList;
 repeat match goal with
 | |- @semax _ _ _ (match ?p with (a,b) => _ end * _) _ _ =>
   destruct_and_bind_annotation d
 | |- @semax _ _ _ (Clight_seplog.close_precondition _ _ match ?p with (a,b) => _ end * _) _ _ =>
   destruct_and_bind_annotation d
 | |- @semax _ _ _ ((match ?p with (a,b) => _ end) eq_refl * _) _ _ =>
   destruct_and_bind_annotation d
 | |- @semax _ _ _ (Clight_seplog.close_precondition _ _ ((match ?p with (a,b) => _ end) eq_refl) * _) _ _ =>
   destruct_and_bind_annotation d
 | _ => idtac
 end;
 first [apply elim_close_precondition; [solve [auto 50 with closed] | solve [auto 50 with closed] | ]
        | erewrite compute_close_precondition by reflexivity];
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
(*
 first [ eapply eliminate_extra_return'; [ reflexivity | reflexivity | ]
        | eapply eliminate_extra_return; [ reflexivity | reflexivity | ]
        | idtac];
*)
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

(*Local*) Ltac apply_seqComplex :=
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

(*Local*) Ltac apply_seq_evar :=
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

Ltac apply_localize :=
  lazymatch goal with |- let d := @abbreviate _ _ in _ =>
    let d := fresh d in
    let L'_name := fresh "L'" in
    evar (L'_name : assert);
    let L' := L'_name in
    refine (apply_localize _ _ _ L' _ _ _ _ _ _ _ _ _);
    [ intro d; abbreviate_semax; revert d
    | subst L'
    ]
  end.

(* Lemma localize:
  forall {Espec: OracleKind} {cs: compspecs},
    forall Delta G L c L' G',
      semax Delta L c L' ->
      G |-- L * (L' -* G') ->
      semax Delta G c G'.
      (forall a, let d := @abbreviate _ (d1 a) in semax Delta (P a) c Post) ->
      (let d := @abbreviate _ (Sgiven A d1) in semax Delta (exp P) c Post).
 *)
(* Lemma apply_localize:
  forall {Espec: OracleKind} {cs: compspecs},
    forall {A: Type} d1 Delta P c Post,
      (forall a, let d := @abbreviate _ (d1 a) in semax Delta (P a) c Post) ->
      (let d := @abbreviate _ (Sgiven A d1) in semax Delta (exp P) c Post). *)

Ltac forwardD :=
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
      lazymatch goal with
      | |- let d := _ in semax _ _ _ _ =>
        refine (apply_given _ _ _ _ _ _)
      | |- let d := _ in ENTAIL _, _ |-- _ =>
        refine (apply_impGiven _ _ _ _ _)
      | _ =>
        fail "no matching pattern when processing Sgiven"
      end;
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
  (* | |- let d := @abbreviate _ (Ssequence (Sifthenelse _ _ _) (Ssequence (Sassert ?P) _)) in _ =>
      let d := fresh d in
      intro d; forwardM_if;
      [ ..
      | revert d; refine (annotation_apply_if_then _ _ _ _ _ _)
      | revert d; refine (annotation_apply_if_else _ _ _ _ _ _)] *)
  (* loop with postcondition *)
  (* | |- let d := @abbreviate _ (Ssequence (Sloop _ _ _) (Ssequence (Sassert ?P) _)) in _ =>
      apply_seqComplex *)
  (* if *)
  | |- let d := @abbreviate _ (Ssequence (Sifthenelse _ _ _) Sskip) in _ =>
      let d := fresh d in
      intro d;
      (* remove trailing Sskip introduced by loop_nocontinue *)
      unfold_abbrev'; try apply -> semax_seq_skip;
      forwardM_if;
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
      let d := fresh d in
      intro d; forwardM_if;
      [ ..
      | revert d; refine (annotation_apply_if_then _ _ _ _ _ _)
      | revert d; refine (annotation_apply_if_else _ _ _ _ _ _)
      | revert d; refine (annotation_apply_if_after _ _ _ _ _ _)]
  (* loop  without postcondition *)
  | |- let d := @abbreviate _ (Ssequence (Sloop _ _ _) _) in _ =>
      apply_seq_evar
  (* } *)
  (* assert *)
  | |- let d := @abbreviate _ (Ssequence (Sassert ?P) _) in _ =>
      lazymatch goal with
      | |- let d := _ in semax _ _ _ _ =>
        refine (apply_seqAssertion _ _ _ _ _ _ _ _);
        [ remove_FF_precondition;
          repeat apply ENTAIL_orp_left
        | ]
      | |- let d := _ in ENTAIL _, _ |-- _ =>
        refine (apply_impAssertion _ _ _ _ _ _ _);
        [ remove_FF_precondition;
          repeat apply ENTAIL_orp_left
        | ]
      | _ =>
        fail "no matching pattern when processing Sassert"
      end
  (* localize *)
  | |- let d := @abbreviate _ (Ssequence (Slocal ?L ?snum ?c ?G') Sskip) in _ =>
      let d := fresh d in
      intro d;
      apply <- semax_seq_skip;
      revert d;
      refine (apply_seq G' _ _ _ _ _ _ _ _ _);
      only 1: apply_localize
  | |- let d := @abbreviate _ (Ssequence (Slocal ?L ?snum ?c ?G') _) in _ =>
      let d := fresh d in
      intro d;
      split_semax_statement snum;
      revert d;
      refine (apply_seq G' _ _ _ _ _ _ _ _ _);
      only 1: apply_localize
  (* sequence call *)
  | |- let d := @abbreviate _ (Ssequence (Scall _ _ _) _) in
       semax _ _ _ _ =>
      let d := fresh d in
      intro d;
      forwardM;
      (* this is still not correct, but better *)
      lazymatch goal with
      | |- semax _ _ _ _ =>
          revert d; refine (annotation_apply_seqAssign _ _ _ _)
      | _ =>
          idtac
      end
  (* sequence *)
  | |- let d := @abbreviate _ (Ssequence _ _) in
       semax _ _ _ _ =>
      let d := fresh d in
      intro d;
      forwardM;
      (* forward may raise side condition. forward may solve the goal as well.
       * This is an ugly solution to accomodate all the cases.
       *)
      try (idtac;
        [.. | revert d; refine (annotation_apply_seqAssign _ _ _ _)]
      )
  (* skip *)
  | |- let d := @abbreviate _ Sskip in _ =>
      intros _;
      (* skip in annotation may or may not correspond to a skip in program *)
      lazymatch goal with
      | |- semax _ _ Clight.Sskip _ =>
          forwardM
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
  end.

Ltac verify :=
  repeat lazymatch goal with
  | |- let d := @abbreviate statement _ in _ =>
      forwardD
  | |- context [ModBox _ _] =>
      simplify_ramif
  end.
