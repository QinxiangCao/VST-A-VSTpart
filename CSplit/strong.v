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
Require Import VST.floyd.SeparationLogicFacts.
Import Ctypes LiftNotation.
Local Open Scope logic.
Require Import Csplit.model_lemmas.
Require Import Csplit.logic_lemmas.

Definition numeric_type (t: type) : bool :=
  match t with
  | Tint IBool _ _ => false
  | Tint _ _ _ => true
  | Tlong _ _ => true
  | Tfloat _ _ => true
  | _ => false
  end.

Definition precise_context (Delta: tycontext) : Prop :=
  forall id fs,
    (glob_specs Delta) ! id = Some fs ->
    precise_funspec Delta fs.

Definition global_block (rho: environ) : ident -> block -> Prop :=
  fun id b =>
    Map.get (ve_of rho) id = None /\
    Map.get (ge_of rho) id = Some b.

Inductive semax {CS: compspecs} {Espec: OracleKind} (Delta: tycontext): (environ -> mpred) -> Clight.statement -> ret_assert -> Prop :=
| semax_ifthenelse :
   forall P (b: expr) c d R,
     @semax CS Espec Delta (P && local (`(typed_true (typeof b)) (eval_expr b))) c R ->
     @semax CS Espec Delta (P && local (`(typed_false (typeof b)) (eval_expr b))) d R ->
     @semax CS Espec Delta (!! (bool_type (typeof b) = true) && tc_expr Delta (Eunop Cop.Onotbool b (Tint I32 Signed noattr)) && P) (Clight.Sifthenelse b c d) R
| semax_seq:
  forall R P Q h t,
    @semax CS Espec Delta P h (overridePost Q R) ->
    @semax CS Espec Delta Q t R ->
    @semax CS Espec Delta P (Clight.Ssequence h t) R
| semax_break: forall Q,
    @semax CS Espec Delta (RA_break Q) Clight.Sbreak Q
| semax_continue: forall Q,
    @semax CS Espec Delta (RA_continue Q) Clight.Scontinue Q
| semax_loop: forall Q Q' incr body R,
     @semax CS Espec Delta Q  body (loop1_ret_assert Q' R) ->
     @semax CS Espec Delta Q' incr (loop2_ret_assert Q R) ->
     @semax CS Espec Delta Q (Clight.Sloop body incr) R
| semax_return: forall (R: ret_assert) ret ,
      @semax CS Espec Delta
                ( (tc_expropt Delta ret (ret_type Delta)) &&
                `(RA_return R : option val -> environ -> mpred) (cast_expropt ret (ret_type Delta)) (@id environ))
                (Clight.Sreturn ret)
                R
| semax_skip: forall P, @semax CS Espec Delta P Clight.Sskip (normal_ret_assert P)
| semax_assign: forall (P: environ->mpred) e1 e2,
  @semax CS Espec Delta
  ((EX sh: share, !! writable_share sh &&
      |> ( (tc_lvalue Delta e1) &&  (tc_expr Delta (Ecast e2 (typeof e1)))  &&
      ((`(mapsto_ sh (typeof e1)) (eval_lvalue e1)) *
       (`(mapsto sh (typeof e1)) (eval_lvalue e1) (`force_val (`(sem_cast (typeof e2) (typeof e1)) (eval_expr e2))) -* P))))
  )
  (Clight.Sassign e1 e2) (normal_ret_assert P)
| semax_set_ptr_compare_load_cast_load_backward: forall (P: environ->mpred) id e,
    @semax CS Espec Delta
       ((|> ( (tc_expr Delta e) &&
             (tc_temp_id id (typeof e) Delta e) &&
             subst id (eval_expr e) P)) ||
        (EX sh: share, EX t2: type, EX v2: val,
              !! (typeof_temp Delta id = Some t2 /\
                  is_neutral_cast (typeof e) t2 = true /\
                  readable_share sh) &&
         |> ( (tc_lvalue Delta e) &&
              local (`(tc_val (typeof e) v2)) &&
              (`(mapsto sh (typeof e)) (eval_lvalue e) (`v2) * TT) &&
              subst id (`v2) P)) ||
        (EX sh: share, EX e1: expr, EX t1: type, EX v2: val,
              !! (e = Ecast e1 t1 /\
                  typeof_temp Delta id = Some t1 /\
                  cast_pointer_to_bool (typeof e1) t1 = false /\
                  readable_share sh) &&
         |> ( (tc_lvalue Delta e1) &&
              local (`(tc_val t1) (`(eval_cast (typeof e1) t1 v2))) &&
              (`(mapsto sh (typeof e1)) (eval_lvalue e1) (`v2) * TT) &&
              subst id (`(force_val (sem_cast (typeof e1) t1 v2))) P)))
        (Clight.Sset id e) (normal_ret_assert P)
| semax_conseq: forall P' (R': ret_assert) P c (R: ret_assert) ,
    local (tc_environ Delta) && (allp_fun_id Delta && P) |-- P' ->
    local (tc_environ Delta) && (allp_fun_id Delta && RA_normal R') |-- RA_normal R ->
    local (tc_environ Delta) && (allp_fun_id Delta && RA_break R') |-- RA_break R ->
    local (tc_environ Delta) && (allp_fun_id Delta && RA_continue R') |-- RA_continue R ->
    (forall vl, local (tc_environ Delta) && (allp_fun_id Delta && RA_return R' vl) |-- RA_return R vl) ->
    @semax CS Espec Delta P' c R' -> @semax CS Espec Delta P c R

| semax_builtin: forall P opt ext tl el, @semax CS Espec Delta FF (Clight.Sbuiltin opt ext tl el) P

| semax_call: forall ret a bl R, (* different from standard VST rule  *)
    @semax CS Espec Delta
      (EX argsig retsig cc A P Q NEP NEQ b id fs,
        !! (Cop.classify_fun (typeof a) =
              Cop.fun_case_f (type_of_params argsig) retsig cc /\ 
            (* type of a must match argsig/retsig *)
            (retsig = Tvoid -> ret = None) /\
            tc_fn_return Delta ret retsig /\ (* return value type check *)
            precise_context Delta /\
            (glob_specs Delta) ! id = Some fs) &&
        ((tc_expr Delta a) && (* function-expression must typecheck *)
         (tc_exprlist Delta (snd (split argsig)) bl)) && (* argument-expressions must typecheck *)
        local (fun rho =>
          gvar_injection (ge_of rho) /\
          eval_expr a rho = Vptr b Ptrofs.zero /\
          global_block rho id b) &&
        `(funspec_sub_si fs (mk_funspec (argsig, retsig) cc A P Q NEP NEQ)) &&
        (* evaluate to an actual function with specification [A]{P}{Q} *)
        |>(EX ts x,
            (`(P ts x: environ -> mpred)
              (make_args' (argsig,retsig) (eval_exprlist (snd (split argsig)) bl))) *
            oboxopt Delta ret (maybe_retval (Q ts x) retsig ret -* R)))
      (Clight.Scall ret a bl)
      (* ret = a(bl) *)
      (normal_ret_assert R)
| semax_label: forall (P:environ -> mpred) (c:Clight.statement) (Q:ret_assert) l,
  @semax CS Espec Delta P c Q ->
  @semax CS Espec Delta P (Clight.Slabel l c) Q
| semax_goto: forall P l, @semax CS Espec Delta FF (Clight.Sgoto l) P
| semax_switch: forall  a sl R,
     (* (Q: environ->mpred)
     (forall rho, Q rho |-- tc_expr Delta a rho) ->
     (forall n,
     @semax CS Espec Delta 
               (local (`eq (eval_expr a) `(Vint n)) &&  Q)
               (seq_of_labeled_statement (select_switch (Int.unsigned n) sl))
               (switch_ret_assert R)) -> *)
     (* @semax CS Espec Delta (!! (is_int_type (typeof a) = true) && Q)  *)
     @semax CS Espec Delta FF (Clight.Sswitch a sl) R.

Inductive semax2 {CS: compspecs} {Espec: OracleKind} (Delta: tycontext): (environ -> mpred) -> Clight.statement -> ret_assert -> Prop :=
| semax_conseq2: forall P' (R': ret_assert) P c (R: ret_assert) ,
(local (tc_environ Delta) && (allp_fun_id Delta && P) |-- P') ->
local (tc_environ Delta) && ((allp_fun_id Delta) && RA_normal R') |-- |==> |> FF || RA_normal R ->
    local (tc_environ Delta) && ((allp_fun_id Delta) && RA_break R') |-- |==> |> FF || RA_break R ->
    local (tc_environ Delta) && ((allp_fun_id Delta) && RA_continue R') |-- |==> |> FF || RA_continue R ->
    (forall vl, local (tc_environ Delta) && ((allp_fun_id Delta) && RA_return R' vl) |-- |==> |> FF || RA_return R vl) ->
    @semax CS Espec Delta P' c R' -> @semax2 CS Espec Delta P c R.

Declare Scope assert_strong.

Notation "'EX' x .. y , P " :=
  (@exp (environ->mpred) _ _ (fun x =>
    ..
    (@exp (environ->mpred) _ _ (fun y => P))
    ..
    )) (at level 65, x binder, y binder, right associativity) : assert_strong.

Notation " 'ENTAIL' d ',' P '|--' Q " :=
  (@derives (environ->mpred) _ (andp (local (tc_environ d)) P) Q) (at level 80, P at level 79, Q at level 79) : assert_strong.

Local Open Scope assert_strong.

Lemma semax_skip_inv: forall CS Espec Delta P R,
  @semax CS Espec Delta P (Clight.Sskip) R ->
  ENTAIL Delta, (allp_fun_id Delta && P) |-- RA_normal R.
Proof.
  intros.
  remember (Clight.Sskip) as c1.
  induction H; try inversion Heqc1.
  - solve_andp.
  - subst. specialize (IHsemax eq_refl).
    eapply derives_trans.
    2:{ apply H0. }
    apply andp_right;try solve_andp.
    apply andp_right;try solve_andp.
    eapply derives_trans.
    2:{ apply IHsemax. }
    apply andp_right;try solve_andp.
    apply andp_right;try solve_andp.
    auto.
Qed.

Ltac unfold_der := unfold normal_ret_assert,
  overridePost, RA_normal, RA_break, RA_continue, RA_return in *.

Lemma semax_call_inv:
  forall {CS: compspecs} {Espec: OracleKind} 
      Delta ret a bl Pre Post,
    @semax CS Espec Delta Pre (Clight.Scall ret a bl) Post ->
    local (tc_environ Delta) && (allp_fun_id Delta && Pre)
    |-- 
    (EX argsig retsig cc A P Q NEP NEQ b id fs, 
      !! (Cop.classify_fun (typeof a) =
            Cop.fun_case_f (type_of_params argsig) retsig cc /\
          (retsig = Tvoid -> ret = None) /\
          tc_fn_return Delta ret retsig /\
          precise_context Delta /\
          (glob_specs Delta) ! id = Some fs) &&
      ((tc_expr Delta a) && (tc_exprlist Delta (snd (split argsig)) bl)) &&
      local (fun rho =>
        gvar_injection (ge_of rho) /\
        eval_expr a rho = Vptr b Ptrofs.zero /\
        global_block rho id b) &&
      `(funspec_sub_si fs (mk_funspec (argsig, retsig) cc A P Q NEP NEQ)) &&
     |>(EX ts x,
        (`(P ts x: environ -> mpred)
          (make_args' (argsig,retsig) (eval_exprlist (snd (split argsig)) bl))) *
        oboxopt Delta ret (maybe_retval (Q ts x) retsig ret -* RA_normal Post))).
Proof.
  intros. 
  remember (Clight.Scall ret a bl) as c1.
  induction H; try inversion Heqc1.
  - subst. 
    eapply derives_trans with
      (Q := local (tc_environ Delta) && (allp_fun_id Delta && P')).
    { rewrite (add_andp _ _ H). solve_andp. }
    eapply derives_trans.
    { apply andp_right.
      + rewrite <- andp_assoc. apply andp_left1.
        apply derives_refl.
      + apply IHsemax;auto. }
    clear IHsemax.
    clear P H.
    reduceR. rewrite andp_assoc.
    apply exp_ENTAILL; intro argsig.
    apply exp_ENTAILL; intro retsig.
    apply exp_ENTAILL; intro cc.
    apply exp_ENTAILL; intro A.
    apply exp_ENTAILL; intro P.
    apply exp_ENTAILL; intro Q.
    apply exp_ENTAILL; intro NEP.
    apply exp_ENTAILL; intro NEQ.
    apply exp_ENTAILL; intro b.
    apply exp_ENTAILL; intro id.
    apply exp_ENTAILL; intro fs.
    normalize.
    apply andp_ENTAILL; [reduceLL; solve_andp |].
    apply later_ENTAILL.
    apply exp_ENTAILL; intro ts.
    apply exp_ENTAILL; intro x.
    apply sepcon_ENTAILL; [reduceLL; solve_andp |].
    apply oboxopt_left2'; eauto.
    { hnf. destruct H. destruct H6 as [? [H7 ?]].
      hnf in H7. destruct ret;auto.
      hnf. destruct ((temp_types Delta) ! i);auto.
      intros C. inv C. }
    apply wand_ENTAILL; [reduceL; solve_andp |].
    auto.
  - solve_andp.
Qed.

Lemma exp_rewrite T H B x:
  @predicates_hered.exp T H B x =
    @exp (predicates_hered.pred T) (algNatDed T) B x.
Proof. reflexivity. Qed.

Lemma allp_rewrite T H B x:
  @predicates_hered.allp T H B x =
    @allp (predicates_hered.pred T) (algNatDed T) B x.
Proof. reflexivity. Qed.

Lemma andp_rewrite T H x y:
  @predicates_hered.andp T H x y =
    @andp (predicates_hered.pred T) (algNatDed T) x y.
Proof. reflexivity. Qed.

Lemma imp_rewrite T H x y:
  @predicates_hered.imp T H x y =
    @imp (predicates_hered.pred T) (algNatDed T) x y.
Proof. reflexivity. Qed.

Lemma prop_rewrite T H x:
  @predicates_hered.prop T H x =
    @prop (predicates_hered.pred T) (algNatDed T) x.
Proof. reflexivity. Qed.

Lemma derives_rewrite P Q:
  predicates_hered.derives P Q ->
  @derives
    (@predicates_hered.pred compcert_rmaps.RML.R.rmap compcert_rmaps.RML.R.ag_rmap) 
    Nveric P Q.
Proof. auto. Qed.

Lemma sepcon_rewrite: forall A B,
  predicates_sl.sepcon A B = sepcon A B.
Proof.
  intros. reflexivity.
Qed.

Ltac rewrite_predicates_hered:=
  repeat (
    try rewrite !andp_rewrite;
    try rewrite !prop_rewrite;
    try rewrite !exp_rewrite;
    try rewrite !imp_rewrite;
    try rewrite !allp_rewrite;
    try rewrite !sepcon_rewrite
  ).

Lemma semax_fun_id:
  forall {CS: compspecs} {Espec: OracleKind}
      id f Delta P Q c,
    (var_types Delta) ! id = None ->
    (glob_specs Delta) ! id = Some f ->
    (glob_types Delta) ! id = Some (type_of_funspec f) ->
    @semax CS Espec Delta
      (P && `(func_ptr f) (eval_var id (type_of_funspec f)))
      c Q ->
    @semax CS Espec Delta P c Q.
Proof.
  intros.
  eapply semax_conseq;[..|apply H2]; try solve [intros; solve_andp].
  apply andp_right; [solve_andp |].
  rewrite andp_comm.
  rewrite imp_andp_adjoint.
  rewrite imp_andp_adjoint.
  intros rho.
  apply derives_extract_prop. intros Hinj.
  apply (allp_left _ id).
  apply (allp_left _ f).
  rewrite log_normalize.prop_imp by auto.
  apply exp_left; intros b.
  unfold local, lift1; unfold_lift; simpl. normalize.
  rewrite <- imp_andp_adjoint.
  rewrite <- imp_andp_adjoint. normalize. 
  unfold derives. apply predicates_hered.exp_right with (x:=b). eapply predicates_hered.prop_andp_right.
  - unfold eval_var. rewrite H3.
    destruct H4 as [_ [? _]].
    specialize (H4 id).
    rewrite H in H4.
    destruct (Map.get (ve_of rho) id) as [[? ?] |]; [exfalso | auto].
    specialize (H4 t).
    destruct H4 as [_ ?].
    specialize (H4 ltac:(eexists; eauto)). congruence.
  - unfold func_ptr, seplog.func_ptr. (* apply predicates_hered.exp_right with (x:=f). *)
    apply predicates_hered.andp_left1. 
    apply predicates_hered.exp_left; intros bb.
    apply normalize.derives_extract_prop; intros X; inv X. trivial.
Qed.

Definition precise_funspec_logic (Delta : seplog.tycontext) (f : funspec) :=
  match f with mk_funspec fsig _ A P R _ _ =>	
    forall (bl : environ -> list val) (Q1 Q2 : environ -> mpred)
        (ret : option ident),
      (snd fsig = Tvoid -> ret = None) ->
      tc_fn_return Delta ret (snd fsig) ->
      ((EX ts x,
        (` (P ts x : environ-> mpred) (make_args' fsig bl)) *
        oboxopt Delta ret
          (fun rho : environ => maybe_retval (R ts x) (snd fsig) ret rho -* Q1 rho)) &&
      (EX ts' x',
        (` (P ts' x' : environ-> mpred) (make_args' fsig bl)) *
        oboxopt Delta ret (maybe_retval (R ts' x') (snd fsig) ret -* Q2)))
      |-- (EX ts x,
          (` (P ts x : environ-> mpred) (make_args' fsig bl)) *
          oboxopt Delta ret (maybe_retval (R ts x) (snd fsig) ret -* Q1 && Q2))
  end.

Lemma precise_funspec_is_precise_logic
    (Delta : seplog.tycontext) (f : funspec):
  precise_funspec Delta f ->
  precise_funspec_logic Delta f.
Proof.
  intros.
  hnf. hnf in H.
  destruct f. intros. intro r.
  specialize (H bl Q1 Q2 ret r H0 H1).
  eapply derives_trans.
  { eapply derives_trans.
    2:{ apply H. }
    apply derives_refl.
  }
  { apply derives_refl. }
Qed.

Ltac Intro_prop :=
  autorewrite with gather_prop;
  match goal with
  | |- _ && ?PQR |-- _ =>
      first [ is_evar PQR; fail 1
            | simple apply derives_extract_prop; fancy_intros false
            ]
  end.

Ltac Intro'' a :=
   ( (simple apply extract_exists_pre; intro a)
   || (simple apply exp_left; intro a)
   || (rewrite exp_andp1; Intro'' a)
   || (rewrite exp_andp2; Intro'' a)
   || (rewrite exp_sepcon1; Intro'' a)
   || (rewrite exp_sepcon2; Intro'' a)
   ).

Ltac Intro a :=
  repeat Intro_prop;
  match goal with
  | |- ?A |-- ?B =>
     let z := fresh "z" in pose (z:=B); change (A|--z); Intro'' a; subst z
  | |- semax _ _ _ _ =>
     Intro'' a
  end.

Tactic Notation "Intros" := repeat Intro_prop.

Tactic Notation "Intros" simple_intropattern(x0) :=
  Intro x0; repeat Intro_prop.

Tactic Notation "Intros" simple_intropattern(x0)
    simple_intropattern(x1) :=
  Intro x0; Intro x1; repeat Intro_prop.

Tactic Notation "Intros" simple_intropattern(x0)
    simple_intropattern(x1) simple_intropattern(x2) :=
  Intro x0; Intro x1; Intro x2; repeat Intro_prop.

Tactic Notation "Intros" simple_intropattern(x0)
    simple_intropattern(x1) simple_intropattern(x2)
    simple_intropattern(x3) :=
  Intro x0; Intro x1; Intro x2; Intro x3; repeat Intro_prop.

Tactic Notation "Intros" simple_intropattern(x0)
    simple_intropattern(x1) simple_intropattern(x2)
    simple_intropattern(x3) simple_intropattern(x4) :=
  Intro x0; Intro x1; Intro x2; Intro x3; Intro x4; repeat Intro_prop.

Tactic Notation "Intros" simple_intropattern(x0)
    simple_intropattern(x1) simple_intropattern(x2)
    simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) :=
  Intro x0; Intro x1; Intro x2; Intro x3; Intro x4;
  Intro x5; repeat Intro_prop.

Tactic Notation "Intros" simple_intropattern(x0)
    simple_intropattern(x1) simple_intropattern(x2)
    simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) :=
  Intro x0; Intro x1; Intro x2; Intro x3; Intro x4;
  Intro x5; Intro x6; repeat Intro_prop.

Tactic Notation "Intros" simple_intropattern(x0)
    simple_intropattern(x1) simple_intropattern(x2)
    simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6)
    simple_intropattern(x7) :=
  Intro x0; Intro x1; Intro x2; Intro x3; Intro x4;
  Intro x5; Intro x6; Intro x7; repeat Intro_prop.

Tactic Notation "Intros" simple_intropattern(x0)
    simple_intropattern(x1) simple_intropattern(x2)
    simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6)
    simple_intropattern(x7) simple_intropattern(x8) :=
  Intro x0; Intro x1; Intro x2; Intro x3; Intro x4;
  Intro x5; Intro x6; Intro x7; Intro x8; repeat Intro_prop.

Tactic Notation "Intros" simple_intropattern(x0)
    simple_intropattern(x1) simple_intropattern(x2)
    simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6)
    simple_intropattern(x7) simple_intropattern(x8)
    simple_intropattern(x9) :=
  Intro x0; Intro x1; Intro x2; Intro x3; Intro x4;
  Intro x5; Intro x6; Intro x7; Intro x8; Intro x9; repeat Intro_prop.

Tactic Notation "Intros" simple_intropattern(x0)
    simple_intropattern(x1) simple_intropattern(x2)
    simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6)
    simple_intropattern(x7) simple_intropattern(x8)
    simple_intropattern(x9) simple_intropattern(x10) :=
  Intro x0; Intro x1; Intro x2; Intro x3; Intro x4;
  Intro x5; Intro x6; Intro x7; Intro x8; Intro x9;
  Intro x10; repeat Intro_prop.

Tactic Notation "Intros" simple_intropattern(x0)
    simple_intropattern(x1) simple_intropattern(x2)
    simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6)
    simple_intropattern(x7) simple_intropattern(x8)
    simple_intropattern(x9) simple_intropattern(x10)
    simple_intropattern(x11) :=
  Intro x0; Intro x1; Intro x2; Intro x3; Intro x4;
  Intro x5; Intro x6; Intro x7; Intro x8; Intro x9;
  Intro x10; Intro x11; repeat Intro_prop.


Lemma assert_PROPP' {A} {NA: NatDed A}:
  forall P Pre (Post: A),
    Pre |-- !! P ->
    (P -> Pre |-- Post) ->
    Pre |-- Post.
Proof.
  intros.
  apply derives_trans with (!!P && Pre).
  apply andp_right; auto.
  apply derives_extract_prop. auto.
Qed.

Tactic Notation "assert_PROPP" constr(A) :=
  first [ apply (assert_PROPP' A)]; [ | intro ].

Tactic Notation "assert_PROPP" constr(A) "by" tactic1(t) :=
  first [apply (assert_PROPP' A) ]; [ now t | intro ].

Tactic Notation "assert_PROPP" constr(A) "as" simple_intropattern(H)  :=
  first [apply (assert_PROPP' A)]; [ | intro H ].

Tactic Notation "assert_PROPP" constr(A) "as" simple_intropattern(H) "by" tactic1(t) :=
  first [apply (assert_PROPP' A)]; [ now t | intro H ].


Ltac Exists'' a :=
  first [ apply exp_right with a
        | rewrite exp_andp1; Exists'' a
        | rewrite exp_andp2; Exists'' a
        | rewrite exp_sepcon1; Exists'' a
        | rewrite exp_sepcon2; Exists'' a
        ].

Ltac Exists' a :=
  match goal with |- ?A |-- ?B =>
     let z := fresh "z" in pose (z:=A); change (z|--B); Exists'' a; subst z
  end.

Tactic Notation "Exists" constr(x0) :=
  Exists' x0.

Tactic Notation "Exists" constr(x0) constr(x1) :=
  Exists' x0; Exists x1.

Tactic Notation "Exists" constr(x0) constr(x1) constr(x2) :=
  Exists' x0; Exists' x1; Exists' x2.

Tactic Notation "Exists" constr(x0) constr(x1) constr(x2) constr(x3) :=
  Exists' x0; Exists' x1; Exists' x2; Exists' x3.

Tactic Notation "Exists" constr(x0) constr(x1) constr(x2) constr(x3)
    constr(x4) :=
  Exists' x0; Exists' x1; Exists' x2; Exists' x3; Exists' x4.

Tactic Notation "Exists" constr(x0) constr(x1) constr(x2) constr(x3)
    constr(x4) constr(x5) :=
  Exists' x0; Exists' x1; Exists' x2; Exists' x3; Exists' x4;
  Exists' x5.

Tactic Notation "Exists" constr(x0) constr(x1) constr(x2) constr(x3)
    constr(x4) constr(x5) constr(x6) :=
  Exists' x0; Exists' x1; Exists' x2; Exists' x3; Exists' x4;
  Exists' x5; Exists' x6.

Tactic Notation "Exists" constr(x0) constr(x1) constr(x2) constr(x3)
 constr(x4) constr(x5) constr(x6) constr(x7) :=
 Exists' x0; Exists' x1; Exists' x2; Exists' x3; Exists' x4;
 Exists' x5; Exists' x6; Exists' x7.

Tactic Notation "Exists" constr(x0) constr(x1) constr(x2) constr(x3)
    constr(x4) constr(x5) constr(x6) constr(x7) constr(x8) :=
  Exists' x0; Exists' x1; Exists' x2; Exists' x3; Exists' x4;
  Exists' x5; Exists' x6; Exists' x7; Exists' x8.

Tactic Notation "Exists" constr(x0) constr(x1) constr(x2) constr(x3)
    constr(x4) constr(x5) constr(x6) constr(x7) constr(x8) constr(x9) :=
  Exists' x0; Exists' x1; Exists' x2; Exists' x3; Exists' x4;
  Exists' x5; Exists' x6; Exists' x7; Exists' x8; Exists' x9.

Tactic Notation "Exists" constr(x0) constr(x1) constr(x2) constr(x3)
    constr(x4) constr(x5) constr(x6) constr(x7) constr(x8) constr(x9)
    constr(x10) :=
  Exists' x0; Exists' x1; Exists' x2; Exists' x3; Exists' x4;
  Exists' x5; Exists' x6; Exists' x7; Exists' x8; Exists' x9;
  Exists' x10.

Tactic Notation "Exists" constr(x0) constr(x1) constr(x2) constr(x3)
    constr(x4) constr(x5) constr(x6) constr(x7) constr(x8) constr(x9)
    constr(x10) constr(x11) :=
  Exists' x0; Exists' x1; Exists' x2; Exists' x3; Exists' x4;
  Exists' x5; Exists' x6; Exists' x7; Exists' x8; Exists' x9;
  Exists' x10; Exists' x11.

Tactic Notation "Exists" constr(x0) constr(x1) constr(x2) constr(x3)
    constr(x4) constr(x5) constr(x6) constr(x7) constr(x8) constr(x9)
    constr(x10) constr(x11) constr(x12) :=
  Exists' x0; Exists' x1; Exists x2; Exists' x3; Exists' x4;
  Exists' x5; Exists' x6; Exists' x7; Exists' x8; Exists' x9;
  Exists' x10; Exists' x11; Exists' x12.

Lemma semax_conj_call_same_function:
  forall (CS: compspecs) a b1 b2 id1 id2,
    local (fun rho =>
      gvar_injection (ge_of rho) /\
      eval_expr a rho = Vptr b1 Ptrofs.zero /\
      global_block rho id1 b1) &&
    local (fun rho =>
      gvar_injection (ge_of rho) /\
      eval_expr a rho = Vptr b2 Ptrofs.zero /\
      global_block rho id2 b2)
    |-- !! (b1 = b2 /\ id1 = id2).
Proof.
  intros.
  intros rho. unfold local, lift1. simpl.
  rewrite <- prop_and.
  apply prop_derives.
  intros [[Hinj [H0 [H1' H1]]] [_ [H2 [H3' H3]]]].
  rewrite H0 in H2. inv H2.
  split; trivial.
  eapply Hinj; eassumption.
Qed.

Lemma funspec_sub_si_sig_cc_eq:
  forall fsig1 fsig2 cc1 cc2 A1 A2 P1 P2 Q1 Q2 NEP1 NEP2 NEQ1 NEQ2,
    `(funspec_sub_si
      (mk_funspec fsig1 cc1 A1 P1 Q1 NEP1 NEQ1)
      (mk_funspec fsig2 cc2 A2 P2 Q2 NEP2 NEQ2))
    |-- !! (fsig1 = fsig2 /\ cc1 = cc2).
Proof.
  intros. intros rho.
  unfold_lift. unfold prop. simpl.
  rewrite_predicates_hered.
  apply andp_left1.
  apply derives_refl.
Qed.

Lemma semax_conj_call:
  forall CS Espec Delta ret a bl P Q Q1 Q2,
    @semax CS Espec Delta P 
      (Clight.Scall ret a bl) (overridePost Q2 Q) ->
    @semax CS Espec Delta P 
      (Clight.Scall ret a bl) (overridePost Q1 Q) ->
    @semax CS Espec Delta P 
      (Clight.Scall ret a bl) (overridePost (Q1 && Q2) Q).
Proof.
  intros CS Espec Delta ret a bl P Q Q1 Q2.
  intros.
  apply semax_call_inv in H.
  apply semax_call_inv in H0.
  pose proof andp_ENTAILL _ _ _ _ _ H0 H.
  rewrite andp_dup in H1. clear H H0.
  eapply semax_conseq;
  [..|apply semax_call with (R:= Q1 && Q2)];
  try (intros; 
  try solve [repeat apply andp_left2;apply FF_left]).
  2:{ destruct Q;unfold_der. solve_andp. }
  eapply ENTAIL_trans;[apply H1|]. clear H1.
  Intros argsig1 retsig1 cc1 A1 P1 R1 NEP1 NER1 b1 id1 fs1.
  Intros argsig2 retsig2 cc2 A2 P2 R2 NEP2 NER2 b2 id2 fs2.
  rewrite <- andp_assoc. rewrite andp_comm.
  rewrite !andp_assoc.
  apply derives_extract_prop.
  intros [H [H0 [H1 [H2 H3]]]].
  rewrite <- andp_assoc. rewrite <- andp_assoc.
  rewrite <- andp_assoc. rewrite <- andp_assoc.
  rewrite <- andp_assoc.
  rewrite andp_comm. rewrite !andp_assoc.
  apply derives_extract_prop.
  intros [H4 [H5 [H6 [H7 H8]]]].
  rewrite H4 in H. inversion H.
  subst cc2 retsig2. clear H.
  apply typ_of_params_eq_inv in H10.
  rewrite H10. clear H10.

  destruct Q as [Qn Qb Qc Qr];unfold_der.

  apply derives_trans with (
    local (tc_environ Delta) && tc_expr Delta a &&
    (tc_exprlist Delta (snd (split argsig2)) bl &&
    (local
      (fun rho : environ =>
        gvar_injection (ge_of rho) /\
        eval_expr a rho = Vptr b1 Ptrofs.zero /\
        global_block rho id1 b1) &&
    local
      (fun rho : environ =>
        gvar_injection (ge_of rho) /\
        eval_expr a rho = Vptr b2 Ptrofs.zero /\
        global_block rho id2 b2)) &&
    (`(funspec_sub_si fs1 (mk_funspec (argsig1, retsig1) cc1 A1 P1 R1 NEP1 NER1)) &&
     `(funspec_sub_si fs2 (mk_funspec (argsig2, retsig1) cc1 A2 P2 R2 NEP2 NER2))) &&
    |> (EX ts1 x1, (` (P1 ts1 x1 : environ -> mpred))
        (make_args' (argsig1, retsig1) (eval_exprlist (snd (split argsig2)) bl)) *
      oboxopt Delta ret (maybe_retval (R1 ts1 x1) retsig1 ret -* Q1)) &&
    |> (EX ts2 x2,  (` (P2 ts2 x2 : environ -> mpred))
        (make_args' (argsig2, retsig1)
            (eval_exprlist (snd (split argsig2)) bl)) *
      oboxopt Delta ret (maybe_retval (R2 ts2 x2) retsig1 ret -* Q2)))).
  { solve_andp. }

  rewrite (add_andp _ _ (semax_conj_call_same_function _ _ _ _ _ _)).
  assert_PROPP (b1 = b2 /\ id1 = id2) by solve_andp.
  destruct H as [<- <-].

  assert (fs1 = fs2).
  { rewrite H3 in H8.
    injection H8. auto. }
  subst fs2.

  destruct fs1 as [fsig' cc' A' P' R' NEP' NER'].
  assert_PROPP (argsig1 = argsig2 /\
    fsig' = (argsig1, retsig1) /\
    cc' = cc1).
  { apply andp_left2. apply andp_left1.
    apply andp_left1. apply andp_left2.
    apply derives_trans with (
      !! (fsig' = (argsig1, retsig1) /\ cc' = cc1) &&
      !! (fsig' = (argsig2, retsig1) /\ cc' = cc1)).
    apply andp_derives; apply funspec_sub_si_sig_cc_eq.
    rewrite <- prop_and. apply prop_derives.
    intros [[? ?] [? ?]].
    split.
    rewrite H10 in H.
    injection H. auto.
    split; auto. }
  destruct H as [? [? ?]].
  subst argsig2 fsig' cc'.
  clear H6 H7 H8.

  Exists argsig1 retsig1 cc1 A' P' R' NEP' NER' b1 id1
    (mk_funspec (argsig1, retsig1) cc1 A' P' R' NEP' NER').
  apply andp_right.
  apply andp_right.
  apply andp_right.
  apply andp_right.
  { apply prop_right. auto. }
  { solve_andp. }
  { solve_andp. }
  { apply derives_trans with TT.
    apply TT_right. unfold_lift. intros rho.
    apply derives_rewrite.
    apply funspec_sub_si_refl. }

  repeat rewrite andp_assoc.
  rewrite andp_comm.
  repeat rewrite andp_assoc.
  apply andp_left2.
  rewrite andp_comm.
  repeat rewrite andp_assoc.
  do 3 apply andp_left2.
  rewrite <- andp_assoc.
  rewrite andp_comm.
  rewrite <- andp_assoc.

  apply derives_trans with (
    |> (EX ts x,
      (` (P' ts x : environ -> mpred))
        (make_args' (argsig1, retsig1)
          (eval_exprlist (snd (split argsig1)) bl)) *
      oboxopt Delta ret
        (maybe_retval (R' ts x) retsig1 ret -* Q1)) &&
    |> (EX ts x,
      (` (P' ts x : environ -> mpred))
        (make_args' (argsig1, retsig1) (eval_exprlist (snd (split argsig1)) bl)) *
      oboxopt Delta ret
        (maybe_retval (R' ts x) retsig1 ret -* Q2))).
  { apply derives_trans with (
      local (tc_environ Delta) &&
      tc_exprlist Delta (snd (split argsig1)) bl &&
      `(funspec_sub_si (mk_funspec (argsig1, retsig1) cc1 A' P' R' NEP' NER')
        (mk_funspec (argsig1, retsig1) cc1 A1 P1 R1 NEP1 NER1)) &&
      |> (EX ts x,
      (` (P1 ts x : environ -> mpred))
        (make_args' (argsig1, retsig1)
          (eval_exprlist (snd (split argsig1)) bl)) *
        oboxopt Delta ret
          (maybe_retval (R1 ts x) retsig1 ret -* Q1)) &&
      (local (tc_environ Delta) &&
      tc_exprlist Delta (snd (split argsig1)) bl &&
      `(funspec_sub_si (mk_funspec (argsig1, retsig1) cc1 A' P' R' NEP' NER')
        (mk_funspec (argsig1, retsig1) cc1 A2 P2 R2 NEP2 NER2)) &&
      |> (EX ts x,
      (` (P2 ts x : environ -> mpred))
        (make_args' (argsig1, retsig1)
          (eval_exprlist (snd (split argsig1)) bl)) *
        oboxopt Delta ret
          (maybe_retval (R2 ts x) retsig1 ret -* Q2)))).
    { solve_andp. }
    apply andp_derives.
    - apply funspec_rewrite_logic.
    - apply funspec_rewrite_logic. }

  rewrite <- later_andp.
  apply later_derives.

  assert (precise_funspec Delta (mk_funspec (argsig1, retsig1) cc1 A' P' R' NEP' NER')).
  { eapply H2; eassumption. }

  apply precise_funspec_is_precise_logic in H.
  unfold precise_funspec_logic in H.
  specialize (H ((eval_exprlist (snd (split argsig1)) bl)) Q1 Q2 ret).
  specialize (H H0 H1).
  apply H.
Qed.

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

Lemma semax_seq_inv:
  forall CS Espec (Delta : tycontext) (P : environ -> mpred) 
      (R : ret_assert) (h t : Clight.statement),
    @semax CS Espec Delta P (Clight.Ssequence h t) R ->
    exists Q : environ -> mpred,
      @semax CS Espec Delta P h (overridePost Q R) /\
      @semax CS Espec Delta Q t R.
Proof.
  intros.
  remember (Clight.Ssequence h  t) as c.
  induction H;inversion Heqc.
  + subst. exists Q. auto.
  + specialize (IHsemax H5).
    destruct IHsemax as [Q [? ?]].
    exists Q. split.
    - eapply semax_conseq;[..|apply H6];auto;
      destruct R as [Rn Rb Rc Rr];
      destruct R' as [Rn' Rb' Rc' Rr']; unfold_der;auto.
      solve_andp.
    - eapply semax_conseq;[..|apply H7];auto;
      destruct R as [Rn Rb Rc Rr];
      destruct R' as [Rn' Rb' Rc' Rr']; unfold_der;auto.
      solve_andp.
Qed.


Lemma semax_seq_inv':
  forall CS Espec (Delta : tycontext) (P : environ -> mpred) 
      (R : ret_assert) (h t : Clight.statement),
    @semax CS Espec Delta P (Clight.Ssequence h t) R ->
    @semax CS Espec Delta P h
      (overridePost
        (EX Q : environ -> mpred,
          !! semax Delta Q t R && Q) R).
Proof.
  intros.
  remember (Clight.Ssequence h  t) as c.
  induction H;inversion Heqc.
  + subst. eapply semax_conseq;[..|apply H];auto;
    destruct R as [Rn Rb Rc Rr]; unfold_der;auto;intros; try solve_andp.
    Exists Q. apply andp_right;try solve_andp. apply prop_right.
    auto.
  + specialize (IHsemax H5).
    eapply semax_conseq;[..|apply IHsemax];auto;
      destruct R as [Rn Rb Rc Rr];
      destruct R' as [Rn' Rb' Rc' Rr']; unfold_der;auto.
    Intros Q. Exists Q.
    apply andp_right;try solve_andp.
    rewrite <- andp_assoc.
    rewrite andp_comm.
    rewrite andp_assoc. apply derives_extract_prop.
    intros. apply prop_right.
    eapply semax_conseq;[..|apply H6];auto;
    unfold_der;auto.
    solve_andp.
Qed.

Lemma semax2_seq_inv: forall CS Espec Delta c1 c2 P R,
  @semax2 CS Espec Delta P (Clight.Ssequence c1 c2) R ->
  exists Q,
    @semax CS Espec Delta P c1 Q /\
    @semax2 CS Espec Delta (RA_normal Q) c2 R.
Proof.
  intros. inv H.
  apply semax_seq_inv in H5.
  destruct H5 as [Q [? ?]].
  destruct R as [Rn Rb Rc Rr].
  destruct R' as [Rn' Rb' Rc' Rr'].
  exists {|
    RA_normal := Q;
    RA_break := |==> |> FF || Rb;
    RA_continue := |==> |> FF || Rc;
    RA_return := |==> |> FF || Rr;
  |}.
  split;unfold_der.
  + eapply semax_conseq;[..|apply H]; unfold_der; auto.
    solve_andp.
  + eapply semax_conseq2;[..|apply H5]; unfold_der; auto.
    solve_andp.
Qed.

Lemma allp_ENTAILL: forall Delta B (P Q: B -> environ -> mpred),
  (forall x: B,
    local (tc_environ Delta) && (allp_fun_id Delta && P x) |-- Q x) ->
  local (tc_environ Delta) && (allp_fun_id Delta && allp P) |-- allp Q.
Proof.
  intros.
  apply allp_right; intro y.
  rewrite <- andp_assoc, andp_comm.
  apply imp_andp_adjoint.
  apply allp_left with y.
  apply imp_andp_adjoint.
  rewrite andp_comm, andp_assoc.
  apply H.
Qed.

Lemma imp_ENTAILL: forall Delta P P' Q Q',
  local (tc_environ Delta) && (allp_fun_id Delta && P') |-- P ->
  local (tc_environ Delta) && (allp_fun_id Delta && Q) |-- Q' ->
  local (tc_environ Delta) && (allp_fun_id Delta && (P -->Q)) |-- P' --> Q'.
Proof.
  intros.
  rewrite <- andp_assoc in *.
  rewrite <- imp_andp_adjoint.
  eapply derives_trans; [| apply H0].
  apply andp_right; [apply andp_left1, andp_left1, derives_refl |].
  rewrite !andp_assoc, (andp_comm _ P'), <- !andp_assoc.
  apply imp_andp_adjoint.
  eapply derives_trans; [apply H |].
  apply imp_andp_adjoint.
  apply modus_ponens.
Qed.

Lemma semax_assign_inv:
  forall {CS: compspecs} {Espec: OracleKind} Delta e1 e2 P Q,
    @semax CS Espec Delta P (Clight.Sassign e1 e2) Q ->
    local (tc_environ Delta) && (allp_fun_id Delta && P) |-- 
      (EX sh: share, !! writable_share sh &&
        |> ( (tc_lvalue Delta e1) &&  (tc_expr Delta (Ecast e2 (typeof e1)))  &&
        ((`(mapsto_ sh (typeof e1)) (eval_lvalue e1)) *
        (`(mapsto sh (typeof e1)) (eval_lvalue e1) (`force_val (`(sem_cast (typeof e2) (typeof e1)) (eval_expr e2))) -* RA_normal Q)))).
Proof.
  intros.
  remember (Clight.Sassign e1 e2) as c eqn:?H.
  induction H;try solve [inv H0].
  + inv H0. reduce2derives. 
    apply exp_derives; intro sh.
    apply andp_derives; auto.
    apply later_derives; auto.
    apply andp_derives; auto.
    apply sepcon_derives; auto.
    apply wand_derives; auto. unfold_der. auto.
  + subst c. specialize (IHsemax eq_refl).
    eapply derives_trans with (Q:= (andp (local (tc_environ Delta)) (andp (allp_fun_id Delta) P'))).
    { repeat (apply andp_right;try solve_andp). auto. }
    eapply derives_trans.
    { apply andp_right with (P0:=local (tc_environ Delta)). solve_andp.
      apply andp_right with (P0:=
      allp_fun_id Delta). solve_andp. apply derives_refl. }
    eapply derives_trans.
    { apply andp_right. apply andp_left1. apply derives_refl.
      apply andp_right. apply andp_left2. apply andp_left1. apply derives_refl.
      apply andp_left2. apply andp_left2.
      apply IHsemax. }
    reduceR. 
    apply exp_ENTAILL; intro sh.
    apply andp_ENTAILL; [reduceLL; apply ENTAIL_refl |].
    apply later_ENTAILL.
    apply andp_ENTAILL; [reduceLL; apply ENTAIL_refl |].
    apply sepcon_ENTAILL; [reduceLL; apply ENTAIL_refl |].
    apply wand_ENTAILL; [reduceLL; apply ENTAIL_refl |].
    auto.
Qed.

Lemma semax_set_inv: forall {CS: compspecs} {Espec: OracleKind} Delta P R id e,
  @semax CS Espec Delta P (Clight.Sset id e) R ->
  local (tc_environ Delta) && (allp_fun_id Delta && P) |-- 
    ( (|> ( (tc_expr Delta e) &&
             (tc_temp_id id (typeof e) Delta e) &&
             subst id (eval_expr e) (RA_normal R))) ||
      (EX sh: share, EX t2: type, EX v2: val,
              !! (typeof_temp Delta id = Some t2 /\
                  is_neutral_cast (typeof e) t2 = true /\
                  readable_share sh) &&
         |> ( (tc_lvalue Delta e) &&
              local (`(tc_val (typeof e) v2)) &&
              (`(mapsto sh (typeof e)) (eval_lvalue e) (`v2) * TT) &&
              subst id (`v2) (RA_normal R))) ||
      (EX sh: share, EX e1: expr, EX t1: type, EX v2: val,
              !! (e = Ecast e1 t1 /\
                  typeof_temp Delta id = Some t1 /\
                  cast_pointer_to_bool (typeof e1) t1 = false /\
                  readable_share sh) &&
         |> ( (tc_lvalue Delta e1) &&
              local (`(tc_val t1) (`(eval_cast (typeof e1) t1 v2))) &&
              (`(mapsto sh (typeof e1)) (eval_lvalue e1) (`v2) * TT) &&
              subst id (`(force_val (sem_cast (typeof e1) t1 v2))) (RA_normal R)))).
Proof.
  intros.
  remember (Clight.Sset id e) as c eqn:?H.
  induction H; try solve [inv H0].
  + inv H0.
    reduce2derives.
    apply orp_derives; [apply orp_derives |].
    - apply later_derives.
      apply andp_derives; auto.
      apply subst_derives. unfold normal_ret_assert.
      unfold RA_normal. auto.
    - apply exp_derives; intros sh.
      apply exp_derives; intros t2.
      apply exp_derives; intros v2.
      apply andp_derives; auto.
      apply later_derives.
      apply andp_derives; auto.
      apply subst_derives. unfold normal_ret_assert.
      unfold RA_normal. auto.
    - apply exp_derives; intros sh.
      apply exp_derives; intros e1.
      apply exp_derives; intros t1.
      apply exp_derives; intros v2.
      apply andp_derives; auto.
      apply later_derives.
      apply andp_derives; auto.
      apply subst_derives. unfold normal_ret_assert.
      unfold RA_normal. auto.
  + subst c.
    rename P into Pre, R into Post. specialize (IHsemax eq_refl).
    eapply derives_trans with (Q:= (andp (local (tc_environ Delta)) (andp (allp_fun_id Delta) P'))).
    { repeat (apply andp_right;try solve_andp). auto. }
    eapply derives_trans.
    { apply andp_right with (P:=local (tc_environ Delta)). solve_andp.
      apply andp_right with (P:=
      allp_fun_id Delta). solve_andp. apply derives_refl. }
    eapply derives_trans.
    { apply andp_right. apply andp_left1. apply derives_refl.
      apply andp_right. apply andp_left2. apply andp_left1. apply derives_refl.
      apply andp_left2. apply andp_left2.
      apply IHsemax. }
      reduceR.
    apply orp_ENTAILL; [apply orp_ENTAILL |].
    - apply later_ENTAILL.
      unfold tc_temp_id, typecheck_temp_id.
      destruct ((temp_types Delta) ! id) eqn:?H; [| normalize].
      eapply andp_subst_ENTAILL; [eauto | | reduceLL; apply ENTAIL_refl |].
      * destruct (is_neutral_cast (implicit_deref (typeof e)) t) eqn:?H; [| normalize].
        intro rho; unfold_lift; unfold local, lift1; simpl.
        normalize.
        apply andp_left2, andp_left1.
        eapply derives_trans; [apply typecheck_expr_sound; auto |].
        normalize.
        intros _.
        eapply expr2.neutral_cast_subsumption'; eauto.
      * auto.
    (* - apply exp_ENTAILL; intro cmp.
      apply exp_ENTAILL; intro e1.
      apply exp_ENTAILL; intro e2.
      apply exp_ENTAILL; intro ty.
      apply exp_ENTAILL; intro sh1.
      apply exp_ENTAILL; intro sh2.
      normalize. apply andp_right.
      { apply prop_right. repeat split;auto. }
      apply later_ENTAILL.
      unfold typecheck_tid_ptr_compare in H10.
      destruct ((temp_types Delta) ! id) eqn:?H; [| inv H10].
      eapply andp_subst_ENTAILL; [eauto | | reduceLL; apply ENTAIL_refl |].
      * unfold_lift; unfold local, lift1; intro rho.
        simpl. normalize.
        apply andp_left2, andp_left1. apply andp_left1.
        eapply derives_trans; [apply andp_derives; apply typecheck_expr_sound; auto |].
        normalize.
        unfold_lift.
        replace (sem_binary_operation' cmp) with (sem_cmp (expr.op_to_cmp cmp)); [| destruct cmp; inv H7; auto].
        apply binop_lemmas2.tc_val'_sem_cmp; auto.
      * auto. *)
    - apply exp_ENTAILL; intro sh.
      apply exp_ENTAILL; intro t2.
      apply exp_ENTAILL; intro v2.
      normalize.
      { apply later_ENTAILL.
        destruct H0 as [H0 [? ?]].
        unfold typeof_temp in H0.
        destruct ((temp_types Delta) ! id) eqn:?H; inv H0.
        eapply andp_subst_ENTAILL; [eauto | | reduceLL; apply ENTAIL_refl |].
        * reduceL.
          apply andp_left1.
          apply andp_left2.
          unfold_lift; unfold local, lift1; intro rho; simpl; normalize.
          intros _; eapply expr2.neutral_cast_subsumption; eauto.
        * auto.
      }
    - apply exp_ENTAILL; intro sh.
      apply exp_ENTAILL; intro e1.
      apply exp_ENTAILL; intro t1.
      apply exp_ENTAILL; intro t2.
      normalize.
      destruct H0 as [? [? [? ?]]].
      apply later_ENTAILL.
      unfold typeof_temp in H6.
      destruct ((temp_types Delta) ! id) eqn:?H; inv H6.
      eapply andp_subst_ENTAILL; [eauto | | reduceLL; apply ENTAIL_refl |].
      * reduceL.
        apply andp_left1.
        apply andp_left2.
        unfold_lift; unfold local, lift1; intro rho; simpl; normalize.
        intros _; auto.
      * auto.
Qed.

Fixpoint nobreak s :=
  match s with
  | Clight.Ssequence s1 s2 => if nobreak s1 then nobreak s2 else false
  | Clight.Sifthenelse _ s1 s2 => if nobreak s1 then nobreak s2 else false
  | Clight.Sloop s1 s2 => if nobreak s1 then nobreak s2 else false
  | Clight.Sswitch _ sl => nobreak_ls sl
  | Clight.Sgoto _ => false
  | Clight.Sbreak => false
  | Clight.Slabel _ s => nobreak s
  | _ => true
  end
with nobreak_ls sl :=
 match sl with
 | Clight.LSnil => true
 | Clight.LScons _ s sl' => if nobreak s then nobreak_ls sl' else false
 end.

Fixpoint noreturn s :=
  match s with
  | Clight.Ssequence s1 s2 => if noreturn s1 then noreturn s2 else false
  | Clight.Sifthenelse _ s1 s2 => if noreturn s1 then noreturn s2 else false
  | Clight.Sloop s1 s2 => if noreturn s1 then noreturn s2 else false
  | Clight.Sswitch _ sl => noreturn_ls sl
  | Clight.Sgoto _ => false
  | Clight.Sreturn _ => false
  | Clight.Slabel _ s => noreturn s
  | _ => true
  end
with noreturn_ls sl :=
  match sl with
  | Clight.LSnil => true
  | Clight.LScons _ s sl' => if noreturn s then noreturn_ls sl' else false
  end.

Fixpoint nocontinue s :=
  match s with
  | Clight.Ssequence s1 s2 => if nocontinue s1 then nocontinue s2 else false
  | Clight.Sifthenelse _ s1 s2 => if nocontinue s1 then nocontinue s2 else false
  | Clight.Sloop s1 s2 => if nocontinue s1 then nocontinue s2 else false
  | Clight.Sswitch _ sl => nocontinue_ls sl
  | Clight.Sgoto _ => false
  | Clight.Scontinue => false
  | Clight.Slabel _ s => nocontinue s
  | _ => true
  end
with nocontinue_ls sl :=
  match sl with
  | Clight.LSnil => true
  | Clight.LScons _ s sl' => if nocontinue s then nocontinue_ls sl' else false
  end.

Lemma noreturn_ls_spec: forall sl,
  noreturn_ls sl = true ->
  noreturn (seq_of_labeled_statement sl) = true.
Proof.
  intros.
  induction sl.
  + reflexivity.
  + simpl in *.
    destruct (noreturn s); [| inv H].
    auto.
Qed.

Lemma noreturn_ls_spec': forall sl n,
  noreturn_ls sl = true ->
  noreturn (seq_of_labeled_statement (select_switch n sl)) = true.
Proof.
  intros.
  apply noreturn_ls_spec in H.
  unfold select_switch.
  destruct (select_switch_case n sl) eqn:?Hs.
  + induction sl.
    - inv Hs.
    - simpl in Hs.
      destruct o as [c|]; [destruct (zeq c n) |].
      * subst c; inv Hs.
        apply H.
      * change (noreturn s && noreturn (seq_of_labeled_statement sl) = true)%bool in H.
        rewrite andb_true_iff in H.
        apply IHsl; auto.
        tauto.
      * change (noreturn s && noreturn (seq_of_labeled_statement sl) = true)%bool in H.
        rewrite andb_true_iff in H.
        apply IHsl; auto.
        tauto.
  + induction sl.
    - reflexivity.
    - simpl in Hs |- *.
      destruct o.
      * change (noreturn s && noreturn (seq_of_labeled_statement sl) = true)%bool in H.
        rewrite andb_true_iff in H.
        apply IHsl; [tauto |].
        if_tac in Hs; [inv Hs | auto].
      * exact H.
Qed. 

Lemma semax_post:
  forall (R' : ret_assert) (Espec : OracleKind) 
      (cs : compspecs) (Delta : tycontext) (R : ret_assert)
      (P : environ -> mpred) (c : Clight.statement),
    ENTAIL Delta, RA_normal R' |-- RA_normal R ->
    ENTAIL Delta, RA_break R' |-- RA_break R ->
    ENTAIL Delta, RA_continue R' |-- RA_continue R ->
    (forall vl : option val,
      ENTAIL Delta, RA_return R' vl |-- RA_return R vl) ->
    semax Delta P c R' -> semax Delta P c R.
Proof.
  intros.
  eapply semax_conseq;[..|apply H3];try solve_andp.
  - intros. eapply derives_trans;[|apply H]. solve_andp.
  - intros. eapply derives_trans;[|apply H0]. solve_andp.
  - intros. eapply derives_trans;[|apply H1]. solve_andp.
  - intros. eapply derives_trans;[|apply H2]. solve_andp.
Qed.

Lemma derives_aux_refl:
  forall (Delta : tycontext) (P : environ -> mpred),
    ENTAIL Delta, allp_fun_id Delta && P |--  P.
Proof.
  intros. solve_andp.
Qed.

Lemma semax_noreturn_inv:
  forall (CS : compspecs) (Espec : OracleKind) (Delta : tycontext)
      (Pre : environ -> mpred) (s : Clight.statement) 
      (Post Post' : ret_assert),
    noreturn s = true ->
    RA_normal Post = RA_normal Post' ->
    RA_break Post = RA_break Post' ->
    RA_continue Post = RA_continue Post' ->
    semax Delta Pre s Post -> semax Delta Pre s Post'.
Proof.
  intros.
  revert Post' H0 H1 H2.
  induction H3; intros.
  + change (noreturn c && noreturn d = true)%bool in H.
    rewrite andb_true_iff in H.
    specialize (IHsemax1 (proj1 H) _ H0 H1 H2).
    specialize (IHsemax2 (proj2 H) _ H0 H1 H2).
    eapply semax_ifthenelse;auto.
  + change (noreturn h && noreturn t = true)%bool in H.
    rewrite andb_true_iff in H.
    specialize (IHsemax1 (proj1 H)).
    specialize (IHsemax2 (proj2 H) _ H0 H1 H2).
    eapply semax_seq; [| eauto].
    apply IHsemax1; destruct Post', R; auto.
  + rewrite H1.
    apply semax_break.
  + rewrite H2.
    apply semax_continue.
  + simpl in H. change (noreturn body && noreturn incr = true)%bool in H.
    rewrite andb_true_iff in H.
    specialize (IHsemax1 (proj1 H) (loop1_ret_assert Q' Post')).
    specialize (IHsemax2 (proj2 H)  (loop2_ret_assert Q Post')).
    eapply semax_loop with (Q'0:=Q').
    - destruct Post', R.
      unfold loop1_ret_assert in H3_.
      simpl in *. subst. apply IHsemax1;auto.
    - destruct Post', R.
      simpl in *. subst. apply IHsemax2;auto.
  + simpl in H. inv H.
  + eapply semax_post with (normal_ret_assert P);
      [intros; apply andp_left2; try apply FF_left; rewrite H0; auto .. |].
    apply semax_skip.
  + eapply semax_post with (normal_ret_assert P);
      [intros; apply andp_left2; try apply FF_left; rewrite H0; auto .. |].
    apply semax_assign.
  + eapply semax_post with (normal_ret_assert P);
      [intros; apply andp_left2; try apply FF_left; rewrite H0; auto .. |].
    apply semax_set_ptr_compare_load_cast_load_backward.
  + apply (semax_conseq _ P' (Build_ret_assert (RA_normal R') (RA_break R') (RA_continue R') (RA_return Post'))).
    - exact H0.
    - rewrite <- H6; exact H1.
    - rewrite <- H7; exact H2.
    - rewrite <- H8; exact H3.
    - intros. solve_andp.
    - apply IHsemax; auto.
  + constructor.
  + eapply semax_conseq;[..|apply semax_call].
    - apply derives_aux_refl.
    - rewrite H0. solve_andp.
    - rewrite H1. solve_andp.
    - rewrite H2. solve_andp.
    - intros. unfold normal_ret_assert. unfold_der.
      repeat apply andp_left2. apply FF_left.
  + constructor. auto.
  + constructor.
  + constructor.
Qed.

Lemma semax_nocontinue_inv:
  forall (CS : compspecs) (Espec : OracleKind) (Delta : tycontext)
      (Pre : environ -> mpred) (s : Clight.statement) 
      (Post Post' : ret_assert),
    nocontinue s = true ->
    RA_normal Post = RA_normal Post' ->
    RA_break Post = RA_break Post' ->
    RA_return Post = RA_return Post' ->
    semax Delta Pre s Post ->
    semax Delta Pre s Post'.
Proof.
  intros.
  revert Post' H0 H1 H2.
  induction H3; intros.
  + change (nocontinue c && nocontinue d = true)%bool in H.
    rewrite andb_true_iff in H.
    specialize (IHsemax1 (proj1 H) _ H0 H1 H2).
    specialize (IHsemax2 (proj2 H) _ H0 H1 H2).
    eapply semax_ifthenelse;auto.
  + change (nocontinue h && nocontinue t = true)%bool in H.
    rewrite andb_true_iff in H.
    specialize (IHsemax1 (proj1 H)).
    specialize (IHsemax2 (proj2 H) _ H0 H1 H2).
    eapply semax_seq; [| eauto].
    apply IHsemax1; destruct Post', R; auto.
  + rewrite H1.
    apply semax_break.
  + inv H.
  + simpl in H. change (nocontinue body && nocontinue incr = true)%bool in H.
    rewrite andb_true_iff in H.
    specialize (IHsemax1 (proj1 H) (loop1_ret_assert Q' Post')).
    specialize (IHsemax2 (proj2 H)  (loop2_ret_assert Q Post')).
    eapply semax_loop with (Q'0:=Q').
    - destruct Post', R.
      unfold loop1_ret_assert in H3_.
      simpl in *. subst. apply IHsemax1;auto.
    - destruct Post', R.
      simpl in *. subst. apply IHsemax2;auto.
  + rewrite H2. apply semax_return.
  + eapply semax_post with (normal_ret_assert P);
      [intros; apply andp_left2; try apply FF_left; rewrite H0; auto .. |].
    apply semax_skip.
  + eapply semax_post with (normal_ret_assert P);
      [intros; apply andp_left2; try apply FF_left; rewrite H0; auto .. |].
    apply semax_assign.
  + eapply semax_post with (normal_ret_assert P);
      [intros; apply andp_left2; try apply FF_left; rewrite H0; auto .. |].
    apply semax_set_ptr_compare_load_cast_load_backward.
  + apply (semax_conseq _ P' (Build_ret_assert (RA_normal R') (RA_break R') (RA_continue Post') (RA_return R'))).
    - exact H0.
    - rewrite <- H6; exact H1.
    - rewrite <- H7; exact H2.
    - solve_andp. 
    - intros. rewrite <- H8; apply H4.
    - apply IHsemax; auto.
  + constructor.
  + eapply semax_conseq;[..|apply semax_call].
    - apply derives_aux_refl.
    - rewrite H0. solve_andp.
    - rewrite H1. solve_andp.
    - unfold normal_ret_assert. unfold_der.
      repeat apply andp_left2. apply FF_left.
    - intros. rewrite H2. solve_andp.
  + constructor. auto.
  + constructor.
  + constructor.
Qed.

Lemma semax_nobreak_inv:
  forall (CS : compspecs) (Espec : OracleKind) (Delta : tycontext)
      (Pre : environ -> mpred) (s : Clight.statement) 
      (Post Post' : ret_assert),
    nobreak s = true ->
    RA_normal Post = RA_normal Post' ->
    RA_return Post = RA_return Post' ->
    RA_continue Post = RA_continue Post' ->
    semax Delta Pre s Post -> semax Delta Pre s Post'.
Proof.
  intros.
  revert Post' H0 H1 H2.
  induction H3; intros.
  + change (nobreak c && nobreak d = true)%bool in H.
    rewrite andb_true_iff in H.
    specialize (IHsemax1 (proj1 H) _ H0 H1 H2).
    specialize (IHsemax2 (proj2 H) _ H0 H1 H2).
    eapply semax_ifthenelse;auto.
  + change (nobreak h && nobreak t = true)%bool in H.
    rewrite andb_true_iff in H.
    specialize (IHsemax1 (proj1 H)).
    specialize (IHsemax2 (proj2 H) _ H0 H1 H2).
    eapply semax_seq; [| eauto].
    apply IHsemax1; destruct Post', R; auto.
  + inv H.
  + rewrite H2. apply semax_continue.
  + simpl in H. change (nobreak body && nobreak incr = true)%bool in H.
    rewrite andb_true_iff in H.
    specialize (IHsemax1 (proj1 H) (loop1_ret_assert Q' Post')).
    specialize (IHsemax2 (proj2 H)  (loop2_ret_assert Q Post')).
    eapply semax_loop with (Q'0:=Q').
    - destruct Post', R.
      unfold loop1_ret_assert in H3_.
      simpl in *. subst. apply IHsemax1;auto.
    - destruct Post', R.
      simpl in *. subst. apply IHsemax2;auto.
  + rewrite H1. apply semax_return.
  + eapply semax_post with (normal_ret_assert P);
      [intros; apply andp_left2; try apply FF_left; rewrite H0; auto .. |].
    apply semax_skip.
  + eapply semax_post with (normal_ret_assert P);
      [intros; apply andp_left2; try apply FF_left; rewrite H0; auto .. |].
    apply semax_assign.
  + eapply semax_post with (normal_ret_assert P);
      [intros; apply andp_left2; try apply FF_left; rewrite H0; auto .. |].
    apply semax_set_ptr_compare_load_cast_load_backward.
  + apply (semax_conseq _ P' (Build_ret_assert (RA_normal R') (RA_break Post') (RA_continue R') (RA_return R'))).
    - exact H0.
    - rewrite <- H6; exact H1.
    - solve_andp. 
    - rewrite <- H8; exact H3.
    - intros. rewrite <- H7; apply H4.
    - apply IHsemax; auto.
  + constructor.
  + eapply semax_conseq;[..|apply semax_call].
    - apply derives_aux_refl.
    - rewrite H0. solve_andp.
    - intros. unfold normal_ret_assert. unfold_der.
      repeat apply andp_left2. apply FF_left.
    - rewrite H2. solve_andp.
    - rewrite H1. intros. solve_andp.
  + constructor. auto.
  + constructor.
  + constructor.
Qed.

Lemma semax_conj_skip: forall CS Espec Delta P Q Q1 Q2,
  @semax CS Espec Delta P Clight.Sskip (overridePost Q2 Q) ->
  @semax CS Espec Delta P Clight.Sskip (overridePost Q1 Q) ->
  @semax CS Espec Delta P Clight.Sskip (overridePost (Q1 && Q2) Q).
Proof.
  intros.
  destruct Q as [Qn Qb Qc Qr].
  unfold overridePost in *.
  apply semax_skip_inv in H0.
  apply semax_skip_inv in H.
  eapply semax_conseq with (P':= andp (Q1) (Q2))
  (R':= (normal_ret_assert (andp (Q1) (Q2)))); unfold normal_ret_assert.
  { apply andp_right;auto.
  }
  { unfold RA_normal.  solve_andp. }
  { unfold RA_break. repeat apply andp_left2. apply FF_left. }
  { unfold RA_continue. repeat apply andp_left2. apply FF_left. }
  { intros. unfold RA_return. repeat apply andp_left2. apply FF_left. }
  apply semax_skip.
Qed.

Lemma share_lub_writable: forall sh1 sh2,
  writable_share sh1 -> writable_share sh2 ->
  writable_share (Share.lub sh1 sh2).
Proof.
  intros. eapply join_writable1.
  2:{ apply H. }
  apply two_share_join.
Qed.


Lemma mapsto_join_andp_write_det_logic: forall sh1 sh2 t p P1 P2 v',
  tc_val t v' -> 
  writable_share sh1 -> writable_share sh2 ->
  (mapsto_ sh1 t p * (mapsto sh1 t p v' -* P1)) && 
  (mapsto_ sh2 t p * (mapsto sh2 t p v' -* P2))
  |--
  mapsto_ (Share.lub sh1 sh2) t p * (mapsto (Share.lub sh1 sh2) t p v' -* (P1 && P2)).
Proof.
  intros.
  apply mapsto_join_andp_write_det;auto.
Qed.

Lemma distrib_orp_andp2:
  forall (A : Type) (ND : NatDed A) (P Q R : A),
    R && (P || Q) = R && P || R && Q.
Proof.
  intros.
  rewrite andp_comm.
  rewrite distrib_orp_andp.
  rewrite andp_comm at 1.
  f_equal. rewrite andp_comm. reflexivity.
Qed.

Lemma semax_conj_assign: forall CS Espec Delta P Q Q1 Q2 e e0,
  @semax CS Espec Delta P (Clight.Sassign e e0) 
    (overridePost Q2 Q) ->
  @semax CS Espec Delta P (Clight.Sassign e e0) 
    (overridePost Q1 Q) ->
  @semax CS Espec Delta P (Clight.Sassign e e0) 
    (normal_ret_assert (Q1 && Q2)).
Proof.
  intros.
  destruct Q as [Qn Qb Qc Qr]. unfold_der.
  apply semax_assign_inv in H0.
  apply semax_assign_inv in H. unfold_der.
  eapply semax_conseq;
    [..|apply semax_assign with (P0:= Q1 && Q2)];
    unfold normal_ret_assert;unfold_der;try (intros; solve_andp).
  pose proof andp_ENTAILL _ _ _ _ _ H0 H.
  rewrite andp_dup in H1.
  eapply ENTAIL_trans;[apply H1|]. clear H1.
  Intros sh1. Intros sh2.
  Exists (Share.lub sh1 sh2).
  assert_PROPP (writable_share sh1). { solve_andp. }
  assert_PROPP (writable_share sh2). { solve_andp. }
  apply andp_right. {
    apply prop_right. apply share_lub_writable;auto. }
  eapply derives_trans with
  (Q:=
  local (tc_environ Delta) &&
  (|> (tc_lvalue Delta e && tc_expr Delta (Ecast e0 (typeof e)) &&
    ((` (mapsto_ sh1 (typeof e))) (eval_lvalue e) *
     ((` (mapsto sh1 (typeof e))) (eval_lvalue e)
        ((` force_val) ((` (sem_cast (typeof e0) (typeof e))) (eval_expr e0))) -*
      Q1))) &&
(
 |> (tc_lvalue Delta e && tc_expr Delta (Ecast e0 (typeof e)) &&
     ((` (mapsto_ sh2 (typeof e))) (eval_lvalue e) *
      ((` (mapsto sh2 (typeof e))) (eval_lvalue e)
         ((` force_val)
            ((` (sem_cast (typeof e0) (typeof e))) (eval_expr e0))) -* Q2)))))
  ); try solve_andp.
  rewrite <- later_andp.
  apply later_ENTAIL.
  repeat apply andp_right; try solve_andp.
  intros r.
  assert_PROPP (tc_val (typeof e)
  ((` force_val) ((` (sem_cast (typeof e0) (typeof e))) (eval_expr e0)) r)).
  { unfold tc_environ. simpl. unfold local.
    unfold lift1. Intros. apply derives_extract_prop. intros H3.
    eapply derives_trans;[| 
      apply (typecheck_expr_sound _ _ (Ecast e0 (typeof e)) H3)].
    solve_andp. }
  eapply derives_trans.
  2:{ eapply (mapsto_join_andp_write_det_logic _ _ (typeof e) ((eval_lvalue e) r) (Q1 r) (Q2 r) ((` force_val) ((` (sem_cast (typeof e0) (typeof e))) (eval_expr e0)) r));auto. } simpl.
  solve_andp.
Qed.

Lemma share_nonidentity_lub: forall sh1 sh2,
  sepalg.nonidentity sh1 -> sepalg.nonidentity sh2 ->
  sepalg.nonidentity (Share.lub sh1 sh2).
Proof.
  intros. intros C.
  apply identity_share_bot in C.
  apply lub_bot_e in C. apply H.
  destruct C. subst. apply bot_identity.
Qed.

Lemma mapsto__join_andp_det_logic:forall  sh1 sh2 t p,
readable_share sh1 -> readable_share sh2 ->
(mapsto_ sh1 t p * TT) && (mapsto_ sh2 t p * TT)
|-- (mapsto_ (Share.lub sh1 sh2) t p * TT).
Proof.
  intros.
  apply mapsto__join_andp_det;auto.
Qed.

Lemma mapsto_join_andp_det_logic: forall  sh1 sh2 t p v1 v2,
v1 <> Vundef -> v2 <> Vundef ->
readable_share sh1 -> readable_share sh2 ->
(mapsto sh1 t p v1 * TT) && (mapsto sh2 t p v2 * TT)
|-- (mapsto (Share.lub sh1 sh2) t p v1 * TT) && !!(v1 = v2).
Proof.
  intros.
  apply mapsto_join_andp_det;auto.
Qed.

Lemma mapsto_conj_der_mem: forall {CS:compspecs} Delta sh1 sh2 t e v1 v2 Q1 Q2 i,
readable_share sh1 -> readable_share sh2 ->
ENTAIL Delta,  local (` (tc_val t v1)) &&
((` (mapsto sh1 t)) (eval_lvalue e) (` v1) * TT) && subst i (` v1) Q1 &&
(tc_lvalue Delta e && local (` (tc_val t v2)) &&
 ((` (mapsto sh2 t)) (eval_lvalue e) (` v2) * TT) && subst i (` v2) Q2)
|-- tc_lvalue Delta e && local (` (tc_val t v1)) &&
    ((` (mapsto (Share.lub sh1 sh2) t)) (eval_lvalue e) (` v1) * TT) &&
    (subst i (` v1) Q1 && subst i (` v1) Q2).
Proof.
  intros.
  assert_PROPP (v1 <> Vundef).
  { destruct (eq_dec v1 Vundef).
    { subst. unfold local. unfold lift1. simpl. intros.
      assert_PROPP (tc_val t Vundef). { solve_andp. } 
      apply tc_val_Vundef in H1. tauto. }
    apply prop_right. auto. }
  assert_PROPP (v2 <> Vundef).
  { destruct (eq_dec v2 Vundef).
    { subst. unfold local. unfold lift1. simpl. intros.
      assert_PROPP (tc_val t Vundef). { solve_andp. }
      apply tc_val_Vundef in H2. tauto. }
    apply prop_right. auto. }
  unfold liftx. simpl. unfold lift. intros r.
  pose proof mapsto_join_andp_det_logic 
    sh1 sh2 t (eval_lvalue e r) v1 v2 H1 H2 H H0.
  eapply derives_trans.
  { apply andp_right.
    + eapply derives_trans. 2:{ apply H3. }
      solve_andp.
    + apply derives_refl.
  }
  assert_PROPP (v1 = v2). { solve_andp. } subst.
  solve_andp.
Qed.

Require Import VST.veric.semax_straight.

Lemma mapsto_conj_der_mem2: forall {CS:compspecs} Delta sh1 sh2 t2 e2 v1 v2 Q1 Q2 i,
readable_share sh1 -> readable_share sh2 ->
  ENTAIL Delta,
  tc_lvalue Delta e2 &&
  local ((` (tc_val t2)) (` (eval_cast (typeof e2) t2 v1))) &&
  ((` (mapsto sh1 (typeof e2))) (eval_lvalue e2) (` v1) * TT) &&
  subst i (` (force_val (sem_cast (typeof e2) t2 v1))) Q1 &&
  (tc_lvalue Delta e2 &&
  local ((` (tc_val t2)) (` (eval_cast (typeof e2) t2 v2))) &&
  ((` (mapsto sh2 (typeof e2))) (eval_lvalue e2) (` v2) * TT) &&
  subst i (` (force_val (sem_cast (typeof e2) t2 v2))) Q2)
  |-- tc_lvalue Delta e2 &&
      local ((` (tc_val t2)) (` (eval_cast (typeof e2) t2 v1))) &&
      ((` (mapsto (Share.lub sh1 sh2) (typeof e2))) (eval_lvalue e2) (` v1) *
      TT) &&
      (subst i (` (force_val (sem_cast (typeof e2) t2 v1))) Q1 &&
      subst i (` (force_val (sem_cast (typeof e2) t2 v1))) Q2).
Proof.
  intros.
  destruct (eq_dec v1 Vundef).
  { subst. rewrite semax_straight.eval_cast_Vundef.
    unfold local. unfold lift1. simpl. intros.
    assert_PROPP (tc_val t2 Vundef). { solve_andp. }
    apply tc_val_Vundef in H1. tauto. }
  destruct (eq_dec v2 Vundef).
  { subst. rewrite semax_straight.eval_cast_Vundef.
    unfold local. unfold lift1. simpl. intros.
    assert_PROPP (tc_val t2 Vundef). { solve_andp. }
    apply tc_val_Vundef in H1. tauto. }
  unfold liftx. simpl. unfold lift. intros r.
  pose proof mapsto_join_andp_det_logic 
    sh1 sh2 (typeof e2) (eval_lvalue e2 r) v1 v2 n n0 H H0.
  eapply derives_trans.
  { apply andp_right.
    + eapply derives_trans. 2:{ apply H1. } solve_andp.
    + apply derives_refl.
  }
  assert_PROPP (v1 = v2). { solve_andp. }
  Intros. subst.
  solve_andp.
Qed.

Lemma eval_lvalue_expr_contra: forall {CS:compspecs} Delta e,
  access_mode (typeof e) <> By_reference ->
  tc_expr Delta e && tc_lvalue Delta e |-- FF.
Proof.
  intros. rename H into Ht. induction e;
  unfold tc_expr; unfold typecheck_expr; unfold tc_lvalue; unfold typecheck_lvalue;
  simpl; intros r; unfold liftx; simpl; unfold lift; try solve [apply derives_extract_prop'; intros H; inv H].
  (* + apply derives_extract_prop. intros. inv H. *)
  + destruct (access_mode t) eqn:E;simpl;
    unfold liftx; simpl; unfold lift; try solve [
      apply derives_extract_prop; intros H; inv H].
    destruct (get_var_type Delta i ) eqn:E1;simpl.
    2:{ apply derives_extract_prop. intros. inv H. }
    (* rewrite denote_tc_assert_bool. *)
    simpl in Ht. contradiction.
  + destruct (access_mode t) eqn:E;simpl;
    unfold liftx; simpl; unfold lift; try solve [apply derives_extract_prop; intros H; inv H].
    simpl in Ht. contradiction.
  + destruct (access_mode t) eqn:E;simpl;
    unfold liftx; simpl; unfold lift; try solve [apply derives_extract_prop; intros H; inv H].
    simpl in Ht. contradiction.
Qed.

Lemma eval_cast_expr_contra: forall {CS:compspecs} Delta e1 t1,
  access_mode (typeof e1) <> By_reference ->
  tc_expr Delta (Ecast e1 t1) && tc_lvalue Delta e1 |-- FF .
Proof.
  intros. rename H into Ht. induction e1;
  unfold tc_expr; unfold typecheck_expr; unfold tc_lvalue; unfold typecheck_lvalue;
  simpl; intros r; unfold liftx; simpl; unfold lift; try solve [apply derives_extract_prop'; intros H; inv H].
  (* + apply derives_extract_prop. intros. inv H. *)
  + destruct (access_mode t) eqn:E;simpl;
    unfold liftx; simpl; unfold lift; try solve [apply derives_extract_prop; intros H; inv H].
    destruct (get_var_type Delta i ) eqn:E1;simpl.
    2:{ apply derives_extract_prop. intros. inv H. }
    (* rewrite denote_tc_assert_bool. *)
    simpl in Ht. contradiction.
  + destruct (access_mode t) eqn:E;simpl;
    unfold liftx; simpl; unfold lift; try solve [apply derives_extract_prop; intros H; inv H].
    simpl in Ht. contradiction.
  + destruct (access_mode t) eqn:E;simpl;
    unfold liftx; simpl; unfold lift; try solve [apply derives_extract_prop; intros H; inv H].
    simpl in Ht. contradiction.
Qed.

Lemma type_is_by_value_sem: forall e, 
  type_is_by_value (typeof e) = true ->
  access_mode (typeof e) <> By_reference.
Proof.
  intros. intros C.
  destruct (typeof e); simpl in H, C; try congruence.
  + destruct i, s; try congruence.
  + destruct f; try congruence.
Qed.

Lemma eval_cast_lvalue_contra: forall {CS:compspecs} Delta e1 t1,
  tc_lvalue Delta (Ecast e1 t1) && tc_lvalue Delta e1 |-- FF .
Proof.
  intros. induction e1;
  unfold tc_expr; unfold typecheck_expr; unfold tc_lvalue; unfold typecheck_lvalue;
  simpl; intros r; unfold liftx; simpl; unfold lift; try solve [apply derives_extract_prop'; intros H; inv H];
  try solve [apply derives_extract_prop; intros C; inv C].
Qed.


Lemma is_neutral_cast_by_value: forall t t',
  is_neutral_cast t t' = true ->
  type_is_by_value t = true.
Proof.
  intros.
  destruct t, t'; try inversion H; simpl; auto.
Qed.

Lemma derives_extract_prop'': forall Delta (P: Prop) Q R,
  (P -> ENTAIL Delta, Q |-- R) ->
  ENTAIL Delta, !! P && Q |-- R.
Proof.
  intros.
  assert_PROPP P. { solve_andp. }
  eapply derives_trans;[|apply H];auto.
  solve_andp.
Qed.


Lemma semax_conj_set: forall CS Espec Delta P Q Q1 Q2 i e,
  @semax CS Espec Delta P (Clight.Sset i e) 
    (overridePost Q2 Q) ->
  @semax CS Espec Delta P (Clight.Sset i e) 
    (overridePost Q1 Q) ->
  @semax CS Espec Delta P (Clight.Sset i e) 
    (normal_ret_assert (Q1 && Q2)).
Proof.
  intros.
  destruct Q as [Qn Qb Qc Qr]. unfold_der.
  apply semax_set_inv in H0.
  apply semax_set_inv in H. unfold_der.
  eapply semax_conseq;
    [..|apply semax_set_ptr_compare_load_cast_load_backward
       with (P0:= Q1 && Q2)];
  unfold normal_ret_assert;unfold_der;try (intros; solve_andp).  pose proof andp_ENTAILL _ _ _ _ _ H0 H.
  rewrite andp_dup in H1.
  eapply ENTAIL_trans;[apply H1|]. clear H1.
  rewrite !distrib_orp_andp. repeat apply orp_ENTAIL.
  - rewrite <- andp_assoc. rewrite !distrib_orp_andp2.
    repeat apply orp_left; rewrite andp_assoc.
    + rewrite subst_andp. rewrite <- later_andp.
      apply later_ENTAIL. solve_andp.
    + Intros sh t2 v2.
      assert_PROPP (typeof_temp Delta i = Some t2 /\
      is_neutral_cast (typeof e) t2 = true /\ readable_share sh).
      { solve_andp. }
      destruct H1 as [? [H2 ?]].
      pose proof is_neutral_cast_by_value _ _ H2.
      apply type_is_by_value_sem in H4.
      eapply derives_trans with (Q:=
      local (tc_environ Delta) && (
|> (tc_expr Delta e && tc_temp_id i (typeof e) Delta e &&
    subst i (eval_expr e) Q1) &&
(
 |> (tc_lvalue Delta e && local (` (tc_val (typeof e) v2)) &&
     ((` (mapsto sh (typeof e))) (eval_lvalue e) (` v2) * TT) &&
     subst i (` v2) Q2))
      )); try solve_andp.
      rewrite <- later_andp. apply later_ENTAIL.
      eapply derives_trans with (Q:= tc_expr Delta e && tc_lvalue Delta e); try solve_andp.
      eapply derives_trans with (Q:= FF).
      2:{ apply FF_left. }
      apply eval_lvalue_expr_contra; auto.
    + Intros sh e1 t1 v2.
      assert_PROPP ((e = Ecast e1 t1 /\
      typeof_temp Delta i = Some t1 /\
      cast_pointer_to_bool (typeof e1) t1 = false /\ readable_share sh)).
      { solve_andp. }
      destruct H1 as [? [? [? ?]]].
      eapply derives_trans with (Q:=
      local (tc_environ Delta) &&
      (|> (tc_expr Delta e && tc_temp_id i (typeof e) Delta e &&
    subst i (eval_expr e) Q1) &&
(|> (tc_lvalue Delta e1 &&
     local ((` (tc_val t1)) (` (eval_cast (typeof e1) t1 v2))) &&
     ((` (mapsto sh (typeof e1))) (eval_lvalue e1) (` v2) * TT) &&
     subst i (` (force_val (sem_cast (typeof e1) t1 v2))) Q2))
      )). { solve_andp. }
      rewrite <- later_andp. apply later_ENTAIL.
      assert_PROPP (access_mode (typeof e1) <> By_reference).
      { destruct (typeof e1) eqn:E0; simpl; simpl in H3; intros r; try solve [apply prop_right;intros C;inv C].
        + destruct i0, s; try solve [apply prop_right;intros C;inv C].
        + destruct f; try try solve [apply prop_right;intros C;inv C].
        + unfold mapsto. simpl. unfold liftx. simpl.  unfold lift. unfold local.
          unfold lift1. simpl. rewrite FF_sepcon. eapply derives_trans with (Q:=FF); try solve_andp.
          apply FF_left.
        + unfold mapsto. simpl. unfold liftx. simpl.  unfold lift. unfold local.
          unfold lift1. simpl. rewrite FF_sepcon. eapply derives_trans with (Q:=FF); try solve_andp.
          apply FF_left. }
      subst e. 
      eapply derives_trans with (Q:= tc_expr Delta (Ecast e1 t1) && tc_lvalue Delta e1); try solve_andp.
      eapply derives_trans with (Q:= FF);try apply FF_left.
      apply eval_cast_expr_contra;auto.
  - rewrite <- andp_assoc. rewrite !distrib_orp_andp2.
    repeat apply orp_left; rewrite andp_assoc.
    + Intros sh t1 v1. Exists sh t1 v1.
      rewrite andp_assoc.
      apply derives_extract_prop''.
      intros [? [? ?]].
      apply andp_right.
      { apply prop_right. auto. }
      pose proof is_neutral_cast_by_value _ _ H2.
      apply type_is_by_value_sem in H4.
      rewrite <- later_andp. apply later_ENTAIL.
      eapply derives_trans with (Q:= tc_expr Delta e && tc_lvalue Delta e); try solve_andp.
      eapply derives_trans with (Q:=FF).
      2:{ apply FF_left. }
      apply eval_lvalue_expr_contra; auto.
    + Intros sh1 t1 v1. Intros sh2 t2 v2.
      rewrite andp_assoc.
      apply derives_extract_prop''.
      intros [? [? ?]].
      rewrite <- andp_assoc.
      rewrite andp_comm. rewrite ! andp_assoc.
      apply derives_extract_prop.
      intros [? [? ?]].
      rewrite H1 in H4. inv H4. Exists (Share.lub sh1 sh2) t2 v1.
      rewrite andp_comm. rewrite andp_assoc.
      rewrite <- later_andp. apply andp_right.
      { apply prop_right. repeat split;auto.
      apply readable_share_lub. auto. }
      apply later_ENTAIL. rewrite subst_andp.
      eapply derives_trans.
      2:{ apply mapsto_conj_der_mem with (v4:=v2);auto. }
      solve_andp.
    + Intros sh1 t1 v1. Intros sh2 e2 t2 v2. Exists sh1 t1 v1.
      rewrite andp_assoc.
      apply derives_extract_prop''.
      intros [? [? ?]].
      rewrite <- andp_assoc.
      rewrite andp_comm. rewrite ! andp_assoc.
      apply derives_extract_prop.
      intros [? [? [? ?]]].
      rewrite andp_comm. rewrite andp_assoc.
      rewrite <- later_andp. apply andp_right.
      { apply prop_right. repeat split;auto. }
      apply later_ENTAIL.
      eapply derives_trans with (Q:= tc_lvalue Delta e && tc_lvalue Delta e2); try solve_andp.
      subst e. eapply derives_trans with (Q:=FF); try apply FF_left.
      apply eval_cast_lvalue_contra.
  - rewrite <- andp_assoc. rewrite !distrib_orp_andp2.
    repeat apply orp_left; rewrite andp_assoc.
    + Intros sh e2 t2 v2. Exists sh e2 t2 v2. 
      rewrite andp_assoc.
      apply derives_extract_prop''.
      intros [? [? [? ?]]].
      rewrite <- later_andp.
      apply andp_right. { apply prop_right;auto. }
      apply later_ENTAIL.
      assert_PROPP (access_mode (typeof e2) <> By_reference).
      { destruct (typeof e2) eqn:E0; simpl; simpl in H3; intros r; try solve [apply prop_right;intros C;inv C].
        + destruct i0, s; try solve [apply prop_right;intros C;inv C].
        + destruct f; try try solve [apply prop_right;intros C;inv C].
        + unfold mapsto. simpl. unfold liftx. simpl.  unfold lift. unfold local.
          unfold lift1. simpl. rewrite FF_sepcon. eapply derives_trans with (Q:=FF); try solve_andp.
          apply FF_left.
        + unfold mapsto. simpl. unfold liftx. simpl.  unfold lift. unfold local.
          unfold lift1. simpl. rewrite FF_sepcon. eapply derives_trans with (Q:=FF); try solve_andp.
          apply FF_left. }
      subst e. 
      eapply derives_trans with (Q:= tc_expr Delta (Ecast e2 t2) && tc_lvalue Delta e2); try solve_andp.
      eapply derives_trans with (Q:= FF);try apply FF_left.
      apply eval_cast_expr_contra;auto.
    + Intros sh1 e1 t1 v1. Intros sh2 t2 v2. Exists sh1 e1 t1 v1.
      rewrite andp_assoc.
      apply derives_extract_prop''.
      intros [? [? [? ? ]]].
      rewrite <- andp_assoc.
      rewrite andp_comm. rewrite ! andp_assoc.
      apply derives_extract_prop.
      intros [? [? ?]].
      rewrite andp_comm. rewrite andp_assoc.
      rewrite <- later_andp. apply andp_right.
      { apply prop_right. repeat split;auto. }
      apply later_ENTAIL.
      eapply derives_trans with (Q:= tc_lvalue Delta e && tc_lvalue Delta e1); try solve_andp.
      subst e. eapply derives_trans with (Q:=FF); try apply FF_left.
      apply eval_cast_lvalue_contra.
    + Intros sh1 e1 t1 v1. Intros sh2 e2 t2 v2.
      rewrite andp_assoc.
      apply derives_extract_prop''.
      intros [? [? [? ?]]].
      rewrite <- andp_assoc.
      rewrite andp_comm. rewrite ! andp_assoc.
      apply derives_extract_prop.
      intros [? [? [? ?]]].
      rewrite andp_comm. rewrite andp_assoc.
      rewrite H2 in H6. inv H6.
      assert (e1 = e2).
      { destruct t2; inv H5; reflexivity. }
      subst e1.
      Exists (Share.lub sh1 sh2) e2 t2 v1.
      rewrite <- later_andp. apply andp_right.
      { apply prop_right. repeat split;auto.
        apply readable_share_lub. auto. }
      apply later_ENTAIL. rewrite subst_andp.
      eapply derives_trans.
      2:{ apply mapsto_conj_der_mem2 with (v4:=v2);auto. }
      solve_andp.
Qed.


Lemma semax_loop_inv: forall {CS: compspecs} {Espec: OracleKind} Delta P R body incr,
  @semax CS Espec Delta P (Clight.Sloop body incr) R ->
  local (tc_environ Delta) && (allp_fun_id Delta && P) |--
   EX Q: environ -> mpred, EX Q': environ -> mpred,
  !! (@semax CS Espec Delta Q body (loop1_ret_assert Q' R) /\
      @semax CS Espec Delta Q' incr (loop2_ret_assert Q R)) &&
  Q.
Proof.
  intros.
  remember (Clight.Sloop body incr) as c eqn:?H.
  induction H; try solve [inv H0].
  + inv H0; clear IHsemax1 IHsemax2.
    reduce2derives.
    apply (exp_right Q).
    apply (exp_right Q').
    apply andp_right; [apply prop_right; auto |].
    auto.
  + eapply derives_trans.
    2:{
      derives_rewrite -> (IHsemax H0); clear IHsemax.
      reduce2derives.
      apply exp_derives; intros Q.
      apply exp_derives; intros Q'.
      normalize. destruct H6.
      apply andp_right; [apply prop_right |]; auto.
      split.
      - destruct R as [nR bR cR rR], R' as [nR' bR' cR' rR']; simpl in H6, H7 |- *.
        simpl RA_normal in H1; simpl RA_break in H2; simpl RA_continue in H3; simpl RA_return in H4.
        eapply semax_conseq; [.. | eassumption]; unfold loop1_ret_assert; unfold_der; try solve [intros;solve_andp];auto.
      - destruct R as [nR bR cR rR], R' as [nR' bR' cR' rR']; simpl in H6, H7 |- *.
        simpl RA_normal in H1; simpl RA_break in H2; simpl RA_continue in H3; simpl RA_return in H4.
        eapply semax_conseq; [.. | eassumption]; unfold loop1_ret_assert;
        unfold_der; try solve [intros;solve_andp];auto.
    }
    { rewrite (add_andp _ _ H). solve_andp. }
Qed.


Lemma semax_break_inv: forall {CS: compspecs} {Espec: OracleKind} Delta P R,
    @semax CS Espec Delta P Clight.Sbreak R ->
    local (tc_environ Delta) && (allp_fun_id Delta && P) |-- RA_break R.
Proof.
  intros.
  remember Clight.Sbreak as c eqn:?H.
  induction H; try solve [inv H0].
  + solve_andp.
  + specialize (IHsemax H0).
    rewrite (add_andp _ _ H).
    eapply derives_trans;[|apply H2].
    repeat apply andp_right;try solve_andp.
    eapply derives_trans;[|apply IHsemax]. solve_andp.
Qed.

Lemma semax_continue_inv: forall {CS: compspecs} {Espec: OracleKind} Delta P R,
    @semax CS Espec Delta P Clight.Scontinue R ->
    local (tc_environ Delta) && (allp_fun_id Delta && P) |--  RA_continue R.
Proof.
  intros.
  remember Clight.Scontinue as c eqn:?H.
  induction H; try solve [inv H0].
  + solve_andp.
  + specialize (IHsemax H0).
    rewrite (add_andp _ _ H).
    eapply derives_trans;[|apply H3].
    repeat apply andp_right;try solve_andp.
    eapply derives_trans;[|apply IHsemax]. solve_andp.
Qed.


Lemma semax_return_inv: forall {CS: compspecs} {Espec: OracleKind} Delta P ret R,
  @semax CS Espec Delta P (Clight.Sreturn ret) R ->
  local (tc_environ Delta) && (allp_fun_id Delta && P) |-- 
  ((tc_expropt Delta ret (ret_type Delta)) && 
  `(RA_return R : option val -> environ -> mpred) (cast_expropt ret (ret_type Delta)) (@id environ)).
Proof.
  intros.
  remember (Clight.Sreturn ret) as c eqn:?H.
  induction H; try solve [inv H0].
  + inv H0. solve_andp.
  + eapply derives_trans.
    { apply andp_right;[|apply H].
      rewrite <- andp_assoc.  apply andp_left1. apply derives_refl.
    }
    rewrite andp_assoc.
    eapply derives_trans.
    { apply andp_right;[|apply (IHsemax H0)].
      rewrite <- andp_assoc.  apply andp_left1. apply derives_refl.
    }
    rewrite andp_assoc.
    apply andp_ENTAILL; [solve_andp |].
    unfold_lift.
    intro rho.
    simpl.
    forget (cast_expropt ret (ret_type Delta) rho) as vl.
    revert rho.
    change (local (tc_environ Delta) && (allp_fun_id Delta && (RA_return R' vl)) |-- RA_return R vl).
    auto.
Qed.

Lemma semax_ifthenelse_inv: forall {CS: compspecs} {Espec: OracleKind} Delta P R b c1 c2,
  @semax CS Espec Delta P (Clight.Sifthenelse b c1 c2) R ->
  local (tc_environ Delta) && (allp_fun_id Delta && P) |--
   (!! (bool_type (typeof b) = true) && tc_expr Delta (Eunop Cop.Onotbool b (Tint I32 Signed noattr)) &&
  EX P': environ -> mpred,
  !! (@semax CS Espec Delta (P' && local (`(typed_true (typeof b)) (eval_expr b))) c1 R /\
      @semax CS Espec Delta (P' && local (`(typed_false (typeof b)) (eval_expr b))) c2 R) &&
  P').
Proof.
  intros.
  remember (Clight.Sifthenelse b c1 c2) as c eqn:?H.
  induction H; try solve [inv H0].
  + inv H0; clear IHsemax1 IHsemax2.
    reduce2derives.
    apply andp_derives; auto.
    apply (exp_right P).
    apply andp_right; [apply prop_right; auto |].
    auto.
  + eapply derives_trans with (Q:= local (tc_environ Delta) && (allp_fun_id Delta && P')).
    { repeat apply andp_right;try solve_andp. derives_rewrite -> H. solve_andp. }
    derives_rewrite -> (IHsemax H0). clear IHsemax.
    reduce2derives.
    apply andp_derives; auto.
    apply exp_derives; intros P''.
    normalize.
    apply andp_right; auto.
    apply prop_right. destruct H6.
    split.
    - eapply semax_conseq; try eassumption. solve_andp.
    - eapply semax_conseq; try eassumption. solve_andp.
Qed.

Lemma semax_post'': forall (R' : environ -> mpred) (Espec:OracleKind)
      (cs : compspecs) (Delta : tycontext) (R : ret_assert)
      (P : environ -> mpred) (c : Clight.statement),
    local (tc_environ Delta) && R' |-- RA_normal R ->
    semax Delta P c (normal_ret_assert R') ->
    semax Delta P c R.
Proof.
  intros. destruct R.
  eapply semax_conseq;[..|apply H0];try solve_andp;
  unfold_der;try solve_andp.
  - eapply derives_trans;[|apply H]. solve_andp.
  - apply andp_left2;apply andp_left2;apply FF_left.
  - apply andp_left2;apply andp_left2;apply FF_left.
  - intros. apply andp_left2;apply andp_left2;apply FF_left.
Qed.

Lemma semax_pre : forall (P' : environ -> mpred) (Espec : OracleKind) 
         (cs : compspecs) (Delta : tycontext) (P : environ -> mpred)
         (c : Clight.statement) (R : ret_assert),
  ENTAIL Delta, P |-- P' ->
  semax Delta P' c R -> semax Delta P c R.
Proof.
  intros. eapply semax_conseq;[..|apply H0]; try solve [intros;solve_andp].
  eapply derives_trans;[|apply H]. solve_andp.
Qed.

Lemma semax_pre' : forall (P' : environ -> mpred) (Espec : OracleKind) 
         (cs : compspecs) (Delta : tycontext) (P : environ -> mpred)
         (c : Clight.statement) (R : ret_assert),
  ENTAIL Delta, allp_fun_id Delta && P |-- P' ->
  semax Delta P' c R -> semax Delta P c R.
Proof.
  intros. eapply semax_conseq;[..|apply H0]; try solve [intros;solve_andp].
  eapply derives_trans;[|apply H]. solve_andp.
Qed.


Lemma semax_builtin_inv: forall {CS: compspecs} {Espec: OracleKind} 
  Delta opt ext tl el Pre Post,
  @semax CS Espec Delta Pre (Clight.Sbuiltin opt ext tl el) Post ->
  local (tc_environ Delta) && (allp_fun_id Delta && Pre) |-- FF.
Proof.
  intros. 
  remember (Clight.Sbuiltin opt ext tl el) as c1.
  induction H; try inversion Heqc1.
  - subst. specialize (IHsemax eq_refl).
    eapply derives_trans.
    2:{ apply IHsemax. }
    rewrite (add_andp _ _ H). solve_andp.
  - solve_andp.
Qed.

Lemma semax_goto_inv: forall {CS: compspecs} {Espec: OracleKind} 
  Delta l Pre Post,
  @semax CS Espec Delta Pre (Clight.Sgoto l) Post ->
  local (tc_environ Delta) && (allp_fun_id Delta && Pre) |-- FF.
Proof.
  intros. 
  remember (Clight.Sgoto l) as c1.
  induction H; try inversion Heqc1.
  - subst. specialize (IHsemax eq_refl).
    eapply derives_trans.
    2:{ apply IHsemax. }
    rewrite (add_andp _ _ H). solve_andp.
  - solve_andp.
Qed.

Lemma semax_switch_inv: forall {CS: compspecs} {Espec: OracleKind} 
  Delta a sl Pre Post,
  @semax CS Espec Delta Pre (Clight.Sswitch a sl) Post ->
  local (tc_environ Delta) && (allp_fun_id Delta && Pre) |-- FF.
Proof.
  intros. 
  remember (Clight.Sswitch a sl) as c1.
  induction H; try inversion Heqc1.
  - subst. specialize (IHsemax eq_refl).
    eapply derives_trans.
    2:{ apply IHsemax. }
    rewrite (add_andp _ _ H). solve_andp.
  - solve_andp.
Qed.

Lemma semax_post_simple: forall (R' : ret_assert) (Espec : OracleKind) 
      (cs : compspecs) (Delta : tycontext) (R : ret_assert)
      (P : environ -> mpred) (c : Clight.statement),
    RA_normal R' |-- RA_normal R ->
    RA_break R' |-- RA_break R ->
    RA_continue R' |-- RA_continue R ->
    (forall vl : option val, RA_return R' vl |-- RA_return R vl) ->
    semax Delta P c R' ->
    semax Delta P c R.
Proof.
  intros.
  eapply semax_conseq;[..|apply H3].
  - solve_andp.
  - rewrite (add_andp _ _ H);solve_andp.
  - rewrite (add_andp _ _ H0);solve_andp.
  - rewrite (add_andp _ _ H1);solve_andp.
  - intros. rewrite (add_andp _ _ (H2 vl));solve_andp.
Qed.


Lemma semax_label_inv: forall {CS: compspecs} {Espec: OracleKind} Delta P R l c,
  @semax CS Espec Delta P (Clight.Slabel l c) R -> @semax CS Espec Delta P c R.
Proof.
  intros.
  remember (Clight.Slabel l c) as c0 eqn:?H.
  induction H; try solve [inv H0].
  + specialize (IHsemax H0).
    eapply semax_conseq; eauto.
  + inv H0.
    apply H.
Qed.

(* 
Ltac induction_stmt s :=
  revert dependent s;
  let s1 := fresh s "1" in
  let s2 := fresh s "2" in
  let IHs := fresh "IH" s in
  let IHs1 := fresh "IH" s1 in
  let IHs2 := fresh "IH" s2 in
  refine (statement_ind _ _ _ _ _ _ _ _ _ _ _ _ _ _ _);
  [
  | intros ?e ?e
  | intros ?i ?e
  | intros ?o ?e ?l
  | intros ?o ?e ?t ?l
  | intros s1 IHs1 s2 IHs2
  | intros ?e s1 IHs1 s2 IHs2
  | intros s1 IHs1 s2 IHs2
  |
  |
  | intros ?o
  | intros ?e ?l ?IH; specialize (all_suf_select_switch _ _ IH); clear IH; intro IH; cbv beta in IH
  | intros ?l s IHs
  | intros ?l ]. *)

Lemma semax_extract_exists:
  forall {CS: compspecs} {Espec: OracleKind},
  forall (A : Type)  (P : A -> environ->mpred) c (Delta: tycontext) (R: ret_assert),
  (forall x, @semax CS Espec Delta (P x) c R) ->
   @semax CS Espec Delta (EX x:A, P x) c R.
Proof.
intros.
  revert A P R H; induction c; intros.
  + pose proof (fun x => semax_skip_inv _ _ _ _ _ (H x)).
    eapply semax_conseq with (R':=R).
    - rewrite !exp_andp2; apply exp_left.
      intro x. specialize (H0 x). apply H0.
    - solve_andp.
    - solve_andp.
    - solve_andp.
    - intros; solve_andp.
    - apply semax_post'' with (R':=(RA_normal R)); 
      [.. | apply semax_skip].
      solve_andp.
  + pose proof (fun x => semax_assign_inv _ _ _ _ _ (H x)).
    clear H.
    apply exp_left in H0.
    rewrite <- !(exp_andp2 A) in H0.
    eapply semax_conseq; [exact H0 | intros; solve_andp .. | clear H0 ].
    eapply semax_conseq; [apply derives_aux_refl | .. | apply semax_assign].
    - reduceL. apply derives_refl.
    - reduceL. apply FF_left.
    - reduceL. apply FF_left.
    - intros; reduceL. apply FF_left.
  + pose proof (fun x => semax_set_inv _ _ _ _ _ (H x)).
    clear H.
    apply exp_left in H0.
    rewrite <- !(exp_andp2 A) in H0.
    eapply semax_conseq; [exact H0 | intros; apply derives_aux_refl .. | clear H0 ].
    eapply semax_conseq; [apply derives_aux_refl | .. | apply semax_set_ptr_compare_load_cast_load_backward].
    - reduceL. apply derives_refl.
    - reduceL. apply FF_left.
    - reduceL. apply FF_left.
    - intros; reduceL. apply FF_left.
  + pose proof (fun x => semax_call_inv _ _ _ _ _ _ (H x)).
    eapply semax_conseq; [ .. | apply semax_call].
    - rewrite !exp_andp2.
      apply exp_left; intros x; specialize (H0 x).
      apply H0.
    - reduceL. apply derives_refl.
    - reduceL. apply FF_left.
    - reduceL. apply FF_left.
    - intros; reduceL. apply FF_left.
  + pose proof (fun x => semax_builtin_inv _ _ _ _ _ _ _ (H x)).
    eapply semax_conseq; [| intros; apply derives_aux_refl .. | apply semax_builtin].
    rewrite !exp_andp2.
    apply exp_left; intros x; specialize (H0 x).
    auto.
  + apply semax_seq with (EX Q: environ -> mpred, !! (semax Delta Q c2 R) && Q).
    - apply IHc1.
      intro x. apply semax_seq_inv';auto.
    - apply IHc2.
      intros Q. 
      apply semax_pre with (EX H0: semax Delta Q c2 R, Q).
      * apply andp_left2.
        apply derives_extract_prop; intros.
        apply (exp_right H0).
        auto.
      * apply IHc2.
        intro H0.
        auto.
  + eapply semax_conseq; [| intros; apply derives_aux_refl .. | apply (semax_ifthenelse _ (EX P': environ -> mpred, !! (semax Delta (P' && local (`(typed_true (typeof e)) (eval_expr e))) c1 R /\ semax Delta (P' && local (`(typed_false (typeof e)) (eval_expr e))) c2 R) && P'))].
    - pose proof (fun x => semax_ifthenelse_inv _ _ _ _ _ _ (H x)).
      clear H.
      apply exp_left in H0.
      rewrite <- !(exp_andp2 A) in H0.
      exact H0.
    - rewrite exp_andp1.
      apply IHc1.
      intro P'.
      apply semax_pre with (EX H0: semax Delta (P' && local ((` (typed_true (typeof e))) (eval_expr e))) c1 R, P' && local ((` (typed_true (typeof e))) (eval_expr e))).
      * apply andp_left2.
        rewrite !andp_assoc.
        apply derives_extract_prop; intros.
        apply (exp_right (proj1 H0)).
        solve_andp.
      * apply IHc1.
        intro H0.
        auto.
    - rewrite exp_andp1.
      apply IHc2.
      intro P'.
      apply semax_pre with (EX H0: semax Delta (P' && local ((` (typed_false (typeof e))) (eval_expr e))) c2 R, P' && local ((` (typed_false (typeof e))) (eval_expr e))).
      * apply andp_left2.
        rewrite !andp_assoc.
        apply derives_extract_prop; intros.
        apply (exp_right (proj2 H0)).
        solve_andp.
      * apply IHc2.
        intro H0.
        auto.
  + pose proof (fun x => semax_loop_inv _ _ _ _ _ (H x)).
    eapply (semax_conseq _ 
      (EX Q : environ -> mpred, EX Q' : environ -> mpred,
          EX H: semax Delta Q c1 (loop1_ret_assert Q' R),
            EX H0: semax Delta Q' c2 (loop2_ret_assert Q R), Q));
    [| intros; apply derives_aux_refl .. |].
    {
      rewrite !exp_andp2.
      apply exp_left.
      intros x.
      derives_rewrite -> (H0 x).
      reduce2derives.
      apply exp_derives; intros Q.
      apply exp_derives; intros Q'.
      apply derives_extract_prop; intros [? ?].
      apply (exp_right H1).
      apply (exp_right H2).
      auto.
    }
    apply (semax_loop _ _
      (EX Q : environ -> mpred, EX Q' : environ -> mpred,
          EX H: semax Delta Q c1 (loop1_ret_assert Q' R),
            EX H0: semax Delta Q' c2 (loop2_ret_assert Q R), Q')).
    - apply IHc1.
      intros Q.
      apply IHc1.
      intros Q'.
      apply IHc1.
      intros ?H.
      apply IHc1.
      intros ?H.
      eapply semax_post_simple; [.. | exact H1].
      * destruct R as [nR bR cR rR].
        unfold loop1_ret_assert.
        apply (exp_right Q), (exp_right Q'), (exp_right H1), (exp_right H2).
        apply derives_refl.
      * destruct R as [nR bR cR rR].
        apply derives_refl.
      * destruct R as [nR bR cR rR].
        unfold loop1_ret_assert.
        apply (exp_right Q), (exp_right Q'), (exp_right H1), (exp_right H2).
        apply derives_refl.
      * intros.
        destruct R as [nR bR cR rR].
        apply derives_refl.
    - apply IHc2.
      intros Q.
      apply IHc2.
      intros Q'.
      apply IHc2.
      intros ?H.
      apply IHc2.
      intros ?H.
      eapply semax_post_simple; [.. | exact H2].
      * destruct R as [nR bR cR rR].
        unfold loop1_ret_assert.
        apply (exp_right Q), (exp_right Q'), (exp_right H1), (exp_right H2).
        apply derives_refl.
      * destruct R as [nR bR cR rR].
        apply derives_refl.
      * destruct R as [nR bR cR rR].
        apply derives_refl.
      * intros.
        destruct R as [nR bR cR rR].
        apply derives_refl.
  + pose proof (fun x => semax_break_inv _ _ _ (H x)).
    eapply semax_conseq; [| intros; apply derives_aux_refl .. |].
    - rewrite !exp_andp2; apply exp_left.
      intro x; apply H0.
    - apply semax_break.
  + pose proof (fun x => semax_continue_inv _ _ _ (H x)).
    eapply semax_conseq; [| intros; apply derives_aux_refl .. |].
    - rewrite !exp_andp2; apply exp_left.
      intro x; apply H0.
    - apply semax_continue.
  + pose proof (fun x => semax_return_inv _ _ _ _ (H x)).
    eapply (semax_conseq _ _ {| RA_normal := _; RA_break := _; RA_continue := _; RA_return := RA_return R |}); [.. | apply semax_return].
    - rewrite !exp_andp2.
      apply exp_left; intros x.
      eapply derives_trans.
      { apply andp_right;[|apply (H0 x)].
        rewrite <- andp_assoc. apply andp_left1. apply derives_refl.
      }
      rewrite andp_assoc.
      apply derives_aux_refl.
    - apply derives_aux_refl.
    - apply derives_aux_refl.
    - apply derives_aux_refl.
    - intros; unfold RA_return at 1. solve_andp.
  + pose proof (fun x => semax_switch_inv _ _ _ _ _ (H x)).
    eapply semax_conseq; [| intros; apply derives_aux_refl .. | apply semax_switch].
    rewrite !exp_andp2.
    apply exp_left; intros x; specialize (H0 x).
    auto.
  + pose proof (fun x => semax_label_inv _ _ _ _ _ (H x)).
    apply semax_label.
    apply IHc.
    auto.
  + pose proof (fun x => semax_goto_inv _ _ _ _ (H x)).
    eapply semax_conseq; [| intros; apply derives_aux_refl .. | apply semax_goto].
    rewrite !exp_andp2.
    apply exp_left; intros x; specialize (H0 x).
    auto.
Qed.

Lemma semax_extract_prop: forall (CS : compspecs) (Espec : OracleKind) 
      (Delta : tycontext) (PP : Prop) (P : environ -> mpred)
      (c : Clight.statement) (Q : ret_assert),
    (PP -> semax Delta P c Q) ->
    semax Delta (!! PP && P) c Q.
Proof.
  intros.
  eapply semax_conseq with (P':=EX H: PP, P) (R':=Q); try solve [intros; solve_andp].
  + apply andp_left2. rewrite andp_comm. rewrite andp_assoc.
    apply derives_extract_prop. intros. Exists H0. solve_andp.
  + apply semax_extract_exists, H.
Qed.

Definition ret_assert_andp Q1 Q2 : ret_assert := {|
  RA_normal := RA_normal Q1 && RA_normal Q2;
  RA_break  := RA_break Q1 && RA_break Q2;
  RA_continue := RA_continue Q1 && RA_continue Q2;
  RA_return := fun v => (RA_return Q1 v && RA_return Q2 v)
|}.

Lemma semax_simple_inv:
forall (CS : compspecs) (Espec : OracleKind) (Delta : tycontext)
(Pre : environ -> mpred) (s : Clight.statement) 
  (Post Post' : ret_assert),
nocontinue s = true ->
noreturn s = true ->
nobreak s = true ->
RA_normal Post = RA_normal Post' ->
semax Delta Pre s Post ->
semax Delta Pre s Post'.
Proof.
  intros. destruct Post as [Qn Qb Qc Qr].
  destruct Post' as [Qn' Qb' Qc' Qr'].
  simpl in H2. subst.
  eapply semax_nobreak_inv with (Post:={|
    RA_normal := Qn';
    RA_break := Qb;
    RA_continue := Qc';
    RA_return := Qr'
  |});auto.
  eapply semax_nocontinue_inv with (Post:={|
    RA_normal := Qn';
    RA_break := Qb;
    RA_continue := Qc;
    RA_return := Qr'
  |});auto.
  eapply semax_noreturn_inv with (Post:={|
    RA_normal := Qn';
    RA_break := Qb;
    RA_continue := Qc;
    RA_return := Qr
  |});auto.
Qed.



Lemma semax_conj_assign_ret: forall CS Espec Delta P Q1 Q2 e e0,
  @semax CS Espec Delta P (Clight.Sassign e e0) Q2 ->
  @semax CS Espec Delta P (Clight.Sassign e e0) Q1 ->
  @semax CS Espec Delta P (Clight.Sassign e e0) (ret_assert_andp Q1 Q2).
Proof.
  intros.
  destruct Q1 as [Q1n Q1b Q1c Q1r].
  destruct Q2 as [Q2n Q2b Q2c Q2r].
  unfold ret_assert_andp. unfold_der.
  apply semax_simple_inv with (Post':=
    normal_ret_assert Q1n
  ) in H0;auto.
  apply semax_simple_inv with (Post':=
  normal_ret_assert Q2n) in H;auto.
  apply semax_simple_inv with (Post:=
  normal_ret_assert (Q1n&&Q2n));auto.
  eapply semax_conj_assign with (Q:= {|
  RA_normal := FF;
  RA_break := FF;
  RA_continue := FF;
  RA_return := (fun v => FF)
  |});auto.
Qed.

Lemma semax_conj_set_ret: forall CS Espec Delta P Q1 Q2 e e0,
  @semax CS Espec Delta P (Clight.Sset e e0) Q2 ->
  @semax CS Espec Delta P (Clight.Sset e e0) Q1 ->
  @semax CS Espec Delta P (Clight.Sset e e0) (ret_assert_andp Q1 Q2).
Proof.
  intros.
  destruct Q1 as [Q1n Q1b Q1c Q1r].
  destruct Q2 as [Q2n Q2b Q2c Q2r].
  unfold ret_assert_andp. unfold_der.
  apply semax_simple_inv with (Post':=
    normal_ret_assert Q1n
  ) in H0;auto.
  apply semax_simple_inv with (Post':=
  normal_ret_assert Q2n) in H;auto.
  apply semax_simple_inv with (Post:=
  normal_ret_assert (Q1n&&Q2n));auto.
  eapply semax_conj_set with (Q:= {|
  RA_normal := FF;
  RA_break := FF;
  RA_continue := FF;
  RA_return := (fun v => FF)
  |});auto.
Qed.


Lemma semax_conj_call_ret: forall CS Espec Delta ret a bl P Q1 Q2,
@semax CS Espec Delta P  (Clight.Scall ret a bl) Q2 ->
@semax CS Espec Delta P  (Clight.Scall ret a bl) Q1 ->
@semax CS Espec Delta P  (Clight.Scall ret a bl) (ret_assert_andp Q1 Q2).
Proof.
  intros.
  destruct Q1 as [Q1n Q1b Q1c Q1r].
  destruct Q2 as [Q2n Q2b Q2c Q2r].
  unfold ret_assert_andp. unfold_der.
  apply semax_simple_inv with (Post':=
    normal_ret_assert Q1n
  ) in H0;auto.
  apply semax_simple_inv with (Post':=
  normal_ret_assert Q2n) in H;auto.
  apply semax_simple_inv with (Post:=
  normal_ret_assert (Q1n&&Q2n));auto.
  eapply semax_conj_call with (Q:= {|
  RA_normal := FF;
  RA_break := FF;
  RA_continue := FF;
  RA_return := (fun v => FF)
  |});auto.
Qed.

Lemma ret_assert_override_distr: forall Q1 Q2 R1 R2,
  ret_assert_andp (overridePost R1 Q2) (overridePost R2 Q1) = 
  overridePost (R1 && R2) (ret_assert_andp Q2 Q1).
Proof.
  intros.
  destruct Q1, Q2. simpl. unfold ret_assert_andp.
  simpl. reflexivity.
Qed.

Lemma ret_assert_symm: forall Q1 Q2,
  ret_assert_andp Q1 Q2 = ret_assert_andp Q2 Q1.
Proof.
  intros.
  destruct Q1, Q2. unfold ret_assert_andp. unfold_der.
  rewrite andp_comm. f_equal; try (rewrite andp_comm;reflexivity).
  extensionality. rewrite andp_comm. reflexivity.
Qed.

Lemma semax_conj_break: forall CS Espec Delta P Q2 Q1,
  @semax CS Espec Delta P (Clight.Sbreak) Q2 ->
  @semax CS Espec Delta P (Clight.Sbreak) Q1 ->
  @semax CS Espec Delta P (Clight.Sbreak) (ret_assert_andp Q1 Q2).
Proof.
  intros.
  apply semax_break_inv in H0.
  apply semax_break_inv in H.
  destruct Q1 as [Q1n Q1b Q1c Q1r], Q2 as [Q2n Q2b Q2c Q2r];unfold ret_assert_andp; unfold_der.
  eapply semax_conseq with (R':={|
    RA_normal := FF;
    RA_break := Q1b && Q2b;
    RA_continue := FF;
    RA_return := (fun v => FF)
  |});[..|apply semax_break];unfold_der;
  try solve [intros;apply andp_left2;apply andp_left2;apply FF_left];try solve_andp.
  apply andp_right;auto.
Qed.

Lemma semax_conj_continue: forall CS Espec Delta P Q2 Q1,
  @semax CS Espec Delta P (Clight.Scontinue) Q2 ->
  @semax CS Espec Delta P (Clight.Scontinue) Q1 ->
  @semax CS Espec Delta P (Clight.Scontinue) (ret_assert_andp Q1 Q2).
Proof.
  intros.
  apply semax_continue_inv in H0.
  apply semax_continue_inv in H.
  destruct Q1 as [Q1n Q1b Q1c Q1r], Q2 as [Q2n Q2b Q2c Q2r];unfold ret_assert_andp; unfold_der.
  eapply semax_conseq with (R':={|
    RA_normal := FF;
    RA_break := FF;
    RA_continue := Q1c && Q2c;
    RA_return := (fun v => FF)
  |});[..|apply semax_continue];unfold_der;
  try solve [intros;apply andp_left2;apply andp_left2;apply FF_left];try solve_andp.
  apply andp_right;auto.
Qed.


Lemma semax_conj_return: forall CS Espec Delta P Q2 Q1 vl,
  @semax CS Espec Delta P (Clight.Sreturn vl) Q2 ->
  @semax CS Espec Delta P (Clight.Sreturn vl) Q1 ->
  @semax CS Espec Delta P (Clight.Sreturn vl) (ret_assert_andp Q1 Q2).
Proof.
  intros.
  apply semax_return_inv in H0.
  apply semax_return_inv in H.
  eapply semax_conseq with (R':= ret_assert_andp Q1 Q2);[..|apply semax_return];unfold_der;try (intros;solve_andp).
  destruct Q1 as [Q1n Q1b Q1c Q1r], Q2 as [Q2n Q2b Q2c Q2r];unfold ret_assert_andp; unfold_der.
  pose proof andp_ENTAILL _ _ _ _ _ H0 H.
  rewrite andp_dup in H1.
  eapply derives_trans;[apply H1|].
  repeat apply andp_right;try solve_andp.
  unfold_lift.
  intro rho.
  simpl.
  forget (cast_expropt vl (ret_type Delta) rho) as ret. solve_andp.
Qed.


Theorem semax_conj_rule: forall  CS Espec Delta P c Q1 Q2 ,
  @semax CS Espec Delta P c Q1 ->
  @semax CS Espec Delta P c Q2 ->
  @semax CS Espec Delta P c (ret_assert_andp Q1 Q2).
Proof.
  intros. revert dependent Q1.
  revert dependent Q2. revert dependent P .
  induction c.
  - intros. apply semax_skip_inv in H0.
    apply semax_skip_inv in H.
    eapply semax_conseq with (P':= RA_normal Q1 && RA_normal Q2);[..|apply semax_skip];try solve [intros;solve_andp].
    + apply andp_right.
      * eapply derives_trans;[|apply H]. solve_andp.
      * eapply derives_trans;[|apply H0]. solve_andp.
    + unfold normal_ret_assert. unfold RA_break. apply andp_left2. apply andp_left2. apply FF_left.
    + unfold normal_ret_assert. unfold RA_break. apply andp_left2. apply andp_left2. apply FF_left.
    + intros. unfold normal_ret_assert. unfold RA_break. apply andp_left2. apply andp_left2. apply FF_left.
  - intros.
    eapply semax_conseq;
    [..|eapply semax_conj_assign_ret with (Q1:=Q1) (Q2:=Q2);eassumption]; try solve_andp.
    intros. solve_andp.
  - intros.
    eapply semax_conseq;
    [..|eapply semax_conj_set_ret with (Q1:=Q1) (Q2:=Q2);eassumption]; try solve_andp.
    intros. solve_andp.
  - intros.
    eapply semax_conseq;
    [..|eapply semax_conj_call_ret with (Q1:=Q1) (Q2:=Q2);eassumption]; try solve_andp.
    intros. solve_andp.
  - intros. apply semax_builtin_inv in H0.
    eapply semax_pre';[apply H0|].
    rewrite <- (FF_andp P).
      unfold FF. apply semax_extract_prop. intros. destruct H1.
  - intros. apply semax_seq_inv' in H0.
    apply semax_seq_inv' in H.
    pose proof IHc1 _ _ H0 _ H.
    destruct Q1 as [Q1n Q1b Q1c Q1r],
    Q2 as [Q2n Q2b Q2c Q2r];unfold ret_assert_andp in *;unfold_der.
    eapply semax_seq with (Q:=
      EX Q, Q && !! semax Delta Q c2 {|
      RA_normal := Q1n && Q2n;
      RA_break := Q1b && Q2b;
      RA_continue := Q1c && Q2c;
      RA_return := fun v : option val => Q1r v && Q2r v |}    
    ).
    { eapply semax_conseq;[..|apply H1];unfold_der;
      intros;try solve_andp.
      Intros Q1. Intros Q2. Exists (Q1 && Q2).
      assert_PROPP (semax Delta Q1 c2
          {|
          RA_normal := Q1n;
          RA_break := Q1b;
          RA_continue := Q1c;
          RA_return := Q1r |}). { solve_andp. }
      assert_PROPP (semax Delta Q2 c2
      {|
      RA_normal := Q2n;
      RA_break := Q2b;
      RA_continue := Q2c;
      RA_return := Q2r |}). { solve_andp. }

      apply andp_right; try solve_andp.
      apply prop_right.
      apply semax_pre' with (P:= Q1 && Q2) in H2; try solve_andp.
      apply semax_pre' with (P:= Q1 && Q2) in H3; try solve_andp.
      pose proof IHc2 _ _ H3 _ H2. unfold_der.
      apply H4.
    }
    apply semax_extract_exists. intros R.
    rewrite andp_comm. apply semax_extract_prop.
    intros. auto.
(* 
    destruct H0 as [R1 [E1 E2]].
    destruct H as [R2 [E3 E4]].
    pose proof IHc1 _ _ E3 _ E1.
    assert (semax Delta (R1 && R2) c2 Q2).
    { eapply semax_conseq;[..|apply E2]; try solve [intros; solve_andp]. }
    assert (semax Delta (R1 && R2) c2 Q1).
    { eapply semax_conseq;[..|apply E4]; try solve [intros; solve_andp]. }
    pose proof IHc2 _ _ H0 _ H1.
    econstructor.
    { rewrite ret_assert_override_distr in H.
      rewrite ret_assert_symm. apply H. }
    { auto. } *)
  - intros.
    apply semax_ifthenelse_inv in H0.
    apply semax_ifthenelse_inv in H.
    pose proof andp_ENTAILL _ _ _ _ _ H0 H.
    rewrite andp_dup in H1.
    eapply semax_conseq with (R':=ret_assert_andp Q1 Q2);[apply H1|..]; try solve [intros;solve_andp].
    rewrite !andp_assoc.
    apply semax_extract_prop. intros.
    rewrite <- andp_assoc.
    rewrite andp_comm. rewrite !andp_assoc.
    apply semax_extract_prop. intros.
    rewrite !exp_andp1. rewrite exp_andp2. apply semax_extract_exists. intros R1.
    rewrite !exp_andp2. apply semax_extract_exists. intros R2.
    rewrite andp_comm. rewrite !andp_assoc. apply semax_extract_prop. intros [E1 E2].
    rewrite andp_comm. rewrite andp_assoc.  rewrite andp_comm. rewrite !andp_assoc.
    apply semax_extract_prop. intros [E3 E4].
    eapply semax_pre with
    (P':= (!! (bool_type (typeof e) = true) && tc_expr Delta (Eunop Cop.Onotbool e (Tint I32 Signed noattr)) && (R1 && R2))).
    { repeat apply andp_right; try solve_andp. apply prop_right. auto. }
    apply semax_ifthenelse.
    { eapply semax_pre.
      2:{ apply IHc1 with (P:= (R1 && R2 && local ((` (typed_true (typeof e))) (eval_expr e)))).
          - eapply semax_pre;[|apply E3]. solve_andp.
          - eapply semax_pre;[|apply E1]. solve_andp.
      } solve_andp.
    }
    { eapply semax_pre.
      2:{ apply IHc2 with (P:= (R1 && R2 && local ((` (typed_false (typeof e))) (eval_expr e)))).
          - eapply semax_pre;[|apply E4]. solve_andp.
          - eapply semax_pre;[|apply E2]. solve_andp.
      } solve_andp.
    }
  - intros.
    apply semax_loop_inv in H0.
    apply semax_loop_inv in H.
    pose proof andp_ENTAILL _ _ _ _ _ H0 H.
    rewrite andp_dup in H1.
    eapply semax_conseq with (R':=ret_assert_andp Q1 Q2);[apply H1|..]; try solve [intros;solve_andp].
    rewrite !exp_andp1. apply semax_extract_exists. intros R1a.
    rewrite !exp_andp1. apply semax_extract_exists. intros R1b.
    rewrite !andp_assoc. apply semax_extract_prop. intros [E1 E2]. rewrite andp_comm.
    rewrite !exp_andp1. apply semax_extract_exists. intros R2a.
    rewrite !exp_andp1. apply semax_extract_exists. intros R2b.
    rewrite !andp_assoc. apply semax_extract_prop. intros [E3 E4].
    clear H0 H H1.
  
    destruct Q1 as [Q1n Q1b Q1c Q1r], Q2 as [Q2n Q2b Q2c Q2r];unfold loop1_ret_assert, loop2_ret_assert in *; unfold_der.
    eapply semax_pre with (P:= R1a && R2a) in E1; try solve_andp.
    eapply semax_pre with (P:= R1b && R2b) in E2; try solve_andp.
    eapply semax_pre with (P:= R1a && R2a) in E3; try solve_andp.
    eapply semax_pre with (P:= R1b && R2b) in E4; try solve_andp.
    pose proof IHc1 _ _ E1 _ E3. pose proof IHc2 _ _ E2 _ E4. clear IHc1 IHc2.
    unfold ret_assert_andp in *. unfold_der.
    
    rewrite andp_comm. eapply semax_loop with (Q':= R1b && R2b);
    unfold loop1_ret_assert, loop2_ret_assert in *; unfold_der.
    + rewrite (andp_comm R1b). auto.
    + rewrite (andp_comm R1a). rewrite FF_andp in H0. auto.
  - intros. apply semax_conj_break;auto.
  - intros. apply semax_conj_continue;auto.
  - intros. apply semax_conj_return;auto.
  - intros. apply semax_switch_inv in H0.
    eapply semax_pre';[apply H0|].
    rewrite <- (FF_andp P).
    unfold FF. apply semax_extract_prop. intros. destruct H1.
  - intros. apply semax_label_inv in H0.
    apply semax_label_inv in H.
    constructor. apply IHc;auto.
  - intros. apply semax_goto_inv in H0.
    eapply semax_pre';[apply H0|].
    rewrite <- (FF_andp P).
    unfold FF. apply semax_extract_prop. intros. destruct H1.
Qed.

Lemma semax_seq_skip:
   forall CS Espec (Delta : tycontext) (P : environ -> mpred)
         (s : Clight.statement) (Q : ret_assert),
    @semax CS Espec Delta P s Q <->
    @semax CS Espec Delta P (Clight.Ssequence s Clight.Sskip) Q.
Proof.
  intros. destruct Q as [Qn Qb Qc Qr];unfold_der.
  split;intro.
  - eapply semax_seq with (Q:=Qn).
    { simpl. auto. }
    { eapply semax_simple_inv;[..|apply semax_skip];auto. }
  - apply semax_seq_inv in H.
    destruct H as [R [E1 E2]].
    apply semax_skip_inv in E2.
    unfold_der. eapply semax_conseq;[..|apply E1];
    try (intros; solve_andp).
    unfold_der. auto.
Qed.


Lemma semax_skip_seq:
  forall CS Espec (Delta : tycontext) (P : environ -> mpred)
      (s : Clight.statement) (Q : ret_assert),
    @semax CS Espec Delta P s Q <->
    @semax CS Espec Delta P (Clight.Ssequence Clight.Sskip s) Q.
Proof.
intros. destruct Q as [Qn Qb Qc Qr];unfold_der.
split;intro.
- eapply semax_seq with (Q:=P).
  { eapply semax_simple_inv;[..|apply semax_skip];auto. }
  { simpl. auto. }
- apply semax_seq_inv in H.
  destruct H as [R [E1 E2]].
  apply semax_skip_inv in E1.
  unfold_der. eapply semax_conseq;[..|apply E2];
  try (intros; solve_andp).
  auto.
Qed.


Theorem seq_assoc:
  forall {CS: compspecs} {Espec: OracleKind},
   forall Delta P s1 s2 s3 R,
        @semax CS Espec Delta P (Ssequence s1 (Ssequence s2 s3)) R <->
        @semax CS Espec Delta P (Ssequence (Ssequence s1 s2) s3) R.
Proof.
  intros.
  split; intros.
  + apply semax_seq_inv in H.
    destruct H as [? [? ?]].
    apply semax_seq_inv in H0.
    destruct H0 as [? [? ?]].
    eapply semax_seq; eauto.
    eapply semax_seq; eauto.
    destruct R; auto.
  + apply semax_seq_inv in H.
    destruct H as [? [? ?]].
    apply semax_seq_inv in H.
    destruct H as [? [? ?]].
    eapply semax_seq with x0; [destruct R; exact H |].
    eapply semax_seq; eauto.
Qed.


Lemma semax_if_seq:
 forall {CS: compspecs} {Espec: OracleKind} Delta P e c1 c2 c Q,
 semax Delta P (Sifthenelse e (Ssequence c1 c) (Ssequence c2 c)) Q ->
 semax Delta P (Ssequence (Sifthenelse e c1 c2) c) Q.
Proof.
  intros.
  apply semax_ifthenelse_inv in H.
  eapply semax_conseq; [exact H | intros; apply derives_aux_refl .. |].
  rewrite exp_andp2.
  apply semax_extract_exists.
  intros P'.
  rewrite andp_comm, andp_assoc.
  apply semax_extract_prop; intros [? ?].
  rewrite andp_comm.
  apply semax_seq_inv in H0.
  apply semax_seq_inv in H1.
  destruct H0 as [Q1 [? ?]], H1 as [Q2 [? ?]].
  apply semax_seq with (orp Q1 Q2); [apply semax_ifthenelse |].
  + eapply semax_post; [| | | | exact H0].
    - destruct Q; apply andp_left2, orp_right1, derives_refl.
    - destruct Q; apply andp_left2, derives_refl.
    - destruct Q; apply andp_left2, derives_refl.
    - intro; destruct Q; apply andp_left2, derives_refl.
  + eapply semax_post; [| | | | exact H1].
    - destruct Q; apply andp_left2, orp_right2, derives_refl.
    - destruct Q; apply andp_left2, derives_refl.
    - destruct Q; apply andp_left2, derives_refl.
    - intro; destruct Q; apply andp_left2, derives_refl.
  + rewrite orp_is_exp.
    apply semax_extract_exists.
    intro.
    destruct x; auto.
Qed.


Definition semax_equiv {CS: compspecs} {Espec: OracleKind} c1 c2: Prop := forall Delta P Q, semax Delta P c1 Q <-> semax Delta P c2 Q.

Lemma semax_equiv_seq: forall {CS: compspecs} {Espec: OracleKind} c1 c2 c3 c4,
  semax_equiv c1 c2 ->
  semax_equiv c3 c4 ->
  semax_equiv (Ssequence c1 c3) (Ssequence c2 c4).
Proof.
  intros.
  hnf; intros; split; intros.
  + apply semax_seq_inv in H1.
    destruct H1 as [? [? ?]].
    rewrite (H Delta P _) in H1.
    rewrite (H0 Delta _ _) in H2.
    eapply semax_seq; eauto.
  + apply semax_seq_inv in H1.
    destruct H1 as [? [? ?]].
    rewrite <- (H Delta P _) in H1.
    rewrite <- (H0 Delta _ _) in H2.
    eapply semax_seq; eauto.
Qed.

Lemma semax_equiv_sym: forall {CS: compspecs} {Espec: OracleKind} c1 c2, semax_equiv c1 c2 -> semax_equiv c2 c1.
Proof.
  intros.
  hnf in H |- *.
  intros.
  specialize (H Delta P Q).
  tauto.
Qed.

Lemma semax_equiv_trans: forall {CS: compspecs} {Espec: OracleKind} c1 c2 c3, semax_equiv c1 c2 -> semax_equiv c2 c3 -> semax_equiv c1 c3.
Proof.
  intros.
  hnf in H, H0 |- *.
  intros.
  specialize (H Delta P Q).
  specialize (H0 Delta P Q).
  tauto.
Qed.


Fixpoint fold_Ssequence lc :=
  match lc with
  | nil => Sskip
  | c1 :: nil => c1
  | c :: lc0 => Ssequence c (fold_Ssequence lc0)
  end.


Definition non_Sseq c :=
  match c with
  | Ssequence _ _ => False
  | _ => True
  end.

Inductive unfold_Sseq_rel: statement -> list statement -> Prop :=
  | singleton: forall c, non_Sseq c -> unfold_Sseq_rel c (c :: nil)
  | tl_step: forall c1 c2 lc, non_Sseq c1 -> unfold_Sseq_rel c2 lc ->
                 unfold_Sseq_rel (Ssequence c1 c2) (c1 :: lc)
  | hd_step: forall c1 c2 c3 lc, unfold_Sseq_rel (Ssequence c1 (Ssequence c2 c3)) lc ->
                 unfold_Sseq_rel (Ssequence (Ssequence c1 c2) c3) lc
  .

Lemma unfold_Sseq_rel_non_nil: forall {c} {P: Prop}, unfold_Sseq_rel c nil -> P.
Proof.
  intros.
  remember nil as lc.
  induction H.
  + congruence.
  + congruence.
  + auto.
Qed.

Lemma unfold_Sseq_rel_sound: forall {CS: compspecs} {Espec: OracleKind} c lc,
  unfold_Sseq_rel c lc -> semax_equiv (fold_Ssequence lc) c.
Proof.
  intros.
  induction H.
  + simpl.
    hnf; intros; tauto.
  + simpl.
    destruct lc; [apply (unfold_Sseq_rel_non_nil H0) |].
    apply semax_equiv_seq; [hnf; intros; tauto | assumption].
  + eapply semax_equiv_trans; [eauto |].
    hnf; intros.
    apply seq_assoc.
Qed.

Lemma unfold_Ssequence_unfold_Sseq_rel: forall c, unfold_Sseq_rel c (unfold_Ssequence c).
Proof.
  intros.
  induction c; try solve [apply singleton, I].
  revert c2 IHc2.
  clear IHc1.
  induction c1; intros; try solve [apply tl_step; [apply I | auto]].
  apply hd_step.
  replace (unfold_Ssequence (Ssequence (Ssequence c1_1 c1_2) c2)) with
    (unfold_Ssequence (Ssequence c1_1 (Ssequence c1_2 c2))).
  2:{
    simpl.
    rewrite <- app_assoc.
    reflexivity.
  }
  apply IHc1_1.
  apply IHc1_2.
  apply IHc2.
Qed.

Lemma unfold_Ssequence_sound: forall {CS: compspecs} {Espec: OracleKind} c, semax_equiv (fold_Ssequence (unfold_Ssequence c)) c.
Proof.
  intros.
  apply unfold_Sseq_rel_sound.
  apply unfold_Ssequence_unfold_Sseq_rel.
Qed.

Lemma semax_unfold_Ssequence': forall {CS: compspecs} {Espec: OracleKind} c1 c2,
  unfold_Ssequence c1 = unfold_Ssequence c2 ->
  (forall P Q Delta, semax Delta P c1 Q <-> semax Delta P c2 Q).
Proof.
  intros.
  eapply semax_equiv_trans.
  + apply semax_equiv_sym.
    apply unfold_Ssequence_sound.
  + rewrite H.
    apply unfold_Ssequence_sound.
Qed.

Lemma semax_unfold_Ssequence: forall {CS: compspecs} {Espec: OracleKind} c1 c2,
  unfold_Ssequence c1 = unfold_Ssequence c2 ->
  (forall P Q Delta, @semax CS Espec Delta P c1 Q -> @semax CS Espec Delta P c2 Q).
Proof.
  intros.
  pose proof semax_unfold_Ssequence' _ _ H.
  clear - H0 H1.
  firstorder.
Qed.
