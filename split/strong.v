Require Import AClight.AClight.
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
Require VST.floyd.SeparationLogicAsLogicSoundness.
Require VST.floyd.SeparationLogicFacts.
Export SeparationLogicAsLogicSoundness.MainTheorem.CSHL_Sound.DeepEmbedded.
Require Import VST.floyd.proofauto.
Import Ctypes LiftNotation.
Local Open Scope logic.
Require Import split.vst_ext.



Definition obox (Delta: tycontext) (i: ident) (P: environ -> mpred): environ -> mpred :=
  ALL v: _,
    match ((temp_types Delta) ! i) with
    | Some t => !! (tc_val' t v) --> subst i (`v) P
    | _ => TT
    end.

Definition oboxopt Delta ret P :=
  match ret with
  | Some id => obox Delta id P
  | _ => P
  end.



Inductive semax_aux {CS: compspecs} {Espec: OracleKind} (Delta: tycontext): (environ -> mpred) -> Clight.statement -> ret_assert -> Prop :=
| semax_aux_ifthenelse :
   forall P (b: expr) c d R,
     @semax_aux CS Espec Delta (P && local (`(typed_true (typeof b)) (eval_expr b))) c R ->
     @semax_aux CS Espec Delta (P && local (`(typed_false (typeof b)) (eval_expr b))) d R ->
     @semax_aux CS Espec Delta (!! (bool_type (typeof b) = true) && tc_expr Delta (Eunop Cop.Onotbool b (Tint I32 Signed noattr)) && P) (Clight.Sifthenelse b c d) R
| semax_aux_seq:
  forall R P Q h t,
    @semax_aux CS Espec Delta P h (overridePost Q R) ->
    @semax_aux CS Espec Delta Q t R ->
    @semax_aux CS Espec Delta P (Clight.Ssequence h t) R
| semax_aux_break: forall Q,
    @semax_aux CS Espec Delta (RA_break Q) Clight.Sbreak Q
| semax_aux_continue: forall Q,
    @semax_aux CS Espec Delta (RA_continue Q) Clight.Scontinue Q
| semax_aux_loop: forall Q Q' incr body R,
     @semax_aux CS Espec Delta  Q body (loop1_ret_assert Q' R) ->
     @semax_aux CS Espec Delta Q' incr (loop2_ret_assert Q R) ->
     @semax_aux CS Espec Delta Q (Clight.Sloop body incr) R
| semax_aux_call_backward: forall ret a bl R,
     @semax_aux CS Espec Delta
         (EX argsig: _, EX retsig: _, EX cc: _,
          EX A: _, EX P: _, EX Q: _, EX NEP: _, EX NEQ: _, EX ts: _, EX x: _,
         !! (Cop.classify_fun (typeof a) =
             Cop.fun_case_f (type_of_params argsig) retsig cc /\
             (retsig = Tvoid -> ret = None) /\
             tc_fn_return Delta ret retsig) &&
          (((tc_expr Delta a) && (tc_exprlist Delta (snd (split argsig)) bl)))  &&
         `(func_ptr (mk_funspec  (argsig,retsig) cc A P Q NEP NEQ)) (eval_expr a) &&
          |>((`(P ts x: environ -> mpred) (make_args' (argsig,retsig) (eval_exprlist (snd (split argsig)) bl))) * oboxopt Delta ret (maybe_retval (Q ts x) retsig ret -* R)))
         (Clight.Scall ret a bl)
         (normal_ret_assert R)
| semax_aux_return: forall (R: ret_assert) ret ,
      @semax_aux CS Espec Delta
                ( (tc_expropt Delta ret (ret_type Delta)) &&
                `(RA_return R : option val -> environ -> mpred) (cast_expropt ret (ret_type Delta)) (@id environ))
                (Clight.Sreturn ret)
                R
| semax_aux_set_ptr_compare_load_cast_load_backward: forall (P: environ->mpred) id e,
    @semax_aux CS Espec Delta
       ((|> ( (tc_expr Delta e) &&
             (tc_temp_id id (typeof e) Delta e) &&
             subst id (eval_expr e) P)) ||
        (EX cmp: Cop.binary_operation, EX e1: expr, EX e2: expr,
         EX ty: type, EX sh1: share, EX sh2: share,
          !! (e = Ebinop cmp e1 e2 ty /\
              sepalg.nonidentity sh1 /\ sepalg.nonidentity sh2 /\
              is_comparison cmp = true /\
              eqb_type (typeof e1) int_or_ptr_type = false /\
              eqb_type (typeof e2) int_or_ptr_type = false /\
              typecheck_tid_ptr_compare Delta id = true) &&
            ( |> ( (tc_expr Delta e1) &&
              (tc_expr Delta e2)  &&
          local (`(blocks_match cmp) (eval_expr e1) (eval_expr e2)) &&
          (`(mapsto_ sh1 (typeof e1)) (eval_expr e1) * TT) &&
          (`(mapsto_ sh2 (typeof e2)) (eval_expr e2) * TT) &&
          subst id (eval_expr (Ebinop cmp e1 e2 ty)) P))) ||
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
| semax_aux_store_backward: forall e1 e2 P,
   @semax_aux CS Espec Delta
          (EX sh: share, !! writable_share sh && |> ( (tc_lvalue Delta e1) &&  (tc_expr Delta (Ecast e2 (typeof e1)))  &&
             ((`(mapsto_ sh (typeof e1)) (eval_lvalue e1)) * (`(mapsto sh (typeof e1)) (eval_lvalue e1) (`force_val (`(sem_cast (typeof e2) (typeof e1)) (eval_expr e2))) -* P))))
          (Clight.Sassign e1 e2)
          (normal_ret_assert P)
| semax_aux_skip: forall P, @semax_aux CS Espec Delta P Clight.Sskip (normal_ret_assert P)
| semax_aux_builtin: forall P opt ext tl el, @semax_aux CS Espec Delta FF (Clight.Sbuiltin opt ext tl el) P
| semax_aux_conseq: forall P' (R': ret_assert) P c (R: ret_assert) ,
    (local (tc_environ Delta) && (allp_fun_id Delta && P) |-- P') ->
    local (tc_environ Delta) && (allp_fun_id Delta && RA_normal R') |-- RA_normal R ->
    local (tc_environ Delta) && (allp_fun_id Delta && RA_break R') |-- RA_break R ->
    local (tc_environ Delta) && (allp_fun_id Delta && RA_continue R') |-- RA_continue R ->
    (forall vl, local (tc_environ Delta) && (allp_fun_id Delta && RA_return R' vl) |-- RA_return R vl) ->
    @semax_aux CS Espec Delta P' c R' -> @semax_aux CS Espec Delta P c R.


Inductive semax {CS: compspecs} {Espec: OracleKind} (Delta: tycontext): (environ -> mpred) -> Clight.statement -> ret_assert -> Prop :=
(* | semax_aux_intro :
   forall P c R,
     @semax_aux CS Espec Delta P c R ->
     @semax CS Espec Delta P c R
| semax_switch: forall (Q: environ->mpred) a sl R,
     (forall rho, Q rho |-- tc_expr Delta a rho) ->
     (forall n,
     @semax CS Espec Delta 
               (local (`eq (eval_expr a) `(Vint n)) &&  Q)
               (seq_of_labeled_statement (select_switch (Int.unsigned n) sl))
               (switch_ret_assert R)) ->
     @semax CS Espec Delta (!! (is_int_type (typeof a) = true) && Q) (Clight.Sswitch a sl) R
(*| semax_call_backward: forall ret a bl R,
     @semax CS Espec Delta
         (EX argsig: _, EX retsig: _, EX cc: _,
          EX A: _, EX P: _, EX Q: _, EX NEP: _, EX NEQ: _, EX ts: _, EX x: _,
         !! (Cop.classify_fun (typeof a) =
             Cop.fun_case_f (type_of_params argsig) retsig cc /\
             (retsig = Tvoid -> ret = None) /\
             tc_fn_return Delta ret retsig) &&
          (|>((tc_expr Delta a) && (tc_exprlist Delta (snd (split argsig)) bl)))  &&
         `(func_ptr (mk_funspec  (argsig,retsig) cc A P Q NEP NEQ)) (eval_expr a) &&
          |>((`(P ts x: environ -> mpred) (make_args' (argsig,retsig) (eval_exprlist (snd (split argsig)) bl))) * oboxopt Delta ret (maybe_retval (Q ts x) retsig ret -* R)))
         (Scall ret a bl)
         (normal_ret_assert R)*)
| semax_label: forall (P:environ -> mpred) c (Q:ret_assert) l,
    @semax CS Espec Delta P c Q -> @semax CS Espec Delta P (Clight.Slabel l c) Q
| semax_goto: forall P l, @semax CS Espec Delta FF (Clight.Sgoto l) P *)
| semax_conseq_intro: forall P' (R': ret_assert) P c (R: ret_assert) ,
    (* local (tc_environ Delta) && ((allp_fun_id Delta) && P) |-- |==> |> FF || P' -> *)
    ENTAIL Delta, (allp_fun_id Delta) && P |-- P' ->
    local (tc_environ Delta) && ((allp_fun_id Delta) && RA_normal R') |-- |==> |> FF || RA_normal R ->
    local (tc_environ Delta) && ((allp_fun_id Delta) && RA_break R') |-- |==> |> FF || RA_break R ->
    local (tc_environ Delta) && ((allp_fun_id Delta) && RA_continue R') |-- |==> |> FF || RA_continue R ->
    (forall vl, local (tc_environ Delta) && ((allp_fun_id Delta) && RA_return R' vl) |-- |==> |> FF || RA_return R vl) ->
    @semax_aux CS Espec Delta P' c R' -> @semax CS Espec Delta P c R.


Lemma semax_aux_skip_inv: forall CS Espec Delta P R,
  @semax_aux CS Espec Delta P (Clight.Sskip) R ->
  ENTAIL Delta, local (tc_environ Delta) && (allp_fun_id Delta && P) |-- RA_normal R.
Proof.
  intros.
  remember (Clight.Sskip) as c1.
  induction H; try inversion Heqc1.
  - solve_andp.
  - subst. specialize (IHsemax_aux eq_refl).
    eapply derives_trans.
    2:{ apply H0. }
    apply andp_right;try solve_andp.
    apply andp_right;try solve_andp.
    eapply derives_trans.
    2:{ apply IHsemax_aux. }
    apply andp_right;try solve_andp.
    apply andp_right;try solve_andp.
    apply andp_right;try solve_andp.
    eapply derives_trans.
    2:{ apply H. }
    solve_andp.
Qed.

Lemma semax_aux_seq_inv: forall CS Espec (Delta : tycontext) (P : environ -> mpred) 
      (R : ret_assert) (h t : Clight.statement),
    @semax_aux CS Espec Delta P (Clight.Ssequence h  t)%C R ->
    exists Q : environ -> mpred,
      @semax_aux CS Espec Delta P h (overridePost Q R) /\
      @semax_aux CS Espec Delta Q t R.
Admitted.


Lemma semax_aux_seq_inv': forall CS Espec (Delta : tycontext) (P : environ -> mpred) 
      (R : ret_assert) (h t : Clight.statement),
    @semax_aux CS Espec Delta P (Clight.Ssequence h  t)%C R ->
    @semax_aux CS Espec Delta P h
         (overridePost
            (EX Q : environ -> mpred,
             !! semax_aux Delta Q t R && Q)%assert R).
Admitted.

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
 match sl with Clight.LSnil => true | Clight.LScons _ s sl' => if nobreak s then nobreak_ls sl' else false
 end.


Lemma semax_aux_nocontinue_inv:
forall (CS : compspecs) (Espec : OracleKind) (Delta : tycontext)
(Pre : environ -> mpred) (s : Clight.statement) 
  (Post Post' : ret_assert),
nocontinue s = true ->
RA_normal Post = RA_normal Post' ->
RA_break Post = RA_break Post' ->
RA_return Post = RA_return Post' ->
semax_aux Delta Pre s Post ->
semax_aux Delta Pre s Post'.
Admitted.

Lemma semax_aux_noreturn_inv:
forall (CS : compspecs) (Espec : OracleKind) (Delta : tycontext)
(Pre : environ -> mpred) (s : Clight.statement) 
  (Post Post' : ret_assert),
noreturn s = true ->
RA_normal Post = RA_normal Post' ->
RA_break Post = RA_break Post' ->
RA_continue Post = RA_continue Post' ->
semax_aux Delta Pre s Post -> semax_aux Delta Pre s Post'.
Admitted.

Lemma semax_aux_nobreak_inv:
forall (CS : compspecs) (Espec : OracleKind) (Delta : tycontext)
(Pre : environ -> mpred) (s : Clight.statement) 
  (Post Post' : ret_assert),
nobreak s = true ->
RA_normal Post = RA_normal Post' ->
RA_return Post = RA_return Post' ->
RA_continue Post = RA_continue Post' ->
semax_aux Delta Pre s Post -> semax_aux Delta Pre s Post'.
Admitted.


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
Admitted.


Lemma semax_noreturn_inv:
forall (CS : compspecs) (Espec : OracleKind) (Delta : tycontext)
(Pre : environ -> mpred) (s : Clight.statement) 
  (Post Post' : ret_assert),
noreturn s = true ->
RA_normal Post = RA_normal Post' ->
RA_break Post = RA_break Post' ->
RA_continue Post = RA_continue Post' ->
semax Delta Pre s Post -> semax Delta Pre s Post'.
Admitted.

Lemma semax_nobreak_inv:
forall (CS : compspecs) (Espec : OracleKind) (Delta : tycontext)
(Pre : environ -> mpred) (s : Clight.statement) 
  (Post Post' : ret_assert),
nobreak s = true ->
RA_normal Post = RA_normal Post' ->
RA_return Post = RA_return Post' ->
RA_continue Post = RA_continue Post' ->
semax Delta Pre s Post -> semax Delta Pre s Post'.
Admitted.


(* no continue/ no break/ no return *)

Lemma semax_aux_seq_inv_strong_normal: forall CS Espec (Delta : tycontext) (P : environ -> mpred) 
      (R : ret_assert) (h t : Clight.statement)
      (Ebr: nobreak h = true) (Econt: nocontinue h = true) (Eret: noreturn h = true),
    @semax CS Espec Delta P (Clight.Ssequence h  t)%C R ->
    @semax_aux CS Espec Delta P h
         (overridePost
            (EX Q : environ -> mpred,
             !! semax Delta Q t R && Q)%assert R).
Proof.
  intros.
  remember (Clight.Ssequence h t) as c eqn:?H.
  inversion H. subst P0 c0 R0.
  revert dependent P. revert dependent R.
  induction H6; try (inv H0).
    * intros. clear IHsemax_aux1 IHsemax_aux2.
      destruct R as [Rn Rb Rc Rr].
      destruct R0 as [Rn' Rb' Rc' Rr'].
      unfold overridePost, RA_normal, RA_break, RA_continue, RA_return in *.
      eapply semax_aux_nobreak_inv with (Post:= {|
        RA_normal := (EX Q0 : environ -> mpred,
                      !! semax Delta Q0 t {| RA_normal := Rn'; RA_break := Rb';
                      RA_continue := Rc'; RA_return := Rr' |} && Q0)%assert;
        RA_break := |==> |> FF || Rb';
        RA_continue := Rc';
        RA_return := Rr' |});try reflexivity;auto.
      eapply semax_aux_nocontinue_inv with (Post:= {|
        RA_normal := (EX Q0 : environ -> mpred,
                      !! semax Delta Q0 t {| RA_normal := Rn'; RA_break := Rb';
                      RA_continue := Rc'; RA_return := Rr' |} && Q0)%assert;
        RA_break := |==> |> FF || Rb';
        RA_continue := |==> |> FF || Rc';
        RA_return := Rr' |});try reflexivity;auto.
      eapply semax_aux_noreturn_inv with (Post:= {|
        RA_normal := (EX Q0 : environ -> mpred,
                      !! semax Delta Q0 t {| RA_normal := Rn'; RA_break := Rb';
                      RA_continue := Rc'; RA_return := Rr' |} && Q0)%assert;
        RA_break := |==> |> FF || Rb';
        RA_continue := |==> |> FF || Rc';
        RA_return := |==> |> FF || Rr' |});try reflexivity;auto.
      eapply semax_aux_conseq; [.. | exact H6_].
      - eapply derives_trans;[|apply H1];solve_andp.
      - unfold RA_normal. Exists Q.
        apply andp_right; [apply prop_right |]; auto. 2:{ solve_andp. }
        eapply semax_conseq_intro;[..|apply H6_0]; auto. solve_andp.
      - unfold RA_break. eapply derives_trans;[|apply H3]. solve_andp.
      - unfold RA_continue. eapply derives_trans;[|apply H4]. solve_andp.
      - unfold RA_return. intros. eapply derives_trans;[|apply H5]. solve_andp.
    * pose proof IHsemax_aux eq_refl. clear IHsemax_aux.
      intros. apply H0;auto.
      - apply add_andp in H1. rewrite H1.
        eapply derives_trans;[|apply H5]. solve_andp.
      - apply add_andp in H2. rewrite H2.
        eapply derives_trans;[|apply H7]. solve_andp.
      - apply add_andp in H3. rewrite H3.
        eapply derives_trans;[|apply H8]. solve_andp.
      - intros. specialize (H4 vl). apply add_andp in H4. rewrite H4.
        eapply derives_trans;[|apply H9]. solve_andp.
      - eapply derives_trans;[|apply H].
        apply add_andp in H11. rewrite H11. solve_andp.
Qed.

Lemma semax_aux_seq_inv_strong: forall CS Espec (Delta : tycontext) (P : environ -> mpred) 
      (R : ret_assert) (h t : Clight.statement),
    @semax CS Espec Delta P (Clight.Ssequence h  t)%C R ->
    @semax CS Espec Delta P h
         (overridePost
            (EX Q : environ -> mpred,
             !! semax_aux Delta Q t R && Q)%assert R).
Proof.
  intros.
  remember (Clight.Ssequence h t) as c eqn:?H.
  induction H; try solve [inv H0].
  + induction H; try solve [ inv H0 ].
    * inv H0. clear IHsemax_aux1 IHsemax_aux2.
      apply semax_aux_intro in H.
      eapply semax_conseq; [.. | exact H].
      - apply aux1_reduceR. apply aux2_reduceR. solve_andp.
      - apply aux1_reduceR. apply aux2_reduceR.
         destruct R; unfold overridePost, tycontext.RA_normal.
        apply (exp_right Q).
        apply andp_right; [apply prop_right |]; auto.
        solve_andp.
      - destruct R. unfold tycontext.RA_break, overridePost.
        apply aux1_reduceR. apply aux2_reduceR. solve_andp.
      - destruct R. unfold tycontext.RA_break, overridePost.
        apply aux1_reduceR. apply aux2_reduceR. solve_andp.
      - intro.  destruct R; unfold tycontext.RA_break, overridePost.
        apply aux1_reduceR. apply aux2_reduceR. solve_andp.
    * subst c.
      pose proof IHsemax_aux eq_refl. clear IHsemax_aux.
      eapply semax_conseq; [.. | exact H0]; auto.
      - apply aux1_reduceR. apply aux2_reduceR.
        eapply derives_trans;[|apply H]. solve_andp.
      - unfold overridePost, tycontext.RA_normal.
        destruct R' as [R'0 R'1 R'2 R'3] at 1; clear R'0 R'1 R'2 R'3.
        destruct R as [R0 R1 R2 R3] at 1; clear R0 R1 R2 R3.
        reduce2derives.
        apply exp_derives.
        intros Q.
        normalize.
        apply andp_right; [apply prop_right | auto].
        eapply semax_aux_conseq; [.. | apply H6]; auto; try
        apply derives_full_refl.
      - destruct R, R'; auto. unfold tycontext.RA_break, overridePost in*.
        apply aux1_reduceR. apply aux2_reduceR. admit.
      - admit.
      - admit.
  + subst c.
    pose proof IHsemax eq_refl. clear IHsemax.
    apply semax_aux_intro.
    eapply semax_aux_conseq; [.. | exact H0]; auto.
    - unfold overridePost, tycontext.RA_normal.
      destruct R' as [R'0 R'1 R'2 R'3] at 1; clear R'0 R'1 R'2 R'3.
      destruct R as [R0 R1 R2 R3] at 1; clear R0 R1 R2 R3.
      reduce2derives.
      apply exp_derives.
      intros Q.
      normalize.
      apply andp_right; [apply prop_right | auto].
      eapply semax_aux_conseq; [.. | apply H6]; auto.
      apply derives_full_refl.
    - destruct R, R'; auto.
    - destruct R, R'; auto.
    - destruct R, R'; auto.





Theorem semax_aux_conj_rule: forall  CS Espec Delta P Q c Q1 Q2 ,
  @semax_aux CS Espec Delta P c (overridePost Q1 Q) ->
  @semax_aux CS Espec Delta P c (overridePost Q2 Q) ->
  @semax_aux CS Espec Delta P c (overridePost (andp Q1 Q2) Q).
Proof.
  intros. revert dependent Q1.
  revert dependent Q2. revert dependent P .
  induction c.
  - intros.
    destruct Q as [Qn Qb Qc Qr].
    unfold overridePost in *.
    apply semax_aux_skip_inv in H0.
    apply semax_aux_skip_inv in H.
    eapply semax_aux_conseq with (P':= andp (Q1) (Q2))
    (R':= (normal_ret_assert (andp (Q1) (Q2)))); unfold normal_ret_assert.
    { apply andp_right.
      { eapply derives_trans;[|apply H]. solve_andp. }
      { eapply derives_trans;[|apply H0]. solve_andp. }
    }
    { unfold RA_normal. apply ENTAIL_refl. }
    { unfold RA_break. apply andp_left2. apply FF_left. }
    { unfold RA_continue. apply andp_left2. apply FF_left. }
    { intros. unfold RA_return. apply andp_left2. apply FF_left. }
    apply semax_aux_skip.
  - 

Admitted.


Theorem semax_derives: forall CS Espec Delta P c Q,
  @semax CS Espec Delta P c Q -> @SeparationLogicAsLogic.AuxDefs.semax CS Espec Delta P c Q.
Admitted.


Lemma semax_noreturn_inv_aux {CS: compspecs} {Espec: OracleKind} 
  (Delta: tycontext):
  forall Pre s Post Post',
    noreturn s = true ->
    RA_normal Post = RA_normal Post' ->
    RA_break Post = RA_break Post' ->
    RA_continue Post = RA_continue Post' ->
    @semax_aux CS Espec Delta Pre s Post -> @semax_aux CS Espec Delta Pre s Post'.
Admitted.




(* Lemma semax_aux_seq_inv: forall {CS: compspecs} {Espec: OracleKind} Delta P R h t,
    @semax CS Espec Delta P (Clight.Ssequence h t) R ->
    exists Q, @semax CS Espec Delta P h (overridePost Q R) /\
              @semax_aux CS Espec Delta Q t R.
Proof.
  intros.
  remember (Clight.Ssequence h t) as c eqn:?H.
  induction H; try solve [inv H0].
  + induction H; try solve [inv H0].
    - inv H0.
      exists Q; split;auto.
      apply semax_aux_intro. auto.
    - subst c. specialize (IHsemax_aux eq_refl).
      destruct IHsemax_aux as [Q [? ?]].
      exists Q. split.
      { destruct R as [Rn Rb Rc Rr],  R' as [Rn' Rb' Rc' Rr'];
        unfold overridePost in *;
         unfold RA_normal, RA_break, RA_continue, RA_return in *.
        apply semax_conseq with (P'0:=P') (R' := {| RA_normal := Q; RA_break := Rb'; RA_continue := Rc'; RA_return := Rr' |});auto;
        unfold RA_normal, RA_break, RA_continue, RA_return in *;
        try apply derives_full_refl; try apply ENTAIL_refl.
        * apply aux1_reduceR. apply aux2_reduceR. eapply derives_trans;[|apply H]. solve_andp. 
        * apply aux1_reduceR. apply aux2_reduceR. eapply derives_trans;[|apply H2]. solve_andp. 
        * apply aux1_reduceR. apply aux2_reduceR. eapply derives_trans;[|apply H3]. solve_andp. 
        * intros. apply aux1_reduceR. apply aux2_reduceR. eapply derives_trans;[|apply H4]. solve_andp. }
      { destruct R as [Rn Rb Rc Rr],  R' as [Rn' Rb' Rc' Rr'];
        unfold overridePost in *;
         unfold RA_normal, RA_break, RA_continue, RA_return in *.
        eapply semax_aux_conseq;[..|apply H6];auto;
        unfold RA_normal, RA_break, RA_continue, RA_return in *;
        try apply derives_full_refl; try apply ENTAIL_refl. }
  + subst c.
    pose proof IHsemax eq_refl. clear IHsemax.
    destruct H0 as [Q [? ?]].
    exists Q.
    split.
    - apply (semax_conseq _ P' (overridePost Q R')); auto.
      * clear.
        destruct R, R'.
        apply derives_full_refl.
      * destruct R, R'; auto.
      * destruct R, R'; auto.
      * destruct R, R'; auto.
    - eapply semax_aux_conseq;[..|apply H6].
    
    ; eauto.
      apply derives_full_refl.
      

  + subst c.
    pose proof IHsemax eq_refl. clear IHsemax.
    destruct H0 as [Q [? ?]].
    exists Q.
    split.
    - apply (AuxDefs.semax_conseq _ P' (overridePost Q R')); auto.
      * clear.
        destruct R, R'.
        apply derives_full_refl.
      * destruct R, R'; auto.
      * destruct R, R'; auto.
      * destruct R, R'; auto.
    - eapply semax_conseq; eauto.
      apply derives_full_refl.
Qed. *)



(* 
Lemma aux_extract_exists_pre: forall {CS Espec} (A : Type) (P : A -> environ -> mpred) 
      (c : Clight.statement) (Delta : tycontext) 
      (R : ret_assert),
    (forall x : A, @semax_aux CS Espec Delta (P x) c R) ->
    semax_aux Delta (EX x : A, P x) c R.
Admitted.

Lemma aux_semax_extract_prop: forall (CS : compspecs) (Espec : OracleKind) 
      (Delta : tycontext) (PP : Prop) (P : environ -> mpred)
      (c : Clight.statement) (Q : ret_assert),
    (PP -> semax_aux Delta P c Q) ->
    semax_aux Delta (!! PP && P) c Q.
Admitted. *)



Lemma aux_extract_exists_pre': forall {CS Espec} (A : Type) (P : A -> environ -> mpred) 
      (c : Clight.statement) (Delta : tycontext) 
      (R : ret_assert),
    (forall x : A, @semax CS Espec Delta (P x) c R) ->
    semax Delta (EX x : A, P x) c R.
Admitted.

Lemma aux_semax_extract_prop': forall (CS : compspecs) (Espec : OracleKind) 
      (Delta : tycontext) (PP : Prop) (P : environ -> mpred)
      (c : Clight.statement) (Q : ret_assert),
    (PP -> semax Delta P c Q) ->
    semax Delta (!! PP && P) c Q.
Admitted.

(* Used for proving

Lemma add_pre_to_semax_sem: forall (x:partial_path_statement),
  (add_pre_to_semax
        (EX Q : assert,
          !! (add_pre_to_semax Q x) && Q)) 
      x.


*)