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
Require Import Split.vst_ext.

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
| semax_aux_return: forall (R: ret_assert) ret ,
      @semax_aux CS Espec Delta
                ( (tc_expropt Delta ret (ret_type Delta)) &&
                `(RA_return R : option val -> environ -> mpred) (cast_expropt ret (ret_type Delta)) (@id environ))
                (Clight.Sreturn ret)
                R
| semax_aux_skip: forall P, @semax_aux CS Espec Delta P Clight.Sskip (normal_ret_assert P)
| semax_aux_assign: forall (P: environ->mpred) e1 e2,
    @semax_aux CS Espec Delta
    (EX sh: share, !! writable_share sh &&
      (|> ( (tc_lvalue Delta e1) &&  (tc_expr Delta (Ecast e2 (typeof e1)))  &&
      ((`(mapsto_ sh (typeof e1)) (eval_lvalue e1)) * (`(mapsto sh (typeof e1)) (eval_lvalue e1) (`force_val (`(sem_cast (typeof e2) (typeof e1)) (eval_expr e2))) -* P)))))
          (Clight.Sassign e1 e2)
          (normal_ret_assert P)
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

Ltac unfold_der := unfold overridePost, RA_normal, RA_break, RA_continue, RA_return in *.

Lemma semax_aux_seq_inv: forall CS Espec (Delta : tycontext) (P : environ -> mpred) 
      (R : ret_assert) (h t : Clight.statement),
    @semax_aux CS Espec Delta P (Clight.Ssequence h  t)%C R ->
    exists Q : environ -> mpred,
      @semax_aux CS Espec Delta P h (overridePost Q R) /\
      @semax_aux CS Espec Delta Q t R.
Proof.
  intros.
  remember (Clight.Ssequence h  t)%C as c.
  induction H;inversion Heqc.
  + subst. exists Q. auto.
  + specialize (IHsemax_aux H5).
    destruct IHsemax_aux as [Q [? ?]].
    exists Q. split.
    - eapply semax_aux_conseq;[..|apply H6];auto;
      destruct R as [Rn Rb Rc Rr];
      destruct R' as [Rn' Rb' Rc' Rr']; unfold_der;auto.
      solve_andp.
    - eapply semax_aux_conseq;[..|apply H7];auto;
      destruct R as [Rn Rb Rc Rr];
      destruct R' as [Rn' Rb' Rc' Rr']; unfold_der;auto.
      solve_andp.
Qed.


Lemma semax_aux_seq_inv': forall CS Espec (Delta : tycontext) (P : environ -> mpred) 
      (R : ret_assert) (h t : Clight.statement),
    @semax_aux CS Espec Delta P (Clight.Ssequence h  t)%C R ->
    @semax_aux CS Espec Delta P h
         (overridePost
            (EX Q : environ -> mpred,
             !! semax_aux Delta Q t R && Q)%assert R).
Proof.
  intros.
  remember (Clight.Ssequence h  t)%C as c.
  induction H;inversion Heqc.
  + subst. eapply semax_aux_conseq;[..|apply H];auto;
    destruct R as [Rn Rb Rc Rr]; unfold_der;auto;intros; try solve_andp.
    Exists Q. apply andp_right;try solve_andp. apply prop_right.
    auto.
  + specialize (IHsemax_aux H5).
    eapply semax_aux_conseq;[..|apply IHsemax_aux];auto;
      destruct R as [Rn Rb Rc Rr];
      destruct R' as [Rn' Rb' Rc' Rr']; unfold_der;auto.
    Intros Q. Exists Q.
    apply andp_right;try solve_andp. apply prop_right.
    eapply semax_aux_conseq;[..|apply H6];auto;
    unfold_der;auto.
    solve_andp.
Qed.

Lemma semax_aux_assign_inv: forall {CS: compspecs} {Espec: OracleKind} 
Delta e1 e2 P Q,
@semax_aux CS Espec Delta P (Clight.Sassign e1 e2) Q ->
local (tc_environ Delta) && (allp_fun_id Delta && P) |-- 
(EX sh: share, !! writable_share sh 
    && |> ( (tc_lvalue Delta e1) &&  (tc_expr Delta (Ecast e2 (typeof e1)))  &&
           ((`(mapsto_ sh (typeof e1)) (eval_lvalue e1)) * (`(mapsto sh (typeof e1)) (eval_lvalue e1) (`force_val (`(sem_cast (typeof e2) (typeof e1)) (eval_expr e2))) -* RA_normal Q)))).
Proof.
intros.
remember (Clight.Sassign e1 e2) as c eqn:?H.
induction H;try solve [inv H0].
+ inv H0. reduce2derives. Intros sh. Exists sh.
  apply andp_right. { apply prop_right. auto. }
  unfold normal_ret_assert. unfold RA_normal.
  apply later_derives; auto.
+ subst c. specialize (IHsemax_aux eq_refl).
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
    apply IHsemax_aux. }
  reduceR. Intros sh. Exists sh.
  apply andp_right.
  { apply prop_right. auto. }
  apply later_ENTAILL.
  apply andp_ENTAILL; [reduceLL; apply ENTAIL_refl |].
  apply sepcon_ENTAILL; [reduceLL; apply ENTAIL_refl |].
  apply wand_ENTAILL; [reduceLL; apply ENTAIL_refl |].
  auto.
Qed.


Lemma semax_aux_set_inv: forall {CS: compspecs} {Espec: OracleKind} Delta P R id e,
  @semax_aux CS Espec Delta P (Clight.Sset id e) R ->
  local (tc_environ Delta) && (allp_fun_id Delta && P) |-- 
    ( (|> ( (tc_expr Delta e) &&
             (tc_temp_id id (typeof e) Delta e) &&
             subst id (eval_expr e) (RA_normal R))) ||
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
          subst id (eval_expr (Ebinop cmp e1 e2 ty)) (RA_normal R)))) ||
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
    apply orp_derives; [apply orp_derives; [apply orp_derives |] |].
    - apply later_derives.
      apply andp_derives; auto.
      apply subst_derives. unfold normal_ret_assert.
      unfold RA_normal. auto.
    - apply exp_derives; intros cmp.
      apply exp_derives; intros e1.
      apply exp_derives; intros e2.
      apply exp_derives; intros ty.
      apply exp_derives; intros sh1.
      apply exp_derives; intros sh2.
      apply andp_derives; auto.
      apply later_derives; auto.
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
    rename P into Pre, R into Post. specialize (IHsemax_aux eq_refl).
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
      apply IHsemax_aux. }
      reduceR.
    apply orp_ENTAILL; [apply orp_ENTAILL; [apply orp_ENTAILL |] |].
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
    - apply exp_ENTAILL; intro cmp.
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
      * auto.
    - apply exp_ENTAILL; intro sh.
      apply exp_ENTAILL; intro t2.
      apply exp_ENTAILL; intro v2.
      normalize.
      (* destruct H0 as [? [? ?]].
      apply later_ENTAILL.
      unfold typeof_temp in H0.
      destruct ((temp_types Delta) ! id) eqn:?H; inv H0.
      eapply andp_subst_ENTAILL; [eauto | | reduceLL; apply ENTAIL_refl |].
      * reduceL.
        apply andp_left1.
        apply andp_left2.
        unfold_lift; unfold local, lift1; intro rho; simpl; normalize.
        intros _; eapply expr2.neutral_cast_subsumption; eauto.
      * apply derives_full_bupd0_left.
        auto.
    - apply exp_ENTAILL; intro sh.
      apply exp_ENTAILL; intro e1.
      apply exp_ENTAILL; intro t1.
      apply exp_ENTAILL; intro t2.
      normalize.
      destruct H0 as [He [? [? ?]]].
      apply later_ENTAILL.
      unfold typeof_temp in H0.
      destruct ((temp_types Delta) ! id) eqn:?H; inv H0.
      eapply andp_subst_ENTAILL; [eauto | | reduceLL; apply ENTAIL_refl |].
      * reduceL.
        apply andp_left1.
        apply andp_left2.
        unfold_lift; unfold local, lift1; intro rho; simpl; normalize.
        intros _; auto.
      * apply derives_full_bupd0_left.
        auto.
Qed. *)
Admitted.

(* Lemma wsh_relation: forall sh1 sh2 t e v Q1 Q2 ,
  writable_share sh1 -> writable_share sh2 ->
  (((mapsto sh1 t e v) -* Q1) && ((mapsto sh2 t e v) -* Q2) |--
  EX sh:share, !! (writable_share sh) &&  ((mapsto sh t e v) -* (Q1 && Q2))).
Proof.
  intros.
  hnf in H. destruct H .
  hnf in H. hnf in H1.
  Exists Tsh. apply andp_right.
  2:{ apply wand_frame_intro'.
      eapply derives_trans.
      { apply distrib_sepcon_andp. }
      apply andp_right.
      - apply andp_left1.
      Search mapsto.
        unfold mapsto at 1. Print access_mode.
        Print By_value.


        pose proof join_comp_Tsh.
        Search mapsto sepcon.
        Search sepcon derives.
      Search Tsh sepalg.join.
  Search sepcon andp.
  Search wand derives. }
  Search sepalg.identity. Search sepcon andp.
  unfold sepalg.identity in H.
  
  unfold writable_share.
  Search share. *)


(* Lemma semax_aux_assign_inv: forall {CS: compspecs} {Espec: OracleKind} 
  Delta e1 e2 P Q,
@semax_aux CS Espec Delta P (Clight.Sassign e1 e2) Q ->
  local (tc_environ Delta) && (allp_fun_id Delta && P) |-- 
  (EX sh: share, !! writable_share sh 
      && |> ( (tc_lvalue Delta e1) &&  (tc_expr Delta (Ecast e2 (typeof e1)))  &&
             ((`(mapsto_ sh (typeof e1)) (eval_lvalue e1)) * (`(mapsto sh (typeof e1)) (eval_lvalue e1) (`force_val (`(sem_cast (typeof e2) (typeof e1)) (eval_expr e2))) -* RA_normal Q)))).
Proof.
  intros.
  remember (Clight.Sassign e1 e2) as c eqn:?H.
  induction H;try solve [inv H0].
  + inv H0. reduce2derives. Exists sh.
    apply andp_right. { apply prop_right. auto. }
    unfold normal_ret_assert. unfold RA_normal. *)

(*

Lemma semax_aux_assign_inv_sh: forall {CS: compspecs} {Espec: OracleKind} 
  Delta e1 e2 P Q sh,
@semax_aux CS Espec Delta P (Clight.Sassign e1 e2) Q ->
  local (tc_environ Delta) && (allp_fun_id Delta && P) |-- 
  !! (writable_share sh) &&
  (|> ( (tc_lvalue Delta e1) &&  (tc_expr Delta (Ecast e2 (typeof e1))) 
    &&
             ((`(mapsto_ sh (typeof e1)) (eval_lvalue e1))))) ->
  local (tc_environ Delta) && (allp_fun_id Delta && P) |-- 
  (|> ( (tc_lvalue Delta e1) &&  (tc_expr Delta (Ecast e2 (typeof e1)))  &&
             ((`(mapsto_ sh (typeof e1)) (eval_lvalue e1)) * (`(mapsto sh (typeof e1)) (eval_lvalue e1) (`force_val (`(sem_cast (typeof e2) (typeof e1)) (eval_expr e2))) -* RA_normal Q)))).
Proof.
  intros. revert dependent sh.
  remember (Clight.Sassign e1 e2) as c eqn:?H.
  induction H;try solve [inv H0].
  + inv H0. intros sh'. intros.
    eapply derives_trans. apply H0.
  
  reduce2derives.
    apply later_derives; auto.
    apply andp_derives; auto.
    apply sepcon_derives; auto.
    { assert (exists sh1, sepalg.join sh' sh1 sh).
      { hnf in H. hnf in Hsh.
        destruct Hsh as [E1 E2].
        destruct H as [E3 E4]. hnf in E2. hnf in E4.
        destruct E2 as [sh1 E2].
        destruct E4 as [sh2 E4].
        hnf in E2. hnf in E4.
        destruct E2 as [E2 E5]. destruct E4 as [E4 E6].
        Search Share.glb Share.bot. unfold sepalg.join.
        unfold Share.Join_ba.V
(** lub (Rsh , sh2) = sh',  lub (Rsh , sh3) = sh
        gub (Rsh, sh2) = bot, lub (Rsh, sh3) = bot

        
        ? = glb (sh2, sh3)?
        lub (lub (Rsh , sh2), ?) = lub (Rsh , sh3)
        /\  glb (lub (Rsh , sh2), ?) = bot
        
        lub (sh', ?) = sh, gub (sh', ?) = bot

      
      
      Goal: join (sh', ?) = sh *)


        exists (Share.glb (Share.lub sh1 sh2) Share.Rsh).
        hnf.
        split.
        (* - unfold nonempty_share. rewrite Share.distrib1.
          hnf in E1. hnf in E3.
          apply identityToken' in C. apply Share.identityToken in C.
          apply lub_bot_e in C. destruct C.
          apply Share.identityToken in H1. apply identityToken' in H1. contradiction.
        - hnf.  hnf in E2. hnf in E4.
          destruct E2 as [sh3 E2]. destruct E4 as [sh4 E4].
          unfold sepalg.join in *. unfold Share.Join_ba in *.
          exists (Share.lub sh3 sh4). destruct E2 as [E5 E6]. destruct E4 as [E7 E8]. *)
          (* split. *)
          + rewrite <- E6.
            rewrite Share.glb_commute.
            rewrite Share.distrib1.
            admit.
          + rewrite <- E5. rewrite <- E6.
            rewrite Share.distrib2.
            Search Share.glb. Share.lub.
          
          rewrite Share.lub_commute.
            rewrite (Share.lub_commute sh1 sh2).
            rewrite <- Share.distrib2. rewrite E2.
            apply Share.lub_bot.
          + rewrite <- E6. rewrite <- E8.
            rewrite (Share.lub_commute (Share.Rsh) sh3).
            rewrite Share.lub_assoc. rewrite <- (Share.lub_assoc Share.Rsh Share.Rsh).
            rewrite Share.lub_idem. rewrite <- (Share.lub_assoc sh3).
            rewrite (Share.lub_commute (sh3) (Share.Rsh)).
            rewrite Share.lub_assoc. reflexivity.



       }

      Search sepalg.join sepalg.join_sub.
      Search Share.glb sepalg.join.
      
      unfold sepalg.join_sub in H.
      unfold sepalg.join in H.
      unfold Share.Join_ba in H.
      
      
      
      
      Search mapsto Share.t. }
    apply wand_derives; auto.
    apply derives_refl.
  + subst c. specialize (IHsemax_aux eq_refl).
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
      apply IHsemax_aux. }
    reduceR. Intros sh. Exists sh.
    apply andp_right.
    { apply prop_right. auto. }
    apply later_ENTAILL.
    apply andp_ENTAILL; [reduceLL; apply ENTAIL_refl |].
    apply sepcon_ENTAILL; [reduceLL; apply ENTAIL_refl |].
    apply wand_ENTAILL; [reduceLL; apply ENTAIL_refl |].
    auto.
Qed. *)


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



Lemma mapsto_wand_reduce: forall sh1 sh2 t p v Q,
  sepalg.join_sub sh1 sh2 ->
  mapsto sh2 t p v * (mapsto sh2 t p v  -* Q) 
  |-- mapsto sh1 t p v  * (mapsto sh1 t p v  -* Q).
Proof.
  intros. destruct H.
  rewrite <- (mapsto_share_join _ _ _ t p v H).
  rewrite sepcon_assoc.
  apply sepcon_derives;auto.
  apply wand_frame_intro'.
  rewrite <- !sepcon_assoc.
  rewrite (mapsto_share_join _ _ _ t p v H).
  apply wand_frame_elim.
Qed.


Lemma mapsto_at_share_join_W:
  forall sh1 sh2 sh t v v1 v2,
  sepalg.join sh1 sh2 sh ->
  writable_share sh1 -> tc_val' t v1 ->
  mapsto sh1 t v v1  * mapsto sh2 t v v2
  |-- (mapsto sh t v v1).
Proof.
  intros.
  rewrite <- (mapsto_share_join _ _ _ t v v1 H).
  apply sepcon_derives;auto.
  pose proof join_writable_readable H H0.
  unfold mapsto. destruct (access_mode t);auto.
  destruct (type_is_volatile t);auto.
  destruct v eqn:E;auto. if_tac;try tauto.
  unfold tc_val'. apply andp_derives.
  2:{ apply derives_refl. } apply prop_derives.
  intros. destruct H4. split;auto.
Qed.

Lemma mapsto_wand_reduce_writable: forall sh1 sh2 t p v1 v2 Q,
  writable_share sh1 ->
  sepalg.join_sub sh1 sh2 ->
  mapsto sh2 t p v1 * (mapsto sh2 t p v2  -* Q) 
  |-- mapsto sh1 t p v1  * (mapsto sh1 t p v2  -* Q).
Proof.
  intros. destruct H0.
  rewrite <- (mapsto_share_join _ _ _ t p v1 H0).
  rewrite sepcon_assoc.
  apply sepcon_derives;auto.
  apply wand_frame_intro'.
  rewrite <- !sepcon_assoc.
  eapply derives_trans.
  { apply sepcon_derives.
    - assert_PROP (tc_val' t v2).
      { sep_apply (mapsto_tc_val'). Intros. apply prop_right. auto. }
      apply mapsto_at_share_join_W; eassumption.
    - apply derives_refl.
  }
  apply wand_frame_elim.
Qed.
(* Lemma mapsto_wand_reduce_writable: forall sh1 sh2 t p v1 v2 Q,
  writable_share sh1 ->
  sepalg.join_sub sh1 sh2 -> tc_val' t v2 ->
(` (mapsto_ sh2 (typeof e))) (eval_lvalue e) *
((` (mapsto sh2 (typeof e))) (eval_lvalue e)
   ((` force_val) ((` (sem_cast (typeof e0) (typeof e))) (eval_expr e0))) -*
 Q1)
 |-- 
 (` (mapsto_ sh1 (typeof e))) (eval_lvalue e) *
 ((` (mapsto sh1 (typeof e))) (eval_lvalue e)
    ((` force_val) ((` (sem_cast (typeof e0) (typeof e))) (eval_expr e0))) -*
  Q1). *)

(* Lemma ws: writable_share Share.Rsh.
Proof.
  hnf. split.
  - hnf.
    intros C. apply identity_share_bot in C.
    Search Share.glb Share.Lsh.
  Search sepalg.identity Share.t. intros C. hnf in C.
    Search Share.

Search writable_share. *)


Lemma share_split_eq: forall sh,
  sh = Share.lub (fst (Share.split sh)) (snd (Share.split sh)).
Proof.
  intros. 
  pose proof Share.split_together (fst (Share.split sh)) (snd (Share.split sh)) sh.
  destruct (Share.split sh). rewrite <- H;auto.
Qed.

Lemma writable_share_join: forall sh1 sh2, writable_share sh1 ->
  writable_share sh2 -> exists sh',
  sepalg.join_sub sh' sh1 /\ sepalg.join_sub sh' sh2 /\ writable_share sh'.
Proof.
  intros.
  destruct H as [E1 E2].
  destruct H0 as [E4 E5].
  destruct E2 as [sh1r [E2 E3]]. destruct E5 as [sh2r [E5 E6]].
  exists (Share.lub Share.Rsh (Share.glb sh1r sh2r)).
  repeat split.
  + exists (Share.glb sh1r (Share.comp sh2r)).
    repeat split.
    * rewrite Share.glb_commute. rewrite Share.distrib1.
      rewrite Share.glb_commute at 1.
      rewrite <- (Share.glb_assoc Share.Rsh).
      rewrite E2. rewrite Share.glb_commute. rewrite Share.glb_bot.
      rewrite Share.lub_commute.
      rewrite Share.lub_bot. rewrite Share.glb_assoc.
      rewrite (Share.glb_commute _ sh2r).
      rewrite <- (Share.glb_assoc _ sh2r).
      rewrite (Share.glb_commute _ sh2r).
      rewrite Share.comp2. rewrite (Share.glb_commute Share.bot). rewrite Share.glb_bot.
      rewrite Share.glb_bot. reflexivity.
    * rewrite Share.lub_assoc. rewrite <- E3.
      f_equal. rewrite <- Share.distrib1. rewrite Share.comp1.
      rewrite Share.glb_top. reflexivity.
  + exists (Share.glb sh2r (Share.comp sh1r)).
    repeat split.
    * rewrite Share.glb_commute. rewrite Share.distrib1.
      rewrite Share.glb_commute at 1.
      rewrite <- (Share.glb_assoc Share.Rsh).
      rewrite E5. rewrite Share.glb_commute. rewrite Share.glb_bot.
      rewrite Share.lub_commute.
      rewrite Share.lub_bot. rewrite Share.glb_assoc.
      rewrite <- (Share.glb_assoc _ sh1r).
      rewrite (Share.glb_commute _ sh1r).
      rewrite Share.comp2. rewrite (Share.glb_commute Share.bot). rewrite Share.glb_bot.
      rewrite Share.glb_bot. reflexivity.
    * rewrite Share.lub_assoc. rewrite <- E6.
      f_equal. rewrite (Share.glb_commute sh1r). rewrite <- Share.distrib1.
      rewrite Share.comp1.
      rewrite Share.glb_top. reflexivity.
  + rewrite Share.distrib1.
    rewrite glb_Lsh_Rsh. rewrite Share.lub_commute.
    rewrite Share.lub_bot. hnf.
    intros. apply identity_share_bot in H.
    admit.
  + exists (Share.glb sh1r sh2r).
    split;auto. rewrite <- Share.glb_assoc. rewrite E2.
    rewrite Share.glb_commute. rewrite Share.glb_bot. reflexivity.
Admitted.


(* Lemma writable_share_ews: forall sh, writable_share sh ->
  sepalg.join_sub Ews sh.
Proof.
  intros. destruct H.
  hnf in H. unfold Ews.
  destruct H0 as [sh' H0].
  hnf in H0. destruct H0. hnf.
  unfold extern_retainer. exists (Share.lub (snd (Share.split Share.Lsh)) sh').
  { split.
    - rewrite share_distrib1'.
      rewrite H0. rewrite glb_split.
      rewrite Share.lub_bot. rewrite lub_bot'.
      pose proof glb_Rsh_Lsh.
      pose proof Share.split_together (fst (Share.split Share.Lsh)) (snd (Share.split Share.Lsh)) Share.Lsh.
      assert (Share.split Share.Lsh =
      (fst (Share.split Share.Lsh), snd (Share.split Share.Lsh)) ).
      { destruct (Share.split Share.Lsh). reflexivity. }
      specialize (H3 H4). clear H4.
      pose proof Share.split_together (fst (Share.split sh')) (snd (Share.split sh')) sh'.
      assert (Share.split sh' = (fst (Share.split sh'), snd (Share.split sh'))).
      { destruct (Share.split sh'). reflexivity. }
      specialize (H4 H5). clear H5.
      rewrite <- H3 in H2. rewrite Share.distrib1 in H2.
      apply lub_bot_e in H2. destruct H2.
      rewrite <- H4 in H0. rewrite Share.distrib1 in H0.
      apply lub_bot_e in H0. destruct H0.
      rewrite H5. rewrite Share.glb_commute. rewrite 
        Search Share.lub Share.bot.
        Search Share.glb Share.lub.
      }

      rewrite <- H3 at 1.
      2:{ destruct (Share.split Share.Lsh). reflexivity.  }
      simpl.
      
      eq_refl.
      Search Share.split Share.lub.
      Search Share.glb Share.Rsh Share.Lsh.
      Search Share.split Share.glb.


    Search Share.glb Share.lub.  }
  
  exists Wsh.
  split;auto.
Qed. *)

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
    { unfold RA_normal.  solve_andp. }
    { unfold RA_break. repeat apply andp_left2. apply FF_left. }
    { unfold RA_continue. repeat apply andp_left2. apply FF_left. }
    { intros. unfold RA_return. repeat apply andp_left2. apply FF_left. }
    apply semax_aux_skip.
  - intros. destruct Q as [Qn Qb Qc Qr]. unfold_der.
    apply semax_aux_assign_inv in H0.
    apply semax_aux_assign_inv in H. unfold_der.
    assert (semax_aux Delta P (Clight.Sassign e e0)%C
    {| RA_normal := Q1 && Q2;
      RA_break := FF;
      RA_continue := FF;
      RA_return := FF |}).
    { eapply semax_aux_conseq;
       [..|apply semax_aux_assign with (P0:= Q1 && Q2)];
        unfold normal_ret_assert;unfold_der;try (intros; solve_andp).
      { pose proof andp_ENTAILL _ _ _ _ _ H0 H.
        rewrite andp_dup in H1.
        eapply derives_trans;[apply H1|]. clear H1.
        Intros sh1. Intros sh2.
        pose proof writable_share_join _ _ H1 H2.
        destruct H3 as [sh' [E1 [E2 E3]]].
        Exists sh'. apply andp_right.
        { apply prop_right. auto. }
        rewrite <- later_andp.
        apply later_derives.
        repeat apply andp_right; try solve_andp.
        rewrite andp_assoc. apply andp_left2. unfold liftx. simpl. unfold lift.
        unfold mapsto_. intros x.
        eapply derives_trans.
        { apply andp_derives.
          { apply mapsto_wand_reduce_writable; try eassumption. }
          apply andp_derives.
          { apply derives_refl. }
          { apply mapsto_wand_reduce_writable; try eassumption. }
        } (* typecheck envrion? => tc_val t v2 *)
        admit.
      }
    }
    eapply semax_aux_noreturn_inv with (Post:={|
      RA_normal := Q1 && Q2; RA_break := Qb; RA_continue := Qc; RA_return := FF
    |});auto.
    eapply semax_aux_nocontinue_inv with (Post:={|
      RA_normal := Q1 && Q2; RA_break := Qb; RA_continue := FF; RA_return := FF
    |});auto.
    eapply semax_aux_nobreak_inv with (Post:={|
      RA_normal := Q1 && Q2; RA_break := FF; RA_continue := FF; RA_return := FF
    |});auto.
  - intros. destruct Q as [Qn Qb Qc Qr]. unfold_der.
    apply semax_aux_set_inv in H0.
    apply semax_aux_set_inv in H. unfold_der.
    assert (semax_aux Delta P (Clight.Sset i e)%C
    {| RA_normal := Q1 && Q2;
      RA_break := FF;
      RA_continue := FF;
      RA_return := FF |}).
    { eapply semax_aux_conseq;
      [..|apply semax_aux_set_ptr_compare_load_cast_load_backward with (P0:= Q1 && Q2)];
        unfold normal_ret_assert;unfold_der;try (intros; solve_andp).
      { pose proof andp_ENTAILL _ _ _ _ _ H0 H.
        rewrite andp_dup in H1.
        eapply derives_trans;[apply H1|]. clear H1.
        rewrite !distrib_orp_andp. repeat apply orp_left.
        + rewrite andp_comm. rewrite !distrib_orp_andp.
          repeat apply orp_left.
          * apply orp_right1. apply orp_right1.
            apply orp_right1. rewrite <- later_andp.
            apply later_derives. rewrite subst_andp.
            solve_andp.
          * eapply derives_trans;[|apply FF_left].
            Intros cmp e1 e2 ty sh1 sh2.
            admit.
          * admit.
          * admit.
        + rewrite andp_comm. rewrite !distrib_orp_andp.
          repeat apply orp_left.
          * admit.
          * apply orp_right1. apply orp_right1.
            apply orp_right2. 
            Intros cmpa e1a e2a tya sh1a sh2a.
            Intros cmpb e1b e2b tyb sh1b sh2b.
            rewrite <- later_andp.
            Search TT sepcon.
            apply later_derives. rewrite subst_andp.
            solve_andp.
            unfold tc_temp_id.
            unfold typecheck_temp_id.
            destruct ((temp_types Delta) ! i) eqn:E.
            2:{  unfold tc_FF. }
            unfold denote_tc_assert.
            Search tc_temp_id.
            Search tc_expr Ebinop.
            unfold tc_temp_id.
            unfold typecheck_temp_id.
            unfold temp_types.
          Search derives FF.
            Search subst andp. solve_andp.
        Search andp orp.



        (* Intros sh1. Intros sh2.
        pose proof writable_share_join _ _ H1 H2.
        destruct H3 as [sh' [E1 [E2 E3]]].
        Exists sh'. apply andp_right. *)
        (* { apply prop_right. auto. } *)
        
        apply andp_right. try solve_andp.
        apply later_derives.
        repeat apply andp_right; try solve_andp.
        rewrite andp_assoc. apply andp_left2. unfold liftx. simpl. unfold lift.
        unfold mapsto_. intros x.
        eapply derives_trans.
        { apply andp_derives.
          { apply mapsto_wand_reduce_writable; try eassumption. }
          apply andp_derives.
          { apply derives_refl. }
          { apply mapsto_wand_reduce_writable; try eassumption. }
        } (* typecheck envrion? => tc_val t v2 *)
        admit.
      }
    }
    
  intros.
    
      { solve_andp. }
          
            Search force_val sem_cast.


            + Search typecheck_environ. auto.
            Check predicates_hered.app_pred.
            Print juicy_mem.juicy_mem.
            Check typecheck_environ.
            Search tc_val force_val.
            unfold tc_val'. intros. unfold force_val in *.
            destruct (typeof e0), (typeof e);simpl in H3.
            unfold sem_cast.
            simpl.
            
            Search tc_val force_val.
        }
        
        simpl.
        
        simpl.
        unfold mapsto_.
        rewrite andp_comm. intros r. simpl.
          assert_PROP (tc_val' (typeof e) (eval_lvalue e r)).
          { admit. }
          eapply derives_trans.
          { eapply andp_derives.
            eapply andp_derives. { apply derives_refl. }
            Search Ews.
            Search juicy_mem.perm_of_sh.
            apply mapsto_wand_reduce_writable.


          }
          eapply derives_andp. 
          unfold mapsto_. simpl.
          rewrite <-andp_assoc. apply andp_left1.
          Search later andp.
          Search andp.
          Search allp_fun_id andp derives.

           hnf. destruct H1 as [E1 E2]. destruct H2 as [E3 E4].
          split.
          - unfold nonempty_share. rewrite Share.distrib1.
            hnf in E1. hnf in E3. intros C. Search sepalg.identity.
            apply identityToken' in C. apply Share.identityToken in C.
            apply lub_bot_e in C. destruct C.
            apply Share.identityToken in H1. apply identityToken' in H1. contradiction.
          - hnf.  hnf in E2. hnf in E4.
            destruct E2 as [sh3 E2]. destruct E4 as [sh4 E4].
            unfold sepalg.join in *. unfold Share.Join_ba in *.
            exists (Share.lub sh3 sh4). destruct E2 as [E5 E6]. destruct E4 as [E7 E8].
            split.
            + rewrite Share.distrib1. rewrite E5. rewrite E7. apply Share.lub_bot.
            + rewrite <- E6. rewrite <- E8.
              rewrite (Share.lub_commute (Share.Rsh) sh3).
              rewrite Share.lub_assoc. rewrite <- (Share.lub_assoc Share.Rsh Share.Rsh).
              rewrite Share.lub_idem. rewrite <- (Share.lub_assoc sh3).
              rewrite (Share.lub_commute (sh3) (Share.Rsh)).
              rewrite Share.lub_assoc. reflexivity.
         }
         rewrite andp_assoc.
         rewrite <- later_andp. rewrite andp_assoc.
         eapply derives_trans.
         { apply andp_right.
          + rewrite <- andp_assoc. apply andp_left1.
            rewrite <- andp_assoc. apply andp_left1. apply derives_refl.
          + apply andp_left2. apply andp_left2. apply derives_refl. }
        rewrite andp_assoc.
        Search writable_share.
        Search mapsto sepcon.
        Search sepalg.joins Share.t.
        Search sepalg.join Share.t.
        Search sepalg.Join Share.t.
        
        
        Search mapsto Share.t.
         apply later_ENTAILL. apply andp_right;try solve_andp.
         Search sepcon.
         eapply andp_right.
         Print andp_right.

         (sepcon (liftx (mapsto_ (Share.lub sh1 sh2) (typeof e)) (eval_lvalue e))
     (wand (liftx (mapsto (Share.lub sh1 sh2) (typeof e)) (eval_lvalue e) (liftx force_val (liftx (sem_cast (typeof e0) (typeof e)) (eval_expr e0))))
        (andp Q1 Q2)))
         apply andp_right.
         
         Search mapsto Share.t.
Search mapsto mapsto_.
         ((` (mapsto_ sh2 (typeof e))) (eval_lvalue e) *
         ((` (mapsto sh2 (typeof e))) (eval_lvalue e) ((` force_val) ((` (sem_cast (typeof e0) (typeof e))) (eval_expr e0))) -* Q1))

         Search sepalg.join ex.
         Search sepalg.joins.
         apply wand_ENTAILL.
         Search "-*" andp. apply wand_ENTAIL.

         Search later andp.
          Search Share.lub sepalg.identity.
            hnf.
          simpl.
        
        }
        Print writable_share.
        Search Share.lub writable_share.
        Search Share.t.
        Check sepalg.join.
        Search share.
      }
      { unfold normal_ret_assert. unfold RA_normal. solve_andp. }
      { unfold normal_ret_assert. unfold RA_break. solve_andp. }
      
      2:{ unfold normal_ret_assert in HeqQ'. unfold_der. }
      Search FF derives.

  
  
  
  admit.
  - admit.
  - admit.
  - admit.
  - intros. apply semax_aux_seq_inv in H0.
    apply semax_aux_seq_inv in H.
    destruct Q as [Qn Qb Qc Qr]. unfold_der.
    destruct H0 as [R1 [? ?]].
    destruct H as [R2 [? ?]].
    specialize (IHc1 _ _ H _ H0).
    eapply semax_aux_seq with (Q:= R1 && R2).
    { unfold_der. auto. }
    apply IHc2.
    { eapply semax_aux_conseq;[..|apply H1];auto;unfold_der;try intros;solve_andp. }
    { eapply semax_aux_conseq;[..|apply H2];auto;unfold_der;try intros;solve_andp. }
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