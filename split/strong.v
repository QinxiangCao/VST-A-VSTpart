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
Require Import Split.model_lemmas.

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

Ltac unfold_der := unfold normal_ret_assert,
  overridePost, RA_normal, RA_break, RA_continue, RA_return in *.

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
      normalize. apply andp_right.
      { apply prop_right. auto. }
      { apply later_ENTAILL.
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
      normalize. apply andp_right.
      { apply prop_right. auto. }
      apply later_ENTAILL.
      unfold typeof_temp in H0.
      destruct ((temp_types Delta) ! id) eqn:?H; inv H0.
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


(* Lemma share_split_eq: forall sh,
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
Admitted. *)

Lemma semax_aux_conj_skip: forall CS Espec Delta P Q Q1 Q2,
  @semax_aux CS Espec Delta P Clight.Sskip (overridePost Q2 Q) ->
  @semax_aux CS Espec Delta P Clight.Sskip (overridePost Q1 Q) ->
  @semax_aux CS Espec Delta P Clight.Sskip (overridePost (Q1 && Q2) Q).
Proof.
  intros.
  destruct Q as [Qn Qb Qc Qr].
  unfold overridePost in *.
  apply semax_aux_skip_inv in H0.
  apply semax_aux_skip_inv in H.
  eapply semax_aux_conseq with (P':= andp (Q1) (Q2))
  (R':= (normal_ret_assert (andp (Q1) (Q2)))); unfold normal_ret_assert.
  { apply andp_right.
    { eapply derives_trans;[|apply H0]. solve_andp. }
    { eapply derives_trans;[|apply H]. solve_andp. }
  }
  { unfold RA_normal.  solve_andp. }
  { unfold RA_break. repeat apply andp_left2. apply FF_left. }
  { unfold RA_continue. repeat apply andp_left2. apply FF_left. }
  { intros. unfold RA_return. repeat apply andp_left2. apply FF_left. }
  apply semax_aux_skip.
Qed.

Lemma share_lub_writable: forall sh1 sh2,
  writable_share sh1 -> writable_share sh2 ->
  writable_share (Share.lub sh1 sh2).
Proof.
  intros. eapply join_writable1.
  2:{ apply H. }
  apply two_share_join.
Qed.

Lemma mapsto_join_andp_write_logic: forall sh1 sh2 t p P1 P2,
(* tc_val t v2 -> can't be undefined *)
writable_share sh1 -> writable_share sh2 ->
(mapsto_ sh1 t p * (ALL v', mapsto sh1 t p v' -* P1)) && 
(mapsto_ sh2 t p * (ALL v', mapsto sh2 t p v' -* P2))
|-- EX (sh':share), 
(mapsto_ sh' t p * (ALL v', mapsto sh' t p v' -* (P1 && P2))).
Proof.
  intros.
  apply mapsto_join_andp_write;auto.
Qed.

Lemma mapsto_join_andp_write_det_logic: forall sh1 sh2 t p P1 P2 v',
tc_val t v' -> 
writable_share sh1 -> writable_share sh2 ->
(mapsto_ sh1 t p * (mapsto sh1 t p v' -* P1)) && 
(mapsto_ sh2 t p * (mapsto sh2 t p v' -* P2))
|-- 
(mapsto_ (Share.lub sh1 sh2) t p * (mapsto (Share.lub sh1 sh2) t p v' -* (P1 && P2))).
Proof.
  intros.
  apply mapsto_join_andp_write_det;auto.
Qed.

Lemma semax_aux_conj_assign: forall CS Espec Delta P Q Q1 Q2 e e0,
  @semax_aux CS Espec Delta P (Clight.Sassign e e0) 
    (overridePost Q2 Q) ->
  @semax_aux CS Espec Delta P (Clight.Sassign e e0) 
    (overridePost Q1 Q) ->
  @semax_aux CS Espec Delta P (Clight.Sassign e e0) 
    (normal_ret_assert (Q1 && Q2)).
Proof.
  intros.
  destruct Q as [Qn Qb Qc Qr]. unfold_der.
  apply semax_aux_assign_inv in H0.
  apply semax_aux_assign_inv in H. unfold_der.
  eapply semax_aux_conseq;
    [..|apply semax_aux_assign with (P0:= Q1 && Q2)];
    unfold normal_ret_assert;unfold_der;try (intros; solve_andp).
  pose proof andp_ENTAILL _ _ _ _ _ H0 H.
  rewrite andp_dup in H1.
  eapply ENTAIL_trans;[apply H1|]. clear H1.
  Intros sh1. Intros sh2.
  Exists (Share.lub sh1 sh2).
  apply andp_right. { apply prop_right. apply share_lub_writable;auto. }
  rewrite <- later_andp.
  apply later_ENTAIL.
  repeat apply andp_right; try solve_andp.
  intros r.
  assert_PROP (tc_val (typeof e)
  ((` force_val) ((` (sem_cast (typeof e0) (typeof e))) (eval_expr e0)) r)).
  { unfold tc_environ. simpl. unfold local.
    unfold lift1. Intros.
    eapply derives_trans;[| 
      apply (typecheck_expr_sound _ _ (Ecast e0 (typeof e)) H3)].
    solve_andp. }
  eapply derives_trans.
  2:{ eapply (mapsto_join_andp_write_det_logic _ _ (typeof e) ((eval_lvalue e) r) (Q1 r) (Q2 r) ((` force_val) ((` (sem_cast (typeof e0) (typeof e))) (eval_expr e0)) r));auto. } simpl.
  solve_andp.
Qed.


Theorem semax_aux_conj_rule: forall  CS Espec Delta P Q c Q1 Q2 ,
  @semax_aux CS Espec Delta P c (overridePost Q1 Q) ->
  @semax_aux CS Espec Delta P c (overridePost Q2 Q) ->
  @semax_aux CS Espec Delta P c (overridePost (andp Q1 Q2) Q).
Proof.
  intros. revert dependent Q1.
  revert dependent Q2. revert dependent P .
  induction c.
  - intros. eapply semax_aux_conj_skip;eassumption.
  - intros.
    eapply semax_aux_conseq;
    [..|eapply semax_aux_conj_assign with (Q1:=Q1) (Q2:=Q2);eassumption];
    destruct Q as [Qn Qb Qc Qr]; unfold_der;try solve_andp;
    intros;eapply derives_trans with (Q:=FF);
      try solve_andp;try (apply FF_left).
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