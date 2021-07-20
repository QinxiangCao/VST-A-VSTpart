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
Require Import VST.floyd.SeparationLogicFacts.
Require Import VST.floyd.SeparationLogicAsLogic.
Export SeparationLogicAsLogicSoundness.MainTheorem.CSHL_Sound.DeepEmbedded.
Require Import VST.floyd.proofauto.
Import Ctypes LiftNotation.
Local Open Scope logic.
Require Import Split.vst_ext.
Require Import Split.model_lemmas.

(* Definition obox (Delta: tycontext) (i: ident) (P: environ -> mpred): environ -> mpred :=
  ALL v: _,
    match ((temp_types Delta) ! i) with
    | Some t => !! (tc_val' t v) --> subst i (`v) P
    | _ => TT
    end.

Definition oboxopt Delta ret P :=
  match ret with
  | Some id => obox Delta id P
  | _ => P
  end. *)

Definition decode_encode_val_ok (chunk1 chunk2: memory_chunk) : Prop :=
  match chunk1, chunk2 with
  | Mint8signed, Mint8signed => True
  | Mint8unsigned, Mint8signed => True
  | Mint8signed, Mint8unsigned => True
  | Mint8unsigned, Mint8unsigned => True
  | Mint16signed, Mint16signed => True
  | Mint16unsigned, Mint16signed => True
  | Mint16signed, Mint16unsigned => True
  | Mint16unsigned, Mint16unsigned => True
  | Mint32, Mfloat32 => True
  | Many32, Many32 => True
  | Many64, Many64 => True
  | Mint32, Mint32 => True
  | Mint64, Mint64 => True
  | Mint64, Mfloat64 => True
  | Mfloat64, Mfloat64 =>  True
  | Mfloat64, Mint64 =>  True
  | Mfloat32, Mfloat32 =>  True
  | Mfloat32, Mint32 =>  True
  | _,_ => False
  end.

Lemma decode_encode_val_ok_trans ch1 ch2 ch3:
  decode_encode_val_ok ch1 ch2 ->
  decode_encode_val_ok ch2 ch3 ->
  decode_encode_val_ok ch1 ch3.
Proof.
  intros.
  destruct ch1, ch2; try solve [inv H]; destruct ch3; try solve [inv H0]; constructor.
Qed.


Lemma decode_encode_val_ok_symm ch1 ch2:
  decode_encode_val_ok ch1 ch2 ->
  decode_encode_val_ok ch2 ch1.
Proof.
  intros.
  destruct ch1, ch2; try solve [inv H]; constructor.
Qed.

Definition numeric_type (t: type) : bool :=
  match t with
  | Tint IBool _ _ => false
  | Tint _ _ _ => true
  | Tlong _ _ => true
  | Tfloat _ _ => true
  | _ => false
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
  ((EX sh: share, !! writable_share sh &&
      |> ( (tc_lvalue Delta e1) &&  (tc_expr Delta (Ecast e2 (typeof e1)))  &&
      ((`(mapsto_ sh (typeof e1)) (eval_lvalue e1)) *
       (`(mapsto sh (typeof e1)) (eval_lvalue e1) (`force_val (`(sem_cast (typeof e2) (typeof e1)) (eval_expr e2))) -* P))))
  )
  (Clight.Sassign e1 e2) (normal_ret_assert P)
| semax_aux_set_ptr_compare_load_cast_load_backward: forall (P: environ->mpred) id e,
    @semax_aux CS Espec Delta
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
| semax_aux_conseq: forall P' (R': ret_assert) P c (R: ret_assert) ,
    (local (tc_environ Delta) && (allp_fun_id Delta && P) |-- P') ->
    local (tc_environ Delta) && (allp_fun_id Delta && RA_normal R') |-- RA_normal R ->
    local (tc_environ Delta) && (allp_fun_id Delta && RA_break R') |-- RA_break R ->
    local (tc_environ Delta) && (allp_fun_id Delta && RA_continue R') |-- RA_continue R ->
    (forall vl, local (tc_environ Delta) && (allp_fun_id Delta && RA_return R' vl) |-- RA_return R vl) ->
    @semax_aux CS Espec Delta P' c R' -> @semax_aux CS Espec Delta P c R

| semax_aux_builtin: forall P opt ext tl el, @semax_aux CS Espec Delta FF (Clight.Sbuiltin opt ext tl el) P
(* | semax_aux_call: forall P ret a bl, @semax_aux CS Espec Delta FF (Clight.Scall ret a bl) P *)
| semax_aux_call: forall ret a bl R,
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
| semax_aux_label: forall (P:environ -> mpred) (c:Clight.statement) (Q:ret_assert) l,
  @semax_aux CS Espec Delta P c Q ->
  @semax_aux CS Espec Delta P (Clight.Slabel l c) Q
| semax_aux_goto: forall P l, @semax_aux CS Espec Delta FF (Clight.Sgoto l) P
| semax_aux_switch: forall  a sl R,
     (* (Q: environ->mpred)
     (forall rho, Q rho |-- tc_expr Delta a rho) ->
     (forall n,
     @semax CS Espec Delta 
               (local (`eq (eval_expr a) `(Vint n)) &&  Q)
               (seq_of_labeled_statement (select_switch (Int.unsigned n) sl))
               (switch_ret_assert R)) -> *)
     (* @semax CS Espec Delta (!! (is_int_type (typeof a) = true) && Q)  *)
     @semax_aux CS Espec Delta FF (Clight.Sswitch a sl) R.



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


Lemma allp_ENTAILL: forall Delta B (P Q: B -> environ -> mpred),
  (forall x: B, local (tc_environ Delta) && (allp_fun_id Delta && P x) |-- Q x) ->
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


Lemma semax_aux_assign_inv: forall {CS: compspecs} {Espec: OracleKind} 
Delta e1 e2 P Q,
@semax_aux CS Espec Delta P (Clight.Sassign e1 e2) Q ->
local (tc_environ Delta) && (allp_fun_id Delta && P) |-- 
((EX sh: share, !! writable_share sh &&
        |> ( (tc_lvalue Delta e1) &&  (tc_expr Delta (Ecast e2 (typeof e1)))  &&
        ((`(mapsto_ sh (typeof e1)) (eval_lvalue e1)) *
        (`(mapsto sh (typeof e1)) (eval_lvalue e1) (`force_val (`(sem_cast (typeof e2) (typeof e1)) (eval_expr e2))) -* RA_normal Q))))
  ).
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
    reduceR. 
    apply exp_ENTAILL; intro sh.
    apply andp_ENTAILL; [reduceLL; apply ENTAIL_refl |].
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
      (* (EX cmp: Cop.binary_operation, EX e1: expr, EX e2: expr,
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
          subst id (eval_expr (Ebinop cmp e1 e2 ty)) (RA_normal R)))) || *)
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
    (* - apply exp_derives; intros cmp.
      apply exp_derives; intros e1.
      apply exp_derives; intros e2.
      apply exp_derives; intros ty.
      apply exp_derives; intros sh1.
      apply exp_derives; intros sh2.
      apply andp_derives; auto.
      apply later_derives; auto.
      apply andp_derives; auto.
      apply subst_derives. unfold normal_ret_assert.
      unfold RA_normal. auto. *)
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
match sl with Clight.LSnil => true | Clight.LScons _ s sl' => if noreturn s then noreturn_ls sl' else false
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
match sl with Clight.LSnil => true | Clight.LScons _ s sl' => if nocontinue s then nocontinue_ls sl' else false
end.

Lemma noreturn_ls_spec: forall sl, noreturn_ls sl = true -> noreturn (seq_of_labeled_statement sl) = true.
Proof.
  intros.
  induction sl.
  + reflexivity.
  + simpl in *.
    destruct (noreturn s); [| inv H].
    auto.
Qed.

Lemma noreturn_ls_spec': forall sl n, noreturn_ls sl = true -> noreturn (seq_of_labeled_statement (select_switch n sl)) = true.
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

Lemma semax_aux_post: forall (R' : ret_assert) (Espec : OracleKind) 
      (cs : compspecs) (Delta : tycontext) (R : ret_assert)
      (P : environ -> mpred) (c : Clight.statement),
    ENTAIL Delta, RA_normal R' |-- RA_normal R ->
    ENTAIL Delta, RA_break R' |-- RA_break R ->
    ENTAIL Delta, RA_continue R' |-- RA_continue R ->
    (forall vl : option val,
     ENTAIL Delta, RA_return R' vl |-- RA_return R vl) ->
    semax_aux Delta P c R' -> semax_aux Delta P c R.
Proof.
  intros.
  eapply semax_aux_conseq;[..|apply H3];try solve_andp.
  - intros. eapply derives_trans;[|apply H]. solve_andp.
  - intros. eapply derives_trans;[|apply H0]. solve_andp.
  - intros. eapply derives_trans;[|apply H1]. solve_andp.
  - intros. eapply derives_trans;[|apply H2]. solve_andp.
Qed.


Lemma derives_aux_refl : forall (Delta : tycontext) 
  (P : environ -> mpred),
       ENTAIL Delta, allp_fun_id Delta && P |--  P.
Proof.
  intros. solve_andp.
Qed.


Lemma semax_aux_noreturn_inv:
forall (CS : compspecs) (Espec : OracleKind) (Delta : tycontext)
(Pre : environ -> mpred) (s : Clight.statement) 
  (Post Post' : ret_assert),
noreturn s = true ->
RA_normal Post = RA_normal Post' ->
RA_break Post = RA_break Post' ->
RA_continue Post = RA_continue Post' ->
semax_aux Delta Pre s Post -> semax_aux Delta Pre s Post'.
Proof.
  intros.
  revert Post' H0 H1 H2.
  induction H3; intros.
  + change (noreturn c && noreturn d = true)%bool in H.
    rewrite andb_true_iff in H.
    specialize (IHsemax_aux1 (proj1 H) _ H0 H1 H2).
    specialize (IHsemax_aux2 (proj2 H) _ H0 H1 H2).
    eapply semax_aux_ifthenelse;auto.
  + change (noreturn h && noreturn t = true)%bool in H.
    rewrite andb_true_iff in H.
    specialize (IHsemax_aux1 (proj1 H)).
    specialize (IHsemax_aux2 (proj2 H) _ H0 H1 H2).
    eapply semax_aux_seq; [| eauto].
    apply IHsemax_aux1; destruct Post', R; auto.
  + rewrite H1.
    apply semax_aux_break.
  + rewrite H2.
    apply semax_aux_continue.
  + simpl in H. change (noreturn body && noreturn incr = true)%bool in H.
    rewrite andb_true_iff in H.
    specialize (IHsemax_aux1 (proj1 H) (loop1_ret_assert Q' Post')).
    specialize (IHsemax_aux2 (proj2 H)  (loop2_ret_assert Q Post')).
    eapply semax_aux_loop with (Q'0:=Q').
    - destruct Post', R.
      unfold loop1_ret_assert in H3_.
      simpl in *. subst. apply IHsemax_aux1;auto.
    - destruct Post', R.
      simpl in *. subst. apply IHsemax_aux2;auto.
  + simpl in H. inv H.
  + eapply semax_aux_post with (normal_ret_assert P);
      [intros; apply andp_left2; try apply FF_left; rewrite H0; auto .. |].
    apply semax_aux_skip.
  + eapply semax_aux_post with (normal_ret_assert P);
      [intros; apply andp_left2; try apply FF_left; rewrite H0; auto .. |].
    apply semax_aux_assign.
  + eapply semax_aux_post with (normal_ret_assert P);
      [intros; apply andp_left2; try apply FF_left; rewrite H0; auto .. |].
    apply semax_aux_set_ptr_compare_load_cast_load_backward.
  + apply (semax_aux_conseq _ P' (Build_ret_assert (RA_normal R') (RA_break R') (RA_continue R') (RA_return Post'))).
    - exact H0.
    - rewrite <- H6; exact H1.
    - rewrite <- H7; exact H2.
    - rewrite <- H8; exact H3.
    - intros. solve_andp.
    - apply IHsemax_aux; auto.
  + constructor.
  + eapply semax_aux_conseq;[..|apply semax_aux_call].
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
Proof.
  intros.
  revert Post' H0 H1 H2.
  induction H3; intros.
  + change (nocontinue c && nocontinue d = true)%bool in H.
    rewrite andb_true_iff in H.
    specialize (IHsemax_aux1 (proj1 H) _ H0 H1 H2).
    specialize (IHsemax_aux2 (proj2 H) _ H0 H1 H2).
    eapply semax_aux_ifthenelse;auto.
  + change (nocontinue h && nocontinue t = true)%bool in H.
    rewrite andb_true_iff in H.
    specialize (IHsemax_aux1 (proj1 H)).
    specialize (IHsemax_aux2 (proj2 H) _ H0 H1 H2).
    eapply semax_aux_seq; [| eauto].
    apply IHsemax_aux1; destruct Post', R; auto.
  + rewrite H1.
    apply semax_aux_break.
  + inv H.
  + simpl in H. change (nocontinue body && nocontinue incr = true)%bool in H.
    rewrite andb_true_iff in H.
    specialize (IHsemax_aux1 (proj1 H) (loop1_ret_assert Q' Post')).
    specialize (IHsemax_aux2 (proj2 H)  (loop2_ret_assert Q Post')).
    eapply semax_aux_loop with (Q'0:=Q').
    - destruct Post', R.
      unfold loop1_ret_assert in H3_.
      simpl in *. subst. apply IHsemax_aux1;auto.
    - destruct Post', R.
      simpl in *. subst. apply IHsemax_aux2;auto.
  + rewrite H2. apply semax_aux_return.
  + eapply semax_aux_post with (normal_ret_assert P);
      [intros; apply andp_left2; try apply FF_left; rewrite H0; auto .. |].
    apply semax_aux_skip.
  + eapply semax_aux_post with (normal_ret_assert P);
      [intros; apply andp_left2; try apply FF_left; rewrite H0; auto .. |].
    apply semax_aux_assign.
  + eapply semax_aux_post with (normal_ret_assert P);
      [intros; apply andp_left2; try apply FF_left; rewrite H0; auto .. |].
    apply semax_aux_set_ptr_compare_load_cast_load_backward.
  + apply (semax_aux_conseq _ P' (Build_ret_assert (RA_normal R') (RA_break R') (RA_continue Post') (RA_return R'))).
    - exact H0.
    - rewrite <- H6; exact H1.
    - rewrite <- H7; exact H2.
    - solve_andp. 
    - intros. rewrite <- H8; apply H4.
    - apply IHsemax_aux; auto.
  + constructor.
  + eapply semax_aux_conseq;[..|apply semax_aux_call].
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


Lemma semax_aux_nobreak_inv:
forall (CS : compspecs) (Espec : OracleKind) (Delta : tycontext)
(Pre : environ -> mpred) (s : Clight.statement) 
  (Post Post' : ret_assert),
nobreak s = true ->
RA_normal Post = RA_normal Post' ->
RA_return Post = RA_return Post' ->
RA_continue Post = RA_continue Post' ->
semax_aux Delta Pre s Post -> semax_aux Delta Pre s Post'.
Proof.
  intros.
  revert Post' H0 H1 H2.
  induction H3; intros.
  + change (nobreak c && nobreak d = true)%bool in H.
    rewrite andb_true_iff in H.
    specialize (IHsemax_aux1 (proj1 H) _ H0 H1 H2).
    specialize (IHsemax_aux2 (proj2 H) _ H0 H1 H2).
    eapply semax_aux_ifthenelse;auto.
  + change (nobreak h && nobreak t = true)%bool in H.
    rewrite andb_true_iff in H.
    specialize (IHsemax_aux1 (proj1 H)).
    specialize (IHsemax_aux2 (proj2 H) _ H0 H1 H2).
    eapply semax_aux_seq; [| eauto].
    apply IHsemax_aux1; destruct Post', R; auto.
  + inv H.
  + rewrite H2. apply semax_aux_continue.
  + simpl in H. change (nobreak body && nobreak incr = true)%bool in H.
    rewrite andb_true_iff in H.
    specialize (IHsemax_aux1 (proj1 H) (loop1_ret_assert Q' Post')).
    specialize (IHsemax_aux2 (proj2 H)  (loop2_ret_assert Q Post')).
    eapply semax_aux_loop with (Q'0:=Q').
    - destruct Post', R.
      unfold loop1_ret_assert in H3_.
      simpl in *. subst. apply IHsemax_aux1;auto.
    - destruct Post', R.
      simpl in *. subst. apply IHsemax_aux2;auto.
  + rewrite H1. apply semax_aux_return.
  + eapply semax_aux_post with (normal_ret_assert P);
      [intros; apply andp_left2; try apply FF_left; rewrite H0; auto .. |].
    apply semax_aux_skip.
  + eapply semax_aux_post with (normal_ret_assert P);
      [intros; apply andp_left2; try apply FF_left; rewrite H0; auto .. |].
    apply semax_aux_assign.
  + eapply semax_aux_post with (normal_ret_assert P);
      [intros; apply andp_left2; try apply FF_left; rewrite H0; auto .. |].
    apply semax_aux_set_ptr_compare_load_cast_load_backward.
  + apply (semax_aux_conseq _ P' (Build_ret_assert (RA_normal R') (RA_break Post') (RA_continue R') (RA_return R'))).
    - exact H0.
    - rewrite <- H6; exact H1.
    - solve_andp. 
    - rewrite <- H8; exact H3.
    - intros. rewrite <- H7; apply H4.
    - apply IHsemax_aux; auto.
  + constructor.
  + eapply semax_aux_conseq;[..|apply semax_aux_call].
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
  assert (semax_aux Delta P' c {|
    RA_normal := RA_normal R';
    RA_break := RA_break R';
    RA_continue := FF;
    RA_return := RA_return R'
  |}).
  { eapply semax_aux_nocontinue_inv;[..|apply H5];auto. }
  econstructor;[..|apply H9];auto.
  - rewrite <- H6. auto.
  - rewrite <- H7. auto.
  - unfold RA_continue. apply andp_left2. 
    apply andp_left2. apply FF_left.
  - rewrite <- H8. auto.
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
  assert (semax_aux Delta P' c {|
    RA_normal := RA_normal R';
    RA_break := RA_break R';
    RA_continue := RA_continue R';
    RA_return :=(fun v => FF)
  |}).
  { eapply semax_aux_noreturn_inv;[..|apply H5];auto. }
  econstructor;[..|apply H9];auto.
  - rewrite <- H6. auto.
  - rewrite <- H7. auto.
  - rewrite <- H8. auto.
  - unfold RA_return. intros. apply andp_left2. 
    apply andp_left2. apply FF_left.
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
  assert (semax_aux Delta P' c {|
    RA_normal := RA_normal R';
    RA_break := FF;
    RA_continue := RA_continue R';
    RA_return := RA_return R'
  |}).
  { eapply semax_aux_nobreak_inv;[..|apply H5];auto. }
  econstructor;[..|apply H9];auto.
  - rewrite <- H6. auto.
  - unfold RA_break. apply andp_left2. 
    apply andp_left2. apply FF_left.
  - rewrite <- H8. auto.
  - rewrite <- H7. auto.
Qed.

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

Lemma oboxopt_ENTAIL: forall (Delta : tycontext) (ret : option ident) 
         (retsig : type) (P Q : environ -> mpred),
       tc_fn_return Delta ret retsig ->
       ENTAIL Delta,  P |-- Q ->
       ENTAIL Delta, oboxopt Delta ret P
       |-- oboxopt Delta ret Q.
Proof.
  intros.
  apply oboxopt_left2; auto.
  eapply tc_fn_return_temp_guard_opt; eauto.
Qed.

Lemma semax_aux_call_inv: forall {CS: compspecs} {Espec: OracleKind} 
  Delta ret a bl Pre Post,
  @semax_aux CS Espec Delta Pre (Clight.Scall ret a bl) Post ->
  local (tc_environ Delta) && (allp_fun_id Delta && Pre) |-- 
    (EX argsig: _, EX retsig: _, EX cc: _,
    EX A: _, EX P: _, EX Q: _, EX NEP: _, EX NEQ: _, EX ts: _, EX x: _,
    !! (Cop.classify_fun (typeof a) =
        Cop.fun_case_f (type_of_params argsig) retsig cc /\
        (retsig = Tvoid -> ret = None) /\
        tc_fn_return Delta ret retsig) &&
    ((*|>*)((tc_expr Delta a) && (tc_exprlist Delta (snd (split argsig)) bl)))  &&
    `(func_ptr (mk_funspec  (argsig,retsig) cc A P Q NEP NEQ)) (eval_expr a) &&
    |>((`(P ts x: environ -> mpred) (make_args' (argsig,retsig) (eval_exprlist (snd (split argsig)) bl))) * oboxopt Delta ret (maybe_retval (Q ts x) retsig ret -* RA_normal Post))).
Proof.
  intros. 
  remember (Clight.Scall ret a bl) as c1.
  induction H; try inversion Heqc1.
  - subst. 
    eapply derives_trans with (Q:=
      local (tc_environ Delta) && (allp_fun_id Delta && P')
    ).
    { rewrite (add_andp _ _ H). solve_andp. }
    eapply derives_trans.
    { apply andp_right.
      + rewrite <- andp_assoc. apply andp_left1.
        apply derives_refl.
      + apply IHsemax_aux;auto. }
    clear IHsemax_aux.
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
    apply exp_ENTAILL; intro ts.
    apply exp_ENTAILL; intro x.
    normalize.
    apply andp_right. { apply prop_right. auto. }
    apply andp_ENTAILL; [reduceLL;solve_andp|].
    apply later_ENTAILL.
    apply sepcon_ENTAILL; [reduceLL; solve_andp |].
    eapply oboxopt_ENTAILL; eauto.
    apply wand_ENTAILL; [reduceL; solve_andp |].
    auto.
  - solve_andp.
Qed.

Lemma func_ptr_unique: forall phi1 phi2 v,
  (predicates_hered.derives ((func_ptr phi1 v) && (func_ptr phi2 v)) (!! (phi1 = phi2)))%pred.
Admitted.

Lemma semax_aux_conj_call: forall CS Espec Delta ret a bl P Q Q1 Q2,
  @semax_aux CS Espec Delta P 
    (Clight.Scall ret a bl) (overridePost Q2 Q) ->
  @semax_aux CS Espec Delta P 
    (Clight.Scall ret a bl) (overridePost Q1 Q) ->
  @semax_aux CS Espec Delta P 
    (Clight.Scall ret a bl) (overridePost (Q1 && Q2) Q).
Proof.
  intros.
  apply semax_aux_call_inv in H.
  apply semax_aux_call_inv in H0.
  pose proof andp_ENTAILL _ _ _ _ _ H0 H.
  rewrite andp_dup in H1. clear H H0.
  eapply semax_aux_conseq;
  [..|apply semax_aux_call with (R:= Q1 && Q2)];
  try (intros; 
    try solve [repeat apply andp_left2;apply FF_left]).
  2:{ destruct Q;unfold_der. solve_andp. }
  eapply ENTAIL_trans;[apply H1|]. clear H1.
  Intros argsig1 retsig1 cc1 A1 P1 R1 NEP1 NEQ1 ts1 x1.
  Intros argsig2 retsig2 cc2 A2 P2 R2 NEP2 NEQ2 ts2 x2.
  rewrite H in H2. inv H2.
  assert_PROP (mk_funspec (argsig1, retsig2) cc2 A1 P1 R1 NEP1 NEQ1 = mk_funspec (argsig2, retsig2) cc2 A2 P2 R2 NEP2 NEQ2).
  { unfold liftx. simpl. intros r. unfold lift. simpl.
    eapply derives_trans;[|apply func_ptr_unique with (v:= eval_expr a r)]. solve_andp. }
  inv H2. apply inj_pair2 in H9. apply inj_pair2 in H10. subst.
  Exists argsig2 retsig2 cc2 A2 P2 R2 NEP1 NEQ1 ts1 x1.
  apply andp_right.
  { repeat apply andp_right;try solve_andp. apply prop_right. auto. }
  eapply derives_trans.
  { apply andp_right. rewrite <-!andp_assoc. apply andp_left1.
    { apply andp_right. repeat apply andp_left1. apply derives_refl.
      apply andp_left1. apply andp_left1. apply andp_left1. apply andp_left2. apply derives_refl. }
    { repeat apply andp_left2. apply derives_refl. }
  }
  rewrite andp_assoc. rewrite <- later_andp.
  apply later_ENTAIL. hnf. intros r. unfold liftx. simpl. unfold lift. simpl. destruct Q as [Qn Qc Qb Qr];unfold_der. simpl.
Admitted.

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
  assert_PROP (v1 <> Vundef).
  { destruct (eq_dec v1 Vundef).
    { subst. unfold local. unfold lift1. simpl. intros. Intros.
      apply tc_val_Vundef in H2. tauto. }
    apply prop_right. auto. }
  assert_PROP (v2 <> Vundef).
  { destruct (eq_dec v2 Vundef).
    { subst. unfold local. unfold lift1. simpl. intros. Intros.
      apply tc_val_Vundef in H4. tauto. }
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
  Intros. subst. solve_andp.
Qed.

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
    unfold local. unfold lift1. simpl. intros. Intros.
    apply tc_val_Vundef in H2. tauto. }
  destruct (eq_dec v2 Vundef).
  { subst. rewrite semax_straight.eval_cast_Vundef.
    unfold local. unfold lift1. simpl. intros. Intros.
    apply tc_val_Vundef in H3. tauto. }
  unfold liftx. simpl. unfold lift. intros r.
  pose proof mapsto_join_andp_det_logic 
    sh1 sh2 (typeof e2) (eval_lvalue e2 r) v1 v2 n n0 H H0.
  eapply derives_trans.
  { apply andp_right.
    + eapply derives_trans. 2:{ apply H1. } solve_andp.
    + apply derives_refl.
  }
  Intros. subst.
  solve_andp.
Qed.

Lemma eval_lvalue_expr_contra: forall {CS:compspecs} Delta e,
  access_mode (typeof e) <> By_reference ->
  tc_expr Delta e && tc_lvalue Delta e |-- FF.
Proof.
  intros. rename H into Ht. induction e;
  unfold tc_expr; unfold typecheck_expr; unfold tc_lvalue; unfold typecheck_lvalue;
  simpl; intros r; unfold liftx; simpl; unfold lift; try solve [Intros; inv H].
  + apply derives_extract_prop. intros. inv H.
  + destruct (access_mode t) eqn:E;simpl;
    unfold liftx; simpl; unfold lift; try solve [Intros; inv H].
    destruct (get_var_type Delta i ) eqn:E1;simpl.
    2:{ apply derives_extract_prop. intros. inv H. }
    rewrite denote_tc_assert_bool.
    simpl in Ht. contradiction.
  + destruct (access_mode t) eqn:E;simpl;
    unfold liftx; simpl; unfold lift; try solve [Intros; inv H].
    simpl in Ht. contradiction.
  + destruct (access_mode t) eqn:E;simpl;
    unfold liftx; simpl; unfold lift; try solve [Intros; inv H].
    simpl in Ht. contradiction.
Qed.

Lemma eval_cast_expr_contra: forall {CS:compspecs} Delta e1 t1,
  access_mode (typeof e1) <> By_reference ->
  tc_expr Delta (Ecast e1 t1) && tc_lvalue Delta e1 |-- FF .
Proof.
  intros. rename H into Ht. induction e1;
  unfold tc_expr; unfold typecheck_expr; unfold tc_lvalue; unfold typecheck_lvalue;
  simpl; intros r; unfold liftx; simpl; unfold lift; try solve [Intros; inv H].
  + apply derives_extract_prop. intros. inv H.
  + destruct (access_mode t) eqn:E;simpl;
    unfold liftx; simpl; unfold lift; try solve [Intros; inv H].
    destruct (get_var_type Delta i ) eqn:E1;simpl.
    2:{ apply derives_extract_prop. intros. inv H. }
    rewrite denote_tc_assert_bool.
    simpl in Ht. contradiction.
  + destruct (access_mode t) eqn:E;simpl;
    unfold liftx; simpl; unfold lift; try solve [Intros; inv H].
    simpl in Ht. contradiction.
  + destruct (access_mode t) eqn:E;simpl;
    unfold liftx; simpl; unfold lift; try solve [Intros; inv H].
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
  simpl; intros r; unfold liftx; simpl; unfold lift; try solve [Intros; inv H];
  try solve [apply derives_extract_prop; intros C; inv C].
Qed.

  
Lemma semax_aux_conj_set: forall CS Espec Delta P Q Q1 Q2 i e,
  @semax_aux CS Espec Delta P (Clight.Sset i e) 
    (overridePost Q2 Q) ->
  @semax_aux CS Espec Delta P (Clight.Sset i e) 
    (overridePost Q1 Q) ->
  @semax_aux CS Espec Delta P (Clight.Sset i e) 
    (normal_ret_assert (Q1 && Q2)).
Proof.
  intros.
  destruct Q as [Qn Qb Qc Qr]. unfold_der.
  apply semax_aux_set_inv in H0.
  apply semax_aux_set_inv in H. unfold_der.
  eapply semax_aux_conseq;
    [..|apply semax_aux_set_ptr_compare_load_cast_load_backward
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
      pose proof is_neutral_cast_by_value _ _ H2.
      apply type_is_by_value_sem in H4.
      rewrite <- later_andp. apply later_ENTAIL.
      eapply derives_trans with (Q:= tc_expr Delta e && tc_lvalue Delta e); try solve_andp.
      eapply derives_trans with (Q:= FF).
      2:{ apply FF_left. }
      apply eval_lvalue_expr_contra; auto.
    + Intros sh e1 t1 v2. 
      rewrite <- later_andp. apply later_ENTAIL.
      assert_PROP (access_mode (typeof e1) <> By_reference).
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
      rewrite H1 in H4. inv H4. Exists (Share.lub sh1 sh2) t2 v1.
      rewrite <- later_andp. apply andp_right.
      { apply prop_right. repeat split;auto.
      apply readable_share_lub. auto. }
      apply later_ENTAIL. rewrite subst_andp.
      eapply derives_trans.
      2:{ apply mapsto_conj_der_mem with (v4:=v2);auto. }
      solve_andp.
    + Intros sh1 t1 v1. Intros sh2 e2 t2 v2. Exists sh1 t1 v1.
      rewrite <- later_andp. apply andp_right.
      { apply prop_right. repeat split;auto. }
      apply later_ENTAIL.
      eapply derives_trans with (Q:= tc_lvalue Delta e && tc_lvalue Delta e2); try solve_andp.
      subst e. eapply derives_trans with (Q:=FF); try apply FF_left.
      apply eval_cast_lvalue_contra.
  - rewrite <- andp_assoc. rewrite !distrib_orp_andp2.
    repeat apply orp_left; rewrite andp_assoc.
    + Intros sh e2 t2 v2. Exists sh e2 t2 v2. 
      rewrite <- later_andp.
      apply andp_right. { apply prop_right;auto. }
      apply later_ENTAIL.
      assert_PROP (access_mode (typeof e2) <> By_reference).
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
      rewrite <- later_andp. apply andp_right.
      { apply prop_right. repeat split;auto. }
      apply later_ENTAIL.
      eapply derives_trans with (Q:= tc_lvalue Delta e && tc_lvalue Delta e1); try solve_andp.
      subst e. eapply derives_trans with (Q:=FF); try apply FF_left.
      apply eval_cast_lvalue_contra.
    + Intros sh1 e1 t1 v1. Intros sh2 e2 t2 v2.
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


Lemma semax_aux_loop_inv: forall {CS: compspecs} {Espec: OracleKind} Delta P R body incr,
  @semax_aux CS Espec Delta P (Clight.Sloop body incr) R ->
  local (tc_environ Delta) && (allp_fun_id Delta && P) |--
   EX Q: environ -> mpred, EX Q': environ -> mpred,
  !! (@semax_aux CS Espec Delta Q body (loop1_ret_assert Q' R) /\
      @semax_aux CS Espec Delta Q' incr (loop2_ret_assert Q R)) &&
  Q.
Proof.
  intros.
  remember (Clight.Sloop body incr) as c eqn:?H.
  induction H; try solve [inv H0].
  + inv H0; clear IHsemax_aux1 IHsemax_aux2.
    reduce2derives.
    apply (exp_right Q).
    apply (exp_right Q').
    apply andp_right; [apply prop_right; auto |].
    auto.
  + eapply derives_trans.
    2:{
      derives_rewrite -> (IHsemax_aux H0); clear IHsemax_aux.
      reduce2derives.
      apply exp_derives; intros Q.
      apply exp_derives; intros Q'.
      normalize.
      apply andp_right; [apply prop_right |]; auto.
      split.
      - destruct R as [nR bR cR rR], R' as [nR' bR' cR' rR']; simpl in H6, H7 |- *.
        simpl RA_normal in H1; simpl RA_break in H2; simpl RA_continue in H3; simpl RA_return in H4.
        eapply semax_aux_conseq; [.. | eassumption]; unfold loop1_ret_assert; unfold_der; try solve [intros;solve_andp];auto.
      - destruct R as [nR bR cR rR], R' as [nR' bR' cR' rR']; simpl in H6, H7 |- *.
        simpl RA_normal in H1; simpl RA_break in H2; simpl RA_continue in H3; simpl RA_return in H4.
        eapply semax_aux_conseq; [.. | eassumption]; unfold loop1_ret_assert;
        unfold_der; try solve [intros;solve_andp];auto.
    }
    { rewrite (add_andp _ _ H). solve_andp. }
Qed.


Lemma semax_aux_break_inv: forall {CS: compspecs} {Espec: OracleKind} Delta P R,
    @semax_aux CS Espec Delta P Clight.Sbreak R ->
    local (tc_environ Delta) && (allp_fun_id Delta && P) |-- RA_break R.
Proof.
  intros.
  remember Clight.Sbreak as c eqn:?H.
  induction H; try solve [inv H0].
  + solve_andp.
  + specialize (IHsemax_aux H0).
    rewrite (add_andp _ _ H).
    eapply derives_trans;[|apply H2].
    repeat apply andp_right;try solve_andp.
    eapply derives_trans;[|apply IHsemax_aux]. solve_andp.
Qed.

Lemma semax_aux_continue_inv: forall {CS: compspecs} {Espec: OracleKind} Delta P R,
    @semax_aux CS Espec Delta P Clight.Scontinue R ->
    local (tc_environ Delta) && (allp_fun_id Delta && P) |--  RA_continue R.
Proof.
  intros.
  remember Clight.Scontinue as c eqn:?H.
  induction H; try solve [inv H0].
  + solve_andp.
  + specialize (IHsemax_aux H0).
    rewrite (add_andp _ _ H).
    eapply derives_trans;[|apply H3].
    repeat apply andp_right;try solve_andp.
    eapply derives_trans;[|apply IHsemax_aux]. solve_andp.
Qed.


Lemma semax_aux_return_inv: forall {CS: compspecs} {Espec: OracleKind} Delta P ret R,
  @semax_aux CS Espec Delta P (Clight.Sreturn ret) R ->
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
    { apply andp_right;[|apply (IHsemax_aux H0)].
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

Lemma semax_aux_ifthenelse_inv: forall {CS: compspecs} {Espec: OracleKind} Delta P R b c1 c2,
  @semax_aux CS Espec Delta P (Clight.Sifthenelse b c1 c2) R ->
  local (tc_environ Delta) && (allp_fun_id Delta && P) |--
   (!! (bool_type (typeof b) = true) && tc_expr Delta (Eunop Cop.Onotbool b (Tint I32 Signed noattr)) &&
  EX P': environ -> mpred,
  !! (@semax_aux CS Espec Delta (P' && local (`(typed_true (typeof b)) (eval_expr b))) c1 R /\
      @semax_aux CS Espec Delta (P' && local (`(typed_false (typeof b)) (eval_expr b))) c2 R) &&
  P').
Proof.
  intros.
  remember (Clight.Sifthenelse b c1 c2) as c eqn:?H.
  induction H; try solve [inv H0].
  + inv H0; clear IHsemax_aux1 IHsemax_aux2.
    reduce2derives.
    apply andp_derives; auto.
    apply (exp_right P).
    apply andp_right; [apply prop_right; auto |].
    auto.
  + eapply derives_trans with (Q:= local (tc_environ Delta) && (allp_fun_id Delta && P')).
    { repeat apply andp_right;try solve_andp. derives_rewrite -> H. solve_andp. }
    derives_rewrite -> (IHsemax_aux H0). clear IHsemax_aux.
    reduce2derives.
    apply andp_derives; auto.
    apply exp_derives; intros P''.
    normalize.
    apply andp_right; auto.
    apply prop_right.
    split.
    - eapply semax_aux_conseq; try eassumption. solve_andp.
    - eapply semax_aux_conseq; try eassumption. solve_andp.
Qed.

Lemma semax_aux_post'': forall (R' : environ -> mpred) (Espec:OracleKind)
      (cs : compspecs) (Delta : tycontext) (R : ret_assert)
      (P : environ -> mpred) (c : Clight.statement),
    local (tc_environ Delta) && R' |-- RA_normal R ->
    semax_aux Delta P c (normal_ret_assert R') ->
    semax_aux Delta P c R.
Proof.
  intros. destruct R.
  eapply semax_aux_conseq;[..|apply H0];try solve_andp;
  unfold_der;try solve_andp.
  - eapply derives_trans;[|apply H]. solve_andp.
  - apply andp_left2;apply andp_left2;apply FF_left.
  - apply andp_left2;apply andp_left2;apply FF_left.
  - intros. apply andp_left2;apply andp_left2;apply FF_left.
Qed.

Lemma semax_aux_pre : forall (P' : environ -> mpred) (Espec : OracleKind) 
         (cs : compspecs) (Delta : tycontext) (P : environ -> mpred)
         (c : Clight.statement) (R : ret_assert),
  ENTAIL Delta, P |-- P' ->
  semax_aux Delta P' c R -> semax_aux Delta P c R.
Proof.
  intros. eapply semax_aux_conseq;[..|apply H0]; try solve [intros;solve_andp].
  eapply derives_trans;[|apply H]. solve_andp.
Qed.

Lemma semax_aux_pre' : forall (P' : environ -> mpred) (Espec : OracleKind) 
         (cs : compspecs) (Delta : tycontext) (P : environ -> mpred)
         (c : Clight.statement) (R : ret_assert),
  ENTAIL Delta, allp_fun_id Delta && P |-- P' ->
  semax_aux Delta P' c R -> semax_aux Delta P c R.
Proof.
  intros. eapply semax_aux_conseq;[..|apply H0]; try solve [intros;solve_andp].
  eapply derives_trans;[|apply H]. solve_andp.
Qed.




Lemma semax_aux_builtin_inv: forall {CS: compspecs} {Espec: OracleKind} 
  Delta opt ext tl el Pre Post,
  @semax_aux CS Espec Delta Pre (Clight.Sbuiltin opt ext tl el) Post ->
  local (tc_environ Delta) && (allp_fun_id Delta && Pre) |-- FF.
Proof.
  intros. 
  remember (Clight.Sbuiltin opt ext tl el) as c1.
  induction H; try inversion Heqc1.
  - subst. specialize (IHsemax_aux eq_refl).
    eapply derives_trans.
    2:{ apply IHsemax_aux. }
    rewrite (add_andp _ _ H). solve_andp.
  - solve_andp.
Qed.

Lemma semax_aux_goto_inv: forall {CS: compspecs} {Espec: OracleKind} 
  Delta l Pre Post,
  @semax_aux CS Espec Delta Pre (Clight.Sgoto l) Post ->
  local (tc_environ Delta) && (allp_fun_id Delta && Pre) |-- FF.
Proof.
  intros. 
  remember (Clight.Sgoto l) as c1.
  induction H; try inversion Heqc1.
  - subst. specialize (IHsemax_aux eq_refl).
    eapply derives_trans.
    2:{ apply IHsemax_aux. }
    rewrite (add_andp _ _ H). solve_andp.
  - solve_andp.
Qed.

Lemma semax_aux_switch_inv: forall {CS: compspecs} {Espec: OracleKind} 
  Delta a sl Pre Post,
  @semax_aux CS Espec Delta Pre (Clight.Sswitch a sl) Post ->
  local (tc_environ Delta) && (allp_fun_id Delta && Pre) |-- FF.
Proof.
  intros. 
  remember (Clight.Sswitch a sl) as c1.
  induction H; try inversion Heqc1.
  - subst. specialize (IHsemax_aux eq_refl).
    eapply derives_trans.
    2:{ apply IHsemax_aux. }
    rewrite (add_andp _ _ H). solve_andp.
  - solve_andp.
Qed.

Lemma semax_aux_post_simple: forall (R' : ret_assert) (Espec : OracleKind) 
      (cs : compspecs) (Delta : tycontext) (R : ret_assert)
      (P : environ -> mpred) (c : Clight.statement),
    RA_normal R' |-- RA_normal R ->
    RA_break R' |-- RA_break R ->
    RA_continue R' |-- RA_continue R ->
    (forall vl : option val, RA_return R' vl |-- RA_return R vl) ->
    semax_aux Delta P c R' ->
    semax_aux Delta P c R.
Proof.
  intros.
  eapply semax_aux_conseq;[..|apply H3].
  - solve_andp.
  - rewrite (add_andp _ _ H);solve_andp.
  - rewrite (add_andp _ _ H0);solve_andp.
  - rewrite (add_andp _ _ H1);solve_andp.
  - intros. rewrite (add_andp _ _ (H2 vl));solve_andp.
Qed.


Lemma semax_aux_label_inv: forall {CS: compspecs} {Espec: OracleKind} Delta P R l c,
  @semax_aux CS Espec Delta P (Clight.Slabel l c) R -> @semax_aux CS Espec Delta P c R.
Proof.
  intros.
  remember (Clight.Slabel l c) as c0 eqn:?H.
  induction H; try solve [inv H0].
  + specialize (IHsemax_aux H0).
    eapply semax_aux_conseq; eauto.
  + inv H0.
    apply H.
Qed.


Lemma aux_semax_extract_exists:
  forall {CS: compspecs} {Espec: OracleKind},
  forall (A : Type)  (P : A -> environ->mpred) c (Delta: tycontext) (R: ret_assert),
  (forall x, @semax_aux CS Espec Delta (P x) c R) ->
   @semax_aux CS Espec Delta (EX x:A, P x) c R.
Proof.
intros.
  revert A P R H; induction_stmt c; intros.
  + pose proof (fun x => semax_aux_skip_inv _ _ _ _ _ (H x)).
    eapply semax_aux_conseq with (R':=R).
    - rewrite !exp_andp2; apply exp_left.
      intro x. specialize (H0 x). eapply derives_trans;[|apply H0]. solve_andp.
    - solve_andp.
    - solve_andp.
    - solve_andp.
    - intros; solve_andp.
    - apply semax_aux_post'' with (R':=(RA_normal R)); 
      [.. | apply semax_aux_skip].
      solve_andp.
  + pose proof (fun x => semax_aux_assign_inv _ _ _ _ _ (H x)).
    clear H.
    apply exp_left in H0.
    rewrite <- !(exp_andp2 A) in H0.
    eapply semax_aux_conseq; [exact H0 | intros; solve_andp .. | clear H0 ].
    eapply semax_aux_conseq; [apply derives_aux_refl | .. | apply semax_aux_assign].
    - reduceL. apply derives_refl.
    - reduceL. apply FF_left.
    - reduceL. apply FF_left.
    - intros; reduceL. apply FF_left.
  + pose proof (fun x => semax_aux_set_inv _ _ _ _ _ (H x)).
    clear H.
    apply exp_left in H0.
    rewrite <- !(exp_andp2 A) in H0.
    eapply semax_aux_conseq; [exact H0 | intros; apply derives_aux_refl .. | clear H0 ].
    eapply semax_aux_conseq; [apply derives_aux_refl | .. | apply semax_aux_set_ptr_compare_load_cast_load_backward].
    - reduceL. apply derives_refl.
    - reduceL. apply FF_left.
    - reduceL. apply FF_left.
    - intros; reduceL. apply FF_left.
  + pose proof (fun x => semax_aux_call_inv _ _ _ _ _ _ (H x)).
    (* eapply semax_aux_conseq; [| intros; apply derives_aux_refl .. | apply semax_aux_call].
    rewrite !exp_andp2.
    apply exp_left; intros x; specialize (H0 x).
    auto. *)
    admit.
  + pose proof (fun x => semax_aux_builtin_inv _ _ _ _ _ _ _ (H x)).
    eapply semax_aux_conseq; [| intros; apply derives_aux_refl .. | apply semax_aux_builtin].
    rewrite !exp_andp2.
    apply exp_left; intros x; specialize (H0 x).
    auto.
  + apply semax_aux_seq with (EX Q: environ -> mpred, !! (semax_aux Delta Q c2 R) && Q).
    - apply IHc1.
      intro x. apply semax_aux_seq_inv';auto.
    - apply IHc2.
      intros Q. 
      apply semax_aux_pre with (EX H0: semax_aux Delta Q c2 R, Q).
      * apply andp_left2.
        apply derives_extract_prop; intros.
        apply (exp_right H0).
        auto.
      * apply IHc2.
        intro H0.
        auto.
  + eapply semax_aux_conseq; [| intros; apply derives_aux_refl .. | apply (semax_aux_ifthenelse _ (EX P': environ -> mpred, !! (semax_aux Delta (P' && local (`(typed_true (typeof e)) (eval_expr e))) c1 R /\ semax_aux Delta (P' && local (`(typed_false (typeof e)) (eval_expr e))) c2 R) && P'))].
    - pose proof (fun x => semax_aux_ifthenelse_inv _ _ _ _ _ _ (H x)).
      clear H.
      apply exp_left in H0.
      rewrite <- !(exp_andp2 A) in H0.
      exact H0.
    - rewrite exp_andp1.
      apply IHc1.
      intro P'.
      apply semax_aux_pre with (EX H0: semax_aux Delta (P' && local ((` (typed_true (typeof e))) (eval_expr e))) c1 R, P' && local ((` (typed_true (typeof e))) (eval_expr e))).
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
      apply semax_aux_pre with (EX H0: semax_aux Delta (P' && local ((` (typed_false (typeof e))) (eval_expr e))) c2 R, P' && local ((` (typed_false (typeof e))) (eval_expr e))).
      * apply andp_left2.
        rewrite !andp_assoc.
        apply derives_extract_prop; intros.
        apply (exp_right (proj2 H0)).
        solve_andp.
      * apply IHc2.
        intro H0.
        auto.
  + pose proof (fun x => semax_aux_loop_inv _ _ _ _ _ (H x)).
    eapply (semax_aux_conseq _ 
      (EX Q : environ -> mpred, EX Q' : environ -> mpred,
          EX H: semax_aux Delta Q c1 (loop1_ret_assert Q' R),
            EX H0: semax_aux Delta Q' c2 (loop2_ret_assert Q R), Q));
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
    apply (semax_aux_loop _ _
      (EX Q : environ -> mpred, EX Q' : environ -> mpred,
          EX H: semax_aux Delta Q c1 (loop1_ret_assert Q' R),
            EX H0: semax_aux Delta Q' c2 (loop2_ret_assert Q R), Q')).
    - apply IHc1.
      intros Q.
      apply IHc1.
      intros Q'.
      apply IHc1.
      intros ?H.
      apply IHc1.
      intros ?H.
      eapply semax_aux_post_simple; [.. | exact H1].
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
      eapply semax_aux_post_simple; [.. | exact H2].
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
  + pose proof (fun x => semax_aux_break_inv _ _ _ (H x)).
    eapply semax_aux_conseq; [| intros; apply derives_aux_refl .. |].
    - rewrite !exp_andp2; apply exp_left.
      intro x; apply H0.
    - apply semax_aux_break.
  + pose proof (fun x => semax_aux_continue_inv _ _ _ (H x)).
    eapply semax_aux_conseq; [| intros; apply derives_aux_refl .. |].
    - rewrite !exp_andp2; apply exp_left.
      intro x; apply H0.
    - apply semax_aux_continue.
  + pose proof (fun x => semax_aux_return_inv _ _ _ _ (H x)).
    eapply (semax_aux_conseq _ _ {| RA_normal := _; RA_break := _; RA_continue := _; RA_return := RA_return R |}); [.. | apply semax_aux_return].
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
  + pose proof (fun x => semax_aux_switch_inv _ _ _ _ _ (H x)).
    eapply semax_aux_conseq; [| intros; apply derives_aux_refl .. | apply semax_aux_switch].
    rewrite !exp_andp2.
    apply exp_left; intros x; specialize (H0 x).
    auto.
  + pose proof (fun x => semax_aux_label_inv _ _ _ _ _ (H x)).
    apply semax_aux_label.
    apply IHc.
    auto.
  + pose proof (fun x => semax_aux_goto_inv _ _ _ _ (H x)).
    eapply semax_aux_conseq; [| intros; apply derives_aux_refl .. | apply semax_aux_goto].
    rewrite !exp_andp2.
    apply exp_left; intros x; specialize (H0 x).
    auto.
(* Qed. *)
Admitted.

Lemma aux_semax_extract_prop: forall (CS : compspecs) (Espec : OracleKind) 
      (Delta : tycontext) (PP : Prop) (P : environ -> mpred)
      (c : Clight.statement) (Q : ret_assert),
    (PP -> semax_aux Delta P c Q) ->
    semax_aux Delta (!! PP && P) c Q.
Proof.
  intros.
  eapply semax_aux_conseq with (P':=EX H: PP, P) (R':=Q); try solve [intros; solve_andp].
  + apply andp_left2. Intros. Exists H0. solve_andp.
  + apply aux_semax_extract_exists, H.
Qed.

Definition ret_assert_andp Q1 Q2 : ret_assert := {|
  RA_normal := RA_normal Q1 && RA_normal Q2;
  RA_break  := RA_break Q1 && RA_break Q2;
  RA_continue := RA_continue Q1 && RA_continue Q2;
  RA_return := fun v => (RA_return Q1 v && RA_return Q2 v)
|}.

Lemma semax_aux_simple_inv:
forall (CS : compspecs) (Espec : OracleKind) (Delta : tycontext)
(Pre : environ -> mpred) (s : Clight.statement) 
  (Post Post' : ret_assert),
nocontinue s = true ->
noreturn s = true ->
nobreak s = true ->
RA_normal Post = RA_normal Post' ->
semax_aux Delta Pre s Post ->
semax_aux Delta Pre s Post'.
Proof.
  intros. destruct Post as [Qn Qb Qc Qr].
  destruct Post' as [Qn' Qb' Qc' Qr'].
  simpl in H2. subst.
  eapply semax_aux_nobreak_inv with (Post:={|
    RA_normal := Qn';
    RA_break := Qb;
    RA_continue := Qc';
    RA_return := Qr'
  |});auto.
  eapply semax_aux_nocontinue_inv with (Post:={|
    RA_normal := Qn';
    RA_break := Qb;
    RA_continue := Qc;
    RA_return := Qr'
  |});auto.
  eapply semax_aux_noreturn_inv with (Post:={|
    RA_normal := Qn';
    RA_break := Qb;
    RA_continue := Qc;
    RA_return := Qr
  |});auto.
Qed.



Lemma semax_aux_conj_assign_ret: forall CS Espec Delta P Q1 Q2 e e0,
  @semax_aux CS Espec Delta P (Clight.Sassign e e0) Q2 ->
  @semax_aux CS Espec Delta P (Clight.Sassign e e0) Q1 ->
  @semax_aux CS Espec Delta P (Clight.Sassign e e0) (ret_assert_andp Q1 Q2).
Proof.
  intros.
  destruct Q1 as [Q1n Q1b Q1c Q1r].
  destruct Q2 as [Q2n Q2b Q2c Q2r].
  unfold ret_assert_andp. unfold_der.
  apply semax_aux_simple_inv with (Post':=
    normal_ret_assert Q1n
  ) in H0;auto.
  apply semax_aux_simple_inv with (Post':=
  normal_ret_assert Q2n) in H;auto.
  apply semax_aux_simple_inv with (Post:=
  normal_ret_assert (Q1n&&Q2n));auto.
  eapply semax_aux_conj_assign with (Q:= {|
  RA_normal := FF;
  RA_break := FF;
  RA_continue := FF;
  RA_return := (fun v => FF)
  |});auto.
Qed.

Lemma semax_aux_conj_set_ret: forall CS Espec Delta P Q1 Q2 e e0,
  @semax_aux CS Espec Delta P (Clight.Sset e e0) Q2 ->
  @semax_aux CS Espec Delta P (Clight.Sset e e0) Q1 ->
  @semax_aux CS Espec Delta P (Clight.Sset e e0) (ret_assert_andp Q1 Q2).
Proof.
  intros.
  destruct Q1 as [Q1n Q1b Q1c Q1r].
  destruct Q2 as [Q2n Q2b Q2c Q2r].
  unfold ret_assert_andp. unfold_der.
  apply semax_aux_simple_inv with (Post':=
    normal_ret_assert Q1n
  ) in H0;auto.
  apply semax_aux_simple_inv with (Post':=
  normal_ret_assert Q2n) in H;auto.
  apply semax_aux_simple_inv with (Post:=
  normal_ret_assert (Q1n&&Q2n));auto.
  eapply semax_aux_conj_set with (Q:= {|
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

Lemma semax_aux_conj_break: forall CS Espec Delta P Q2 Q1,
  @semax_aux CS Espec Delta P (Clight.Sbreak) Q2 ->
  @semax_aux CS Espec Delta P (Clight.Sbreak) Q1 ->
  @semax_aux CS Espec Delta P (Clight.Sbreak) (ret_assert_andp Q1 Q2).
Proof.
  intros.
  apply semax_aux_break_inv in H0.
  apply semax_aux_break_inv in H.
  destruct Q1 as [Q1n Q1b Q1c Q1r], Q2 as [Q2n Q2b Q2c Q2r];unfold ret_assert_andp; unfold_der.
  eapply semax_aux_conseq with (R':={|
    RA_normal := FF;
    RA_break := Q1b && Q2b;
    RA_continue := FF;
    RA_return := (fun v => FF)
  |});[..|apply semax_aux_break];unfold_der;
  try solve [intros;apply andp_left2;apply andp_left2;apply FF_left];try solve_andp.
  apply andp_right;auto.
Qed.

Lemma semax_aux_conj_continue: forall CS Espec Delta P Q2 Q1,
  @semax_aux CS Espec Delta P (Clight.Scontinue) Q2 ->
  @semax_aux CS Espec Delta P (Clight.Scontinue) Q1 ->
  @semax_aux CS Espec Delta P (Clight.Scontinue) (ret_assert_andp Q1 Q2).
Proof.
  intros.
  apply semax_aux_continue_inv in H0.
  apply semax_aux_continue_inv in H.
  destruct Q1 as [Q1n Q1b Q1c Q1r], Q2 as [Q2n Q2b Q2c Q2r];unfold ret_assert_andp; unfold_der.
  eapply semax_aux_conseq with (R':={|
    RA_normal := FF;
    RA_break := FF;
    RA_continue := Q1c && Q2c;
    RA_return := (fun v => FF)
  |});[..|apply semax_aux_continue];unfold_der;
  try solve [intros;apply andp_left2;apply andp_left2;apply FF_left];try solve_andp.
  apply andp_right;auto.
Qed.


Lemma semax_aux_conj_return: forall CS Espec Delta P Q2 Q1 vl,
  @semax_aux CS Espec Delta P (Clight.Sreturn vl) Q2 ->
  @semax_aux CS Espec Delta P (Clight.Sreturn vl) Q1 ->
  @semax_aux CS Espec Delta P (Clight.Sreturn vl) (ret_assert_andp Q1 Q2).
Proof.
  intros.
  apply semax_aux_return_inv in H0.
  apply semax_aux_return_inv in H.
  eapply semax_aux_conseq with (R':= ret_assert_andp Q1 Q2);[..|apply semax_aux_return];unfold_der;try (intros;solve_andp).
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


Theorem semax_aux_conj_rule: forall  CS Espec Delta P c Q1 Q2 ,
  @semax_aux CS Espec Delta P c Q1 ->
  @semax_aux CS Espec Delta P c Q2 ->
  @semax_aux CS Espec Delta P c (ret_assert_andp Q1 Q2).
Proof.
  intros. revert dependent Q1.
  revert dependent Q2. revert dependent P .
  induction c.
  - intros. apply semax_aux_skip_inv in H0.
    apply semax_aux_skip_inv in H.
    eapply semax_aux_conseq with (P':= RA_normal Q1 && RA_normal Q2);[..|apply semax_aux_skip];try solve [intros;solve_andp].
    + apply andp_right.
      * eapply derives_trans;[|apply H]. solve_andp.
      * eapply derives_trans;[|apply H0]. solve_andp.
    + unfold normal_ret_assert. unfold RA_break. apply andp_left2. apply andp_left2. apply FF_left.
    + unfold normal_ret_assert. unfold RA_break. apply andp_left2. apply andp_left2. apply FF_left.
    + intros. unfold normal_ret_assert. unfold RA_break. apply andp_left2. apply andp_left2. apply FF_left.
  - intros.
    eapply semax_aux_conseq;
    [..|eapply semax_aux_conj_assign_ret with (Q1:=Q1) (Q2:=Q2);eassumption]; try solve_andp.
    intros. solve_andp.
  - intros.
    eapply semax_aux_conseq;
    [..|eapply semax_aux_conj_set_ret with (Q1:=Q1) (Q2:=Q2);eassumption]; try solve_andp.
    intros. solve_andp.
  - intros. apply semax_aux_call_inv in H0.
    (* eapply semax_aux_pre';[apply H0|].
    rewrite <- (FF_andp P).
      unfold FF. apply aux_semax_extract_prop. intros. destruct H1. *)
      admit.
  - intros. apply semax_aux_builtin_inv in H0.
    eapply semax_aux_pre';[apply H0|].
    rewrite <- (FF_andp P).
      unfold FF. apply aux_semax_extract_prop. intros. destruct H1.
  - intros. apply semax_aux_seq_inv in H0.
    apply semax_aux_seq_inv in H.
    destruct H0 as [R1 [E1 E2]].
    destruct H as [R2 [E3 E4]].
    pose proof IHc1 _ _ E3 _ E1.
    assert (semax_aux Delta (R1 && R2) c2 Q2).
    { eapply semax_aux_conseq;[..|apply E2]; try solve [intros; solve_andp]. }
    assert (semax_aux Delta (R1 && R2) c2 Q1).
    { eapply semax_aux_conseq;[..|apply E4]; try solve [intros; solve_andp]. }
    pose proof IHc2 _ _ H0 _ H1.
    econstructor.
    { rewrite ret_assert_override_distr in H.
      rewrite ret_assert_symm. apply H. }
    { auto. }
  - intros.
    apply semax_aux_ifthenelse_inv in H0.
    apply semax_aux_ifthenelse_inv in H.
    pose proof andp_ENTAILL _ _ _ _ _ H0 H.
    rewrite andp_dup in H1.
    eapply semax_aux_conseq with (R':=ret_assert_andp Q1 Q2);[apply H1|..]; try solve [intros;solve_andp].
    rewrite !andp_assoc.
    apply aux_semax_extract_prop. intros.
    rewrite <- andp_assoc.
    rewrite andp_comm. rewrite !andp_assoc.
    apply aux_semax_extract_prop. intros.
    rewrite !exp_andp1. rewrite exp_andp2. apply aux_semax_extract_exists. intros R1.
    rewrite !exp_andp2. apply aux_semax_extract_exists. intros R2.
    rewrite andp_comm. rewrite !andp_assoc. apply aux_semax_extract_prop. intros [E1 E2].
    rewrite andp_comm. rewrite andp_assoc.  rewrite andp_comm. rewrite !andp_assoc.
    apply aux_semax_extract_prop. intros [E3 E4].
    eapply semax_aux_pre with
    (P':= (!! (bool_type (typeof e) = true) && tc_expr Delta (Eunop Onotbool e (Tint I32 Signed noattr)) && (R1 && R2))).
    { repeat apply andp_right; try solve_andp. apply prop_right. auto. }
    apply semax_aux_ifthenelse.
    { eapply semax_aux_pre.
      2:{ apply IHc1 with (P:= (R1 && R2 && local ((` (typed_true (typeof e))) (eval_expr e)))).
          - eapply semax_aux_pre;[|apply E3]. solve_andp.
          - eapply semax_aux_pre;[|apply E1]. solve_andp.
      } solve_andp.
    }
    { eapply semax_aux_pre.
      2:{ apply IHc2 with (P:= (R1 && R2 && local ((` (typed_false (typeof e))) (eval_expr e)))).
          - eapply semax_aux_pre;[|apply E4]. solve_andp.
          - eapply semax_aux_pre;[|apply E2]. solve_andp.
      } solve_andp.
    }
  - intros.
    apply semax_aux_loop_inv in H0.
    apply semax_aux_loop_inv in H.
    pose proof andp_ENTAILL _ _ _ _ _ H0 H.
    rewrite andp_dup in H1.
    eapply semax_aux_conseq with (R':=ret_assert_andp Q1 Q2);[apply H1|..]; try solve [intros;solve_andp].
    rewrite !exp_andp1. apply aux_semax_extract_exists. intros R1a.
    rewrite !exp_andp1. apply aux_semax_extract_exists. intros R1b.
    rewrite !andp_assoc. apply aux_semax_extract_prop. intros [E1 E2]. rewrite andp_comm.
    rewrite !exp_andp1. apply aux_semax_extract_exists. intros R2a.
    rewrite !exp_andp1. apply aux_semax_extract_exists. intros R2b.
    rewrite !andp_assoc. apply aux_semax_extract_prop. intros [E3 E4].
    clear H0 H H1.
  
    destruct Q1 as [Q1n Q1b Q1c Q1r], Q2 as [Q2n Q2b Q2c Q2r];unfold loop1_ret_assert, loop2_ret_assert in *; unfold_der.
    eapply semax_aux_pre with (P:= R1a && R2a) in E1; try solve_andp.
    eapply semax_aux_pre with (P:= R1b && R2b) in E2; try solve_andp.
    eapply semax_aux_pre with (P:= R1a && R2a) in E3; try solve_andp.
    eapply semax_aux_pre with (P:= R1b && R2b) in E4; try solve_andp.
    pose proof IHc1 _ _ E1 _ E3. pose proof IHc2 _ _ E2 _ E4. clear IHc1 IHc2.
    unfold ret_assert_andp in *. unfold_der.
    
    rewrite andp_comm. eapply semax_aux_loop with (Q':= R1b && R2b);
    unfold loop1_ret_assert, loop2_ret_assert in *; unfold_der.
    + rewrite (andp_comm R1b). auto.
    + rewrite (andp_comm R1a). rewrite FF_andp in H0. auto.
  - intros. apply semax_aux_conj_break;auto.
  - intros. apply semax_aux_conj_continue;auto.
  - intros. apply semax_aux_conj_return;auto.
  - intros. apply semax_aux_switch_inv in H0.
    eapply semax_aux_pre';[apply H0|].
    rewrite <- (FF_andp P).
    unfold FF. apply aux_semax_extract_prop. intros. destruct H1.
  - intros. apply semax_aux_label_inv in H0.
    apply semax_aux_label_inv in H.
    constructor. apply IHc;auto.
  - intros. apply semax_aux_goto_inv in H0.
    eapply semax_aux_pre';[apply H0|].
    rewrite <- (FF_andp P).
    unfold FF. apply aux_semax_extract_prop. intros. destruct H1.
(* Qed. *)
Admitted.

(* Theorem semax_conj_rule: forall  CS Espec Delta P c Q1 Q2 ,
  @semax CS Espec Delta P c Q1 ->
  @semax CS Espec Delta P c Q2 ->
  @semax CS Espec Delta P c (ret_assert_andp Q1 Q2).
Proof.
  intros.
  inv H. inv H0.
  assert (semax_aux Delta P c R').
  { eapply semax_aux_pre';[|apply H6]. auto. }
  assert (semax_aux Delta P c R'0).
  { eapply semax_aux_pre';[|apply H11]. auto. }
  pose proof semax_aux_conj_rule _ _ _ _ _ _ _ H0 H12.
  destruct R' as [R1n R1b R1c R1r], R'0 as [R2n R2b R2c R2r],
  Q1 as [Q1n Q1b Q1c Q1r], Q2 as [Q2n Q2b Q2c Q2r];
  unfold ret_assert_andp in *; unfold_der.
  eapply semax_conseq_intro;[..|apply H13];unfold_der.
  - solve_andp.
  - eapply derives_trans with 
      (Q:= (|==> |> FF || Q1n) && (|==> |> FF || Q2n)).
    { apply andp_right.
      - eapply derives_trans;[|apply H2]. solve_andp.
      - eapply derives_trans;[|apply H7]. solve_andp. }
    {  apply bupd_mono.


     }
  
  Search bupd andp.   *)


Theorem semax_aux_derives: forall CS Espec Delta P c Q,
  @semax_aux CS Espec Delta P c Q -> @SeparationLogicAsLogic.AuxDefs.semax CS Espec Delta P c Q.
Proof.
  intros.
  induction H.
  - constructor; auto.
  - econstructor; eauto.
  - constructor;auto.
  - constructor;auto.
  - econstructor;eauto.
  - constructor;auto.
  - constructor;auto.
  - constructor;auto.
  - eapply AuxDefs.semax_conseq;
    [..|apply AuxDefs.semax_set_ptr_compare_load_cast_load_backward with (P0:=P)].
    { apply aux1_reduceR. eapply derives_trans;[|apply bupd_intro].
      repeat apply orp_ENTAILL.
      + apply orp_right1. solve_andp.
      + solve_andp.
      + solve_andp. }
    { apply derives_full_refl. } 
    { apply derives_full_refl. }
    { apply derives_full_refl. }  
    { intros. apply derives_full_refl. }
  - eapply AuxDefs.semax_conseq;[..|apply IHsemax_aux];
    try solve [intros;apply aux1_reduceR; eapply derives_trans;[|apply bupd_intro];auto].
  - constructor.
  - admit.
   (* rewrite <- (FF_andp TT).
    unfold FF. apply semax_extract_prop. intros. destruct H. *)
  - constructor. auto.
  - constructor.
  - rewrite <- (FF_andp TT).
    unfold FF. apply semax_extract_prop. intros. destruct H.
Admitted.
(* Qed. *)

Theorem semax_derives: forall CS Espec Delta P c Q,
  @semax CS Espec Delta P c Q -> @SeparationLogicAsLogic.AuxDefs.semax CS Espec Delta P c Q.
Proof.
  intros.
  induction H. 
  apply semax_aux_derives in H4.
  eapply semax_conseq;[..|apply H4];auto;
  try solve [intros;apply aux1_reduceR; eapply derives_trans;[|apply bupd_intro];auto].
Qed.


Lemma semax_aux_seq_skip:
   forall CS Espec (Delta : tycontext) (P : environ -> mpred)
         (s : Clight.statement) (Q : ret_assert),
    @semax_aux CS Espec Delta P s Q <->
    @semax_aux CS Espec Delta P (Clight.Ssequence s Clight.Sskip) Q.
Proof.
  intros. destruct Q as [Qn Qb Qc Qr];unfold_der.
  split;intro.
  - eapply semax_aux_seq with (Q:=Qn).
    { simpl. auto. }
    { eapply semax_aux_simple_inv;[..|apply semax_aux_skip];auto. }
  - apply semax_aux_seq_inv in H.
    destruct H as [R [E1 E2]].
    apply semax_aux_skip_inv in E2.
    unfold_der. eapply semax_aux_conseq;[..|apply E1];
    try (intros; solve_andp).
    unfold_der. eapply derives_trans;[|apply E2].
    solve_andp.
Qed.


Lemma semax_aux_skip_seq:
  forall CS Espec (Delta : tycontext) (P : environ -> mpred)
      (s : Clight.statement) (Q : ret_assert),
    @semax_aux CS Espec Delta P s Q <->
    @semax_aux CS Espec Delta P (Clight.Ssequence Clight.Sskip s) Q.
Proof.
intros. destruct Q as [Qn Qb Qc Qr];unfold_der.
split;intro.
- eapply semax_aux_seq with (Q:=P).
  { eapply semax_aux_simple_inv;[..|apply semax_aux_skip];auto. }
  { simpl. auto. }
- apply semax_aux_seq_inv in H.
  destruct H as [R [E1 E2]].
  apply semax_aux_skip_inv in E1.
  unfold_der. eapply semax_aux_conseq;[..|apply E2];
  try (intros; solve_andp).
  unfold_der. eapply derives_trans;[|apply E1].
  solve_andp.
Qed.
      

(* Lemma aux_extract_exists_pre': forall {CS Espec} (A : Type) (P : A -> environ -> mpred) 
      (c : Clight.statement) (Delta : tycontext) 
      (R : ret_assert),
    (forall x : A, @semax CS Espec Delta (P x) c R) ->
    semax Delta (EX x : A, P x) c R.
Proof.
  intros.
  pose proof aux_semax_extract_exists.
Admitted.

Lemma aux_semax_extract_prop': forall (CS : compspecs) (Espec : OracleKind) 
      (Delta : tycontext) (PP : Prop) (P : environ -> mpred)
      (c : Clight.statement) (Q : ret_assert),
    (PP -> semax Delta P c Q) ->
    semax Delta (!! PP && P) c Q.
Admitted. *)
