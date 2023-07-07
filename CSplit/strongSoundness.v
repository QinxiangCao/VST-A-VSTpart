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
Require VST.floyd.SeparationLogicAsLogicSoundness.
Require Import VST.floyd.SeparationLogicAsLogic.
Require Import VST.floyd.proofauto.
Require Import Csplit.semantics.
Require Import Csplit.soundness.
Require Import Csplit.strong.
Require Import Csplit.AClight.
Require Import Csplit.AClightFunc.
Import Ctypes LiftNotation.
Local Open Scope logic.

Lemma semax_call_derives_aux:
  forall (CS: compspecs) Delta a b id fs fs',
    (glob_specs Delta) ! id = Some fs ->
    allp_fun_id Delta &&
    local (fun rho =>
      gvar_injection (ge_of rho) /\
      eval_expr a rho = Vptr b Ptrofs.zero /\
      global_block rho id b) &&
    `(funspec_sub_si fs fs')
    |-- ` (func_ptr fs') (eval_expr a).
Proof.
  intros. intros rho.
  unfold local, lift1.
  unfold_lift. unfold andp. simpl.
  unfold allp_fun_id. seplog_tactics.normalize. rewrite H1.
  unfold func_ptr.
  apply derives_trans with (
    func_ptr_si fs (Vptr b Ptrofs.zero) && funspec_sub_si fs fs'
  ).
  2: { rewrite andp_comm. apply func_ptr_si_mono. }
  apply andp_derives. 2: apply derives_refl.
  apply (allp_left _ id).
  apply (allp_left _ fs).
  rewrite log_normalize.prop_imp; auto.
  Intros b'. destruct H2. rewrite H4 in H3. inv H3.
  apply derives_refl.
Qed.

Theorem semax_derives: forall CS Espec Delta P c Q,
  @semax CS Espec Delta P c Q -> 
  @CSHL_Def.semax CS Espec Delta P c Q.
Proof.
  intros.
  induction H.

  - rewrite andp_assoc.
    apply CSHL_PracticalLogic.semax_extract_prop. intros.
    apply CSHL_MinimumLogic.semax_ifthenelse;eauto.
  - eapply CSHL_MinimumLogic.semax_seq;eauto.
  - eapply CSHL_MinimumLogic.semax_break;eauto.
  - eapply CSHL_MinimumLogic.semax_continue;eauto.
  - eapply CSHL_MinimumLogic.semax_loop;eauto.
  - eapply CSHL_MinimumLogic.semax_return;eauto.
  - eapply CSHL_MinimumLogic.semax_skip;eauto.
  - apply CSHL_MinimumLogic.semax_extract_exists.
    intros sh.
    apply CSHL_PracticalLogic.semax_extract_prop.
    intros.
    eapply CSHL_MinimumLogic.semax_conseq;
    [..|apply CSHL_MinimumLogic.semax_store with 
    (P0:=(((` (mapsto sh (typeof e1))) (eval_lvalue e1)
    ((` force_val)
       ((` (sem_cast (typeof e2) (typeof e1))) (eval_expr e2))) -* P))) (sh0:=sh)];auto.
    { apply aux1_reduceR. eapply derives_trans;[|apply bupd_intro].
      solve_andp. }
    { apply aux1_reduceR. eapply derives_trans;[|apply bupd_intro].
      rewrite normal_ret_assert_elim. apply andp_left2.
      apply andp_left2. apply modus_ponens_wand. }
    { apply derives_full_refl. }
    { apply derives_full_refl. }  
    { intros. apply derives_full_refl. }
  - rewrite orp_is_exp.
    apply CSHL_MinimumLogic.semax_extract_exists.
    intros b1. destruct b1;[
      rewrite orp_is_exp;
      apply CSHL_MinimumLogic.semax_extract_exists;
      intros b2; destruct b2|].
    + apply semax_set.
    + repeat (apply CSHL_MinimumLogic.semax_extract_exists; intros).
      apply CSHL_PracticalLogic.semax_extract_prop.
      intros [H1 [H2 H3]].
      eapply CSHL_MinimumLogic.semax_conseq;
      [..|apply semax_load with (sh:=x) (t2:=x0) (v2:=x1)
      (P0:= ((` (mapsto x (typeof e))) (eval_lvalue e) (` x1) * TT)
        && subst id (` x1) P
      )
      ];auto.
      { rewrite !andp_assoc. apply derives_full_refl. }
      { rewrite normal_ret_assert_elim. apply aux1_reduceR.
        eapply derives_trans;[|apply bupd_intro].
        rewrite normal_ret_assert_elim.
        unfold local. unfold_lift. unfold lift1. simpl. intros.
        unfold subst. apply derives_extract_prop. intros rho.
        apply andp_left2. apply exp_left. intros x3.
        apply derives_extract_prop. intros. apply andp_left2.
        rewrite env_set_env_set. rewrite <- H.
        rewrite env_set_eval_id with (Delta:=Delta) (t:=x0);auto.
        unfold typeof_temp in H1.
        destruct (temp_types Delta) ! id; inv H1; auto. }
      { apply derives_full_refl. }
      { apply derives_full_refl. }
      { intros. apply derives_full_refl. }
      { solve_andp. }
    + repeat (apply CSHL_MinimumLogic.semax_extract_exists; intros).
      apply CSHL_PracticalLogic.semax_extract_prop.
      intros [H1 [H2 [H3 H4]]]. subst e.
      eapply CSHL_MinimumLogic.semax_conseq;
      [..|eapply semax_cast_load
       with (v2 := x2) (sh:= x)
      (P0:= ((` (mapsto x (typeof x0))) (eval_lvalue x0) (` x2) * TT) &&
      subst id (` (force_val (sem_cast (typeof x0) x1 x2))) P)
      ];auto.
      { rewrite !andp_assoc. apply derives_full_refl. }
      { rewrite normal_ret_assert_elim. apply aux1_reduceR.
        eapply derives_trans;[|apply bupd_intro].
        rewrite normal_ret_assert_elim.
        unfold local. unfold_lift. unfold lift1. simpl. intros.
        unfold subst. apply derives_extract_prop. intros rho.
        apply andp_left2. apply exp_left. intros x4.
        apply derives_extract_prop. intros. apply andp_left2.
        rewrite env_set_env_set. rewrite <- H.
        rewrite env_set_eval_id with (Delta:=Delta) (t:=x1);auto.
        unfold typeof_temp in H2.
        destruct (temp_types Delta) ! id; inv H2; auto. }
      { apply derives_full_refl. }
      { apply derives_full_refl. }
      { intros. apply derives_full_refl. }
      { solve_andp. }
  - eapply CSHL_MinimumLogic.semax_conseq;[..|apply IHsemax];
    try solve [intros;apply aux1_reduceR; eapply derives_trans;[|apply bupd_intro];auto].
  - apply semax_ff.
  - repeat (apply CSHL_MinimumLogic.semax_extract_exists; intros).
    apply extract_exists_pre_later;intros.
    apply extract_exists_pre_later;intros.
    rewrite !andp_assoc.
    apply CSHL_PracticalLogic.semax_extract_prop.
    intros [H1 [H2 [H3 [H4 H5]]]].
    eapply CSHL_MinimumLogic.semax_conseq;
      [..|eapply CSHL_MinimumLogic.semax_call];
      try eassumption.
    { rewrite <- !andp_assoc. apply aux1_reduceR.
      eapply derives_trans;[|apply bupd_intro].
      apply andp_derives.
      { apply derives_trans with (
          local (tc_environ Delta) && tc_expr Delta a &&
          tc_exprlist Delta (snd (split x)) bl &&
          (allp_fun_id Delta &&
          local (fun rho =>
            gvar_injection (ge_of rho) /\
            eval_expr a rho = Vptr x7 Ptrofs.zero /\
            global_block rho x8 x7) &&
          `(funspec_sub_si x9 (mk_funspec (x, x0) x1 x2 x3 x4 x5 x6)))).
        { solve_andp. }
        apply andp_derives. solve_andp.
        eapply semax_call_derives_aux; eassumption. }
      rewrite sepcon_comm. solve_andp.
    }
    { apply aux1_reduceR. eapply derives_trans;[|apply bupd_intro].
      rewrite !normal_ret_assert_elim.
      rewrite <- !andp_assoc.
      rewrite andp_comm. rewrite exp_andp1.
      apply exp_left. intros old.
      rewrite substopt_oboxopt.

      destruct ret.
      2:{ intros rho. unfold oboxopt.
          simpl. apply andp_left1.
          apply wand_frame_elim''. }
      intros rho. unfold oboxopt.
      unfold obox. hnf in H3.
      destruct (temp_types Delta) ! i eqn:E; inv H3.
      unfold local. unfold lift1. simpl.
      rewrite andp_comm. rewrite andp_assoc.
      apply derives_extract_prop. 
      intros. apply andp_left2. eapply derives_trans.
      { apply sepcon_derives.
        2: { apply derives_refl. }
        apply allp_instantiate' with (x:= eval_id i rho). }
      unfold subst. unfold liftx. unfold_lift.
      rewrite !env_set_eval_id with (Delta:=Delta) (t:=t);auto.
      rewrite log_normalize.prop_imp.
      2:{ apply tc_eval'_id_i with (Delta:=Delta);auto. }
      apply wand_frame_elim''. }
    { apply derives_full_refl. }
    { apply derives_full_refl. }  
    { intros. apply derives_full_refl. }
  - apply CSHL_MinimumLogic.semax_Slabel. auto.
  - apply semax_ff.
  - apply semax_ff.
Qed.


Fixpoint S_statement_to_Clight (s: S_statement) : Clight.statement :=
  match s with
  | Ssequence s1 s2 =>
      Clight.Ssequence 
        (S_statement_to_Clight s1) 
        (S_statement_to_Clight s2)
  | Sassert       => Clight.Sskip
  | Sskip         => Clight.Sskip
  | Sassign e1 e2 => Clight.Sassign e1 e2
  | Scall id e args
      => Clight.Scall id e args
  | Sset id e
      => Clight.Sset id e
  | Sifthenelse e s1 s2
      => Clight.Sifthenelse e 
          (S_statement_to_Clight s1) 
          (S_statement_to_Clight s2)
  | Sloop s1 s2
      => Clight.Sloop 
          (S_statement_to_Clight s1) 
          (S_statement_to_Clight s2)
  | Sbreak => Clight.Sbreak 
  | Scontinue => Clight.Scontinue
  | Sreturn e => Clight.Sreturn e
  end.

Fixpoint remove_skip (c: statement): statement :=
  match c with
  | Clight.Ssequence c1 c2 =>
      match remove_skip c1 with
      | Clight.Sskip => remove_skip c2
      | _ => match remove_skip c2 with
             | Clight.Sskip => remove_skip c1
             | _ => Clight.Ssequence (remove_skip c1) (remove_skip c2)
             end
      end
  | Clight.Sifthenelse e c1 c2 =>
      Clight.Sifthenelse e (remove_skip c1) (remove_skip c2)
  | Clight.Sloop c1 c2 =>
      Clight.Sloop (remove_skip c1) (remove_skip c2)
  | _ =>
      c
  end.

Theorem semax_remove_skip: forall {Ora: OracleKind} {CS} Delta P c Q,
  @semax CS Ora Delta P c Q <-> @semax CS Ora Delta P (remove_skip c) Q.
Proof.
  intros.
  revert P Q.
  induction c; intros; try tauto.
  + simpl.
    assert (semax Delta P (Clight.Ssequence c1 c2) Q <->
            semax Delta P (Clight.Ssequence (remove_skip c1) (remove_skip c2)) Q).
    {
      split; intros HH; apply semax_seq_inv in HH; destruct HH as [R [? ?] ].
      + rewrite IHc1 in H; rewrite IHc2 in H0.
        eapply semax_seq; eauto.
      + rewrite <- IHc1 in H; rewrite <- IHc2 in H0.
        eapply semax_seq; eauto.
    }
    destruct (remove_skip c1), (remove_skip c2);
      solve
        [ auto
        | rewrite H; symmetry; apply semax_skip_seq
        | rewrite H; symmetry; apply semax_seq_skip].
  + simpl.
    split; intros HH; apply semax_ifthenelse_inv in HH.
    - eapply semax_pre'; eauto.
      rewrite andp_comm.
      rewrite exp_andp1.
      apply semax_extract_exists; intros P'.
      rewrite andp_assoc.
      apply semax_extract_prop; intros [? ?].
      rewrite andp_comm.
      apply semax_ifthenelse.
      * apply IHc1, H.
      * apply IHc2, H0.
    - eapply semax_pre'; eauto.
      rewrite andp_comm.
      rewrite exp_andp1.
      apply semax_extract_exists; intros P'.
      rewrite andp_assoc.
      apply semax_extract_prop; intros [? ?].
      rewrite andp_comm.
      apply semax_ifthenelse.
      * apply IHc1, H.
      * apply IHc2, H0.
  + simpl.
    split; intros HH; apply semax_loop_inv in HH.
    - eapply semax_pre'; eauto.
      apply semax_extract_exists; intros Q1.
      apply semax_extract_exists; intros Q2.
      apply semax_extract_prop; intros [? ?].
      eapply semax_loop.
      * apply IHc1, H.
      * apply IHc2, H0.
    - eapply semax_pre'; eauto.
      apply semax_extract_exists; intros Q1.
      apply semax_extract_exists; intros Q2.
      apply semax_extract_prop; intros [? ?].
      eapply semax_loop.
      * apply IHc1, H.
      * apply IHc2, H0.
Qed.

Lemma soundness: forall {Espec CS} Delta
(P:assert) (Q:ret_assert) (s_stm: S_statement)
(c_stm: C_statement s_stm) (c: statement),
remove_skip c = remove_skip (S_statement_to_Clight s_stm) ->
split_Semax Delta P Q (C_split s_stm c_stm) ->
@semax CS Espec Delta P c Q.
Proof.
  intros.
  apply semax_remove_skip.
  rewrite H.
  rewrite <- semax_remove_skip.
  eapply soundness; eauto.
Qed.

Lemma semax_skip_normal_split_post: forall {Ora CS} Delta P Q,
  P |-- Q ->
  @semax Ora CS Delta P Clight.Sskip (normal_split_assert Q).
Proof.
  intros.
  eapply semax_post_simple with (normal_ret_assert P); [apply H | apply TT_right .. | apply TT_right | intro; apply TT_right | ].
  apply semax_skip.
Qed.

Lemma semax_return_return_split_assert: forall {Ora CS} Delta P c Q F,
  @semax Ora CS Delta P c (frame_ret_assert Q F) ->
  @semax Ora CS Delta P c (return_split_assert (RA_return (frame_ret_assert Q F))).
Proof.
  intros.
  eapply semax_post_simple; [ .. | apply H].
  + apply TT_right.
  + apply TT_right.
  + apply TT_right.
  + intros; apply derives_refl.
Qed.
