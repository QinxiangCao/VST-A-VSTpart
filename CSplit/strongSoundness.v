


(* Lemma semax_derives_vst: forall CS  Espec Delta P c Q,
@SeparationLogicAsLogic.AuxDefs.semax CS Espec Delta P c Q ->
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
  - eapply CSHL_MinimumLogic.semax_switch;eauto.

  Search AuxDefs.semax.
  apply H. *)

  Theorem semax_derives: forall CS Espec Delta P c Q,
  @semax CS Espec Delta P c Q -> 
  (* @SeparationLogicAsLogic.AuxDefs.semax CS Espec Delta P c Q. *)
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
    intros [H1 [H2 H3]].
    eapply CSHL_MinimumLogic.semax_conseq;
    [..|eapply CSHL_MinimumLogic.semax_call
    with (P := x3) (Q:=x4) (NEP:=x5) (NEQ:=x6) (A:= x2)
    (ts:=x7) (x9:=x8) (argsig:=x) (retsig:=x0) (cc:=x1)
    (F:=oboxopt Delta ret (maybe_retval (x4 x7 x8) x0 ret -* R))
    ];auto.
    { rewrite <- !andp_assoc. apply aux1_reduceR.
      eapply derives_trans;[|apply bupd_intro].
      apply andp_derives. { solve_andp. }
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
