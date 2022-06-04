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
(* Require VST.floyd.SeparationLogicAsLogicSoundness.
Require Import VST.floyd.SeparationLogicAsLogic.
Require Import VST.floyd.proofauto. *)
Import Ctypes LiftNotation.
Local Open Scope logic.
Require Import CSplit.strong.


Lemma modifiedvars_aux: forall id, (fun i => isSome (insert_idset id idset0) ! i) = eq id.
Proof.
  intros.
  extensionality i.
  apply prop_ext.
  unfold insert_idset.
  destruct (ident_eq i id).
  + subst.
    rewrite PTree.gss.
    simpl; tauto.
  + rewrite PTree.gso by auto.
    unfold idset0.
    rewrite PTree.gempty.
    simpl.
    split; [tauto | intro].
    congruence.
Qed.


Lemma sepcon_derives_full: forall Delta P1 P2 Q1 Q2,
  local (tc_environ Delta) && (allp_fun_id Delta && P1) |-- P2 ->
  local (tc_environ Delta) && (allp_fun_id Delta && Q1) |-- Q2 ->
  local (tc_environ Delta) && (allp_fun_id Delta && (P1 * Q1)) |-- (P2 * Q2).
Proof.
  intros.
  pose proof sepcon_ENTAILL  _ _ _ _ _ H H0.
  eapply derives_trans; [exact H1 |].
  clear.
  solve_andp.
  (* eapply derives_trans; [apply bupd_sepcon |].
  apply bupd_mono.
  rewrite distrib_orp_sepcon, !distrib_orp_sepcon2.
  repeat apply orp_left.
  + apply orp_right1.
    rewrite <- later_sepcon.
    rewrite FF_sepcon; auto.
  + apply orp_right1.
    rewrite sepcon_comm.
    apply wand_sepcon_adjoint.
    eapply derives_trans; [apply now_later |].
    apply wand_sepcon_adjoint.
    rewrite <- later_sepcon.
    rewrite sepcon_FF.
    auto.
  + apply orp_right1.
    apply wand_sepcon_adjoint.
    eapply derives_trans; [apply now_later |].
    apply wand_sepcon_adjoint.
    rewrite <- later_sepcon.
    rewrite sepcon_FF.
    auto.
  + apply orp_right2; auto. *)
Qed.


Lemma tc_fn_return_temp_guard_opt: forall ret retsig Delta,
  tc_fn_return Delta ret retsig ->
  temp_guard_opt Delta ret.
Proof.
  intros.
  destruct ret; hnf in H |- *; [destruct ((temp_types Delta) ! i) |]; auto; congruence.
Qed.

Lemma semax_frame:
  forall {CS: compspecs} {Espec: OracleKind},
  forall Delta P s R F,
   closed_wrt_modvars s F ->
  @semax CS Espec Delta P s R ->
    @semax CS Espec Delta (P * F) s (frame_ret_assert R F).
Proof.
  intros.
  induction H0.
  + apply semax_pre with (!! (bool_type (typeof b) = true) && tc_expr Delta (Eunop Cop.Onotbool b (Tint I32 Signed noattr)) && (P * F)).
    - normalize.
      apply andp_left2, andp_right.
      * eapply derives_trans; [apply sepcon_derives; [apply andp_left1 |]; apply derives_refl |].
        intro rho.
        apply (predicates_sl.extend_sepcon (extend_tc.extend_tc_expr Delta (Eunop Cop.Onotbool b (Tint I32 Signed noattr)) rho)).
      * eapply derives_trans; [apply sepcon_derives; [apply andp_left2 |]; apply derives_refl |].
        auto.
    - rewrite semax_lemmas.closed_Sifthenelse in H; destruct H.
      apply semax_ifthenelse.
      * eapply semax_pre; [| apply IHsemax1; auto].
        apply andp_left2.
        unfold_lift.
        intro rho; unfold local, lift1; simpl.
        normalize.
      * eapply semax_pre; [| apply IHsemax2; auto].
        apply andp_left2.
        unfold_lift.
        intro rho; unfold local, lift1; simpl.
        normalize.
  + rewrite semax_lemmas.closed_Ssequence in H; destruct H.
    apply semax_seq with (Q * F).
    - destruct R; apply IHsemax1; auto.
    - destruct R; apply IHsemax2; auto.
  + replace (RA_break Q * F) with (RA_break (frame_ret_assert Q F)) by (destruct Q; auto).
    apply semax_break.
  + replace (RA_continue Q * F) with (RA_continue (frame_ret_assert Q F)) by (destruct Q; auto).
    apply semax_continue.
  + rewrite semax_lemmas.closed_Sloop in H; destruct H.
    eapply semax_loop with (Q' * F).
    - destruct R; apply IHsemax1; auto.
    - replace (loop2_ret_assert (Q * F) (frame_ret_assert R F))
        with (frame_ret_assert (loop2_ret_assert Q R) F)
        by (destruct R; simpl; f_equal; extensionality rho; apply pred_ext; normalize).
      apply IHsemax2; auto.
  + eapply semax_pre; [| apply semax_return].
    apply andp_left2.
    apply andp_right.
    - intro rho; simpl.
      eapply derives_trans; [apply sepcon_derives; [| apply derives_refl]; apply andp_left1, derives_refl |].
      apply (predicates_sl.extend_sepcon (extend_tc.extend_tc_expropt Delta ret (ret_type Delta) rho)).
    - intro rho; simpl.
      eapply derives_trans; [apply sepcon_derives; [| apply derives_refl]; apply andp_left2, derives_refl |].
      destruct R; simpl.
      apply derives_refl.
  + rewrite frame_normal.
    apply semax_skip.
  + rewrite frame_normal.
    eapply semax_pre; [| apply semax_assign].
    apply andp_left2.
    rewrite exp_sepcon1; apply exp_derives; intros sh.
    normalize.
    eapply derives_trans; [apply sepcon_derives; [apply derives_refl |]; apply now_later |].
    rewrite <- later_sepcon.
    apply later_derives.
    apply andp_right.
    - eapply derives_trans; [apply sepcon_derives; [| apply derives_refl]; apply andp_left1, derives_refl |].
      intro rho; simpl.
      apply (predicates_sl.extend_sepcon (extend_tc.extend_andp _ _ (extend_tc.extend_tc_lvalue Delta e1 rho) (extend_tc.extend_tc_expr Delta (Ecast e2 (typeof e1)) rho))).
    - eapply derives_trans; [apply sepcon_derives; [| apply derives_refl]; apply andp_left2, derives_refl |].
      rewrite sepcon_assoc; apply sepcon_derives; auto.
      rewrite <- (sepcon_emp ((` (mapsto sh (typeof e1))) (eval_lvalue e1)
                   ((` (force_val oo sem_cast (typeof e2) (typeof e1))) (eval_expr e2)))) at 2.
      eapply derives_trans; [| apply wand_frame_hor].
      apply sepcon_derives; [apply derives_refl |].
      rewrite <- wand_sepcon_adjoint.
      rewrite sepcon_emp; auto.
  + rewrite frame_normal.
    eapply semax_pre; [| apply semax_set_ptr_compare_load_cast_load_backward].
    apply andp_left2.
    rewrite !distrib_orp_sepcon.
    repeat apply orp_derives.
    - eapply derives_trans; [apply sepcon_derives; [apply derives_refl |]; apply now_later |].
      rewrite <- later_sepcon.
      apply later_derives.
      apply andp_right.
      * intro rho; simpl.
        eapply derives_trans; [apply sepcon_derives; [| apply derives_refl]; apply andp_left1, derives_refl |].
        apply (predicates_sl.extend_sepcon (extend_tc.extend_andp _ _ (extend_tc.extend_tc_expr Delta e rho) (extend_tc.extend_tc_temp_id id (typeof e) Delta e rho))).
      * eapply derives_trans; [apply sepcon_derives; [| apply derives_refl]; apply andp_left2, derives_refl |].
        rewrite subst_sepcon.
        rewrite (closed_wrt_subst _ _ F); auto.
        unfold closed_wrt_modvars in H.
        rewrite <- modifiedvars_aux.
        auto.
    
    (* - rewrite exp_sepcon1; apply exp_derives; intros cmp.
      rewrite exp_sepcon1; apply exp_derives; intros e1.
      rewrite exp_sepcon1; apply exp_derives; intros e2.
      rewrite exp_sepcon1; apply exp_derives; intros ty.
      rewrite exp_sepcon1; apply exp_derives; intros sh1.
      rewrite exp_sepcon1; apply exp_derives; intros sh2.
      normalize.
      eapply derives_trans; [apply sepcon_derives; [apply derives_refl |]; apply now_later |].
      rewrite <- later_sepcon.
      apply later_derives.
      apply andp_right; [apply andp_right; [apply andp_right; [apply andp_right |] |] |].
      * eapply derives_trans; [apply sepcon_derives; [| apply derives_refl]; apply andp_left1, andp_left1, andp_left1, andp_left1, derives_refl |].
        intro rho; simpl.
        apply (predicates_sl.extend_sepcon (extend_tc.extend_andp _ _ (extend_tc.extend_tc_expr Delta e1 rho) (extend_tc.extend_tc_expr Delta e2 rho))).
      * unfold local, lift1; unfold_lift; intro rho; simpl.
        eapply derives_trans; [apply sepcon_derives; [| apply derives_refl]; apply andp_left1, andp_left1, andp_left1, andp_left2, derives_refl |].
        rewrite <- (andp_TT (prop _)) at 1.
        normalize.
      * eapply derives_trans; [apply sepcon_derives; [| apply derives_refl]; apply andp_left1, andp_left1, andp_left2, derives_refl |].
        rewrite sepcon_assoc.
        apply sepcon_derives; auto.
      * eapply derives_trans; [apply sepcon_derives; [| apply derives_refl]; apply andp_left1, andp_left2, derives_refl |].
        rewrite sepcon_assoc.
        apply sepcon_derives; auto.
      * eapply derives_trans; [apply sepcon_derives; [| apply derives_refl]; apply andp_left2, derives_refl |].
        rewrite subst_sepcon.
        rewrite (closed_wrt_subst _ _ F); auto.
        unfold closed_wrt_modvars in H.
        rewrite <- modifiedvars_aux.
        auto. *)
    - rewrite exp_sepcon1; apply exp_derives; intros sh.
      rewrite exp_sepcon1; apply exp_derives; intros t2.
      rewrite exp_sepcon1; apply exp_derives; intros v2.
      normalize.
      eapply derives_trans; [apply sepcon_derives; [apply derives_refl |]; apply now_later |].
      rewrite <- later_sepcon.
      apply later_derives.
      apply andp_right; [apply andp_right; [apply andp_right |] |].
      * eapply derives_trans; [apply sepcon_derives; [| apply derives_refl]; apply andp_left1, andp_left1, andp_left1, derives_refl |].
        intro rho; simpl.
        apply (predicates_sl.extend_sepcon (extend_tc.extend_tc_lvalue Delta e rho)).
      * unfold local, lift1; unfold_lift; intro rho; simpl.
        eapply derives_trans; [apply sepcon_derives; [| apply derives_refl]; apply andp_left1, andp_left1, andp_left2, derives_refl |].
        rewrite <- (andp_TT (prop _)) at 1.
        normalize.
      * eapply derives_trans; [apply sepcon_derives; [| apply derives_refl]; apply andp_left1, andp_left2, derives_refl |].
        rewrite sepcon_assoc.
        apply sepcon_derives; auto.
      * eapply derives_trans; [apply sepcon_derives; [| apply derives_refl]; apply andp_left2, derives_refl |].
        rewrite subst_sepcon.
        rewrite (closed_wrt_subst _ _ F); auto.
        unfold closed_wrt_modvars in H.
        rewrite <- modifiedvars_aux.
        auto.
    - rewrite exp_sepcon1; apply exp_derives; intros sh.
      rewrite exp_sepcon1; apply exp_derives; intros e1.
      rewrite exp_sepcon1; apply exp_derives; intros t1.
      rewrite exp_sepcon1; apply exp_derives; intros v2.
      normalize.
      eapply derives_trans; [apply sepcon_derives; [apply derives_refl |]; apply now_later |].
      rewrite <- later_sepcon.
      apply later_derives.
      apply andp_right; [apply andp_right; [apply andp_right |] |].
      * eapply derives_trans; [apply sepcon_derives; [| apply derives_refl]; apply andp_left1, andp_left1, andp_left1, derives_refl |].
        intro rho; simpl.
        apply (predicates_sl.extend_sepcon (extend_tc.extend_tc_lvalue Delta e1 rho)).
      * unfold local, lift1; unfold_lift; intro rho; simpl.
        eapply derives_trans; [apply sepcon_derives; [| apply derives_refl]; apply andp_left1, andp_left1, andp_left2, derives_refl |].
        rewrite <- (andp_TT (prop _)) at 1.
        normalize.
      * eapply derives_trans; [apply sepcon_derives; [| apply derives_refl]; apply andp_left1, andp_left2, derives_refl |].
        rewrite sepcon_assoc.
        apply sepcon_derives; auto.
      * eapply derives_trans; [apply sepcon_derives; [| apply derives_refl]; apply andp_left2, derives_refl |].
        rewrite subst_sepcon.
        rewrite (closed_wrt_subst _ _ F); auto.
        unfold closed_wrt_modvars in H.
        rewrite <- modifiedvars_aux.
        auto.

  + eapply semax_conseq; [.. | apply IHsemax; auto].
    - apply sepcon_derives_full; [exact H0 |].
      reduce2derives.
      auto.
    - destruct R, R'.
      apply sepcon_derives_full; [exact H1 |].
      reduce2derives.
      auto.
    - destruct R, R'.
      apply sepcon_derives_full; [exact H2 |].
      reduce2derives.
      auto.
    - destruct R, R'.
      apply sepcon_derives_full; [exact H3 |].
      reduce2derives.
      auto.
    - intros; destruct R, R'.
      apply sepcon_derives_full; [apply H4 |].
      reduce2derives.
      auto.
  + rewrite FF_sepcon.
    apply semax_builtin.
  + rewrite frame_normal.
    eapply semax_pre; [.. | apply semax_call; auto].
    - apply andp_left2.
      rewrite exp_sepcon1. apply exp_derives; intros argsig.
      rewrite exp_sepcon1. apply exp_derives; intros retsig.
      rewrite exp_sepcon1. apply exp_derives; intros cc.
      rewrite exp_sepcon1. apply exp_derives; intros A.
      rewrite exp_sepcon1. apply exp_derives; intros P.
      rewrite exp_sepcon1. apply exp_derives; intros Q.
      rewrite exp_sepcon1. apply exp_derives; intros NEP.
      rewrite exp_sepcon1. apply exp_derives; intros NEQ.
      normalize.
      apply andp_right; [apply andp_right |];[apply andp_right|..].
      * apply wand_sepcon_adjoint.
        apply andp_left1.
        apply andp_left1.
        apply andp_left1.
        apply wand_sepcon_adjoint.
        eapply derives_trans; [apply sepcon_derives; [apply derives_refl | apply now_later] |].
        (* rewrite <- later_sepcon. *)
        (* apply later_derives. *)
        intro rho.
        simpl.
        epose proof (predicates_sl.extend_sepcon (extend_tc.extend_andp _ _ (extend_tc.extend_tc_expr Delta a rho) (extend_tc.extend_tc_exprlist Delta (snd (split argsig)) bl rho))).
        repeat (try rewrite !andp_rewrite in H1;
          try rewrite !prop_rewrite in H1;
          try rewrite !exp_rewrite in H1;
          try rewrite !imp_rewrite;
          try rewrite !allp_rewrite;
          try rewrite !sepcon_rewrite in H1
        ).
        apply derives_rewrite.
        change extend_tc.tc_expr with tc_expr in H1.
        change extend_tc.tc_exprlist with tc_exprlist in H1.
        apply H1.
      * apply wand_sepcon_adjoint.
        apply andp_left1, andp_left1, andp_left2.
        apply wand_sepcon_adjoint.
        apply derives_left_sepcon_right_corable; auto.
        intro.
        apply corable_func_ptr.
      * apply wand_sepcon_adjoint.
        apply andp_left1, andp_left2.
        apply wand_sepcon_adjoint.
        apply derives_left_sepcon_right_corable; auto.
        intro.
        unfold model_lemmas.precise_fun_at_ptr. unfold liftx.
        unfold_lift. rewrite !allp_rewrite.
        apply corable_allp. intros.
        rewrite !allp_rewrite. apply corable_allp. intros.
        rewrite !imp_rewrite. apply corable_imp.
        { rewrite !andp_rewrite. apply corable_andp.
          + rewrite !prop_rewrite. apply corable_prop.
          + change corable with corable.corable.
            apply assert_lemmas.corable_func_at.
        }
        { rewrite !prop_rewrite. apply corable_prop. }
      * apply wand_sepcon_adjoint.
        apply andp_left2.
        apply wand_sepcon_adjoint.
        eapply derives_trans; [apply sepcon_derives; [apply derives_refl | apply now_later] |].
        rewrite <- later_sepcon.
        apply later_derives.
        rewrite exp_sepcon1. apply exp_derives; intros ts.
        rewrite exp_sepcon1. apply exp_derives; intros x.
        rewrite sepcon_assoc; apply sepcon_derives; auto.

        destruct H0 as [? [? ?]].
        rewrite <- (oboxopt_closed Delta ret F) at 1
        (* Locate tc_fn_return_temp_guard_opt.
        2:{ eapply tc_fn_return_temp_guard_opt; eauto. } *)
        by (try eapply tc_fn_return_temp_guard_opt; eauto).
        eapply derives_trans; [apply oboxopt_sepcon |].
        apply oboxopt_K.
        rewrite <- (sepcon_emp (maybe_retval _ _ _)) at 2.
        eapply derives_trans; [| apply wand_frame_hor].
        apply sepcon_derives; auto.
        apply wand_sepcon_adjoint.
        rewrite sepcon_emp; auto.

  + apply semax_label.
    apply IHsemax; auto.
  + rewrite FF_sepcon.
    apply semax_goto.
  + 
    rewrite FF_sepcon.
    apply semax_switch.
  (* rewrite corable_andp_sepcon1 by (apply corable_prop).
    eapply semax_switch; auto.
    - intro.
      eapply derives_trans; [apply sepcon_derives; [apply H0 | apply derives_refl] |].
      apply (predicates_sl.extend_sepcon (extend_tc.extend_tc_expr Delta a rho)).
    - intros.
      rewrite <- corable_andp_sepcon1 by (intro; apply corable_prop).
      replace (switch_ret_assert (frame_ret_assert R F)) with
        (frame_ret_assert (switch_ret_assert R) F)
        by (destruct R; simpl; f_equal; extensionality rho; apply pred_ext; normalize).
      apply (H2 n).
      eapply semax_lemmas.closed_Sswitch; eauto. *)

Qed.

