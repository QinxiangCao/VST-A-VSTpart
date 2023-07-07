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
Require Import Csplit.strong.
Local Open Scope logic.

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
  + apply semax_pre with (!! (bool_type (typeof b) = true) && tc_expr Delta (Eunop Cop.Onotbool b (Ctypes.Tint I32 Signed noattr)) && (P * F)).
    - normalize.
      apply andp_left2, andp_right.
      * eapply derives_trans; [apply sepcon_derives; [apply andp_left1 |]; apply derives_refl |].
        intro rho.
        apply (predicates_sl.extend_sepcon (extend_tc.extend_tc_expr Delta (Eunop Cop.Onotbool b (Ctypes.Tint I32 Signed noattr)) rho)).
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
      rewrite exp_sepcon1. apply exp_derives; intros b.
      rewrite exp_sepcon1. apply exp_derives; intros id.
      rewrite exp_sepcon1. apply exp_derives; intros fs.
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
        unfold local, lift1.
        apply corable_prop.
      * apply wand_sepcon_adjoint.
        apply andp_left1. apply andp_left2.
        apply wand_sepcon_adjoint.
        apply derives_left_sepcon_right_corable; auto.
        unfold_lift. intro rho.
        apply assert_lemmas.corable_funspec_sub_si.
      * apply wand_sepcon_adjoint.
        apply andp_left2.
        apply wand_sepcon_adjoint.
        eapply derives_trans; [apply sepcon_derives; [apply derives_refl | apply now_later] |].
        rewrite <- later_sepcon.
        apply later_derives.
        rewrite exp_sepcon1. apply exp_derives; intros ts.
        rewrite exp_sepcon1. apply exp_derives; intros x.
        rewrite sepcon_assoc; apply sepcon_derives; auto.

        destruct H0 as [? [? [? ?]]].
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


Lemma semax_pre_simple: forall {Espec: OracleKind}{cs: compspecs},
 forall P' Delta P c R,
     P |-- P' ->
     @semax cs Espec Delta P' c R  -> @semax cs Espec Delta P c R.
Proof.
intros; eapply semax_pre; [| eauto].
apply andp_left2; auto.
Qed.



Theorem semax_load_backward: forall {CS: compspecs} {Espec: OracleKind} (Delta: tycontext),
  forall (P: environ->mpred) id e1,
    @semax CS Espec Delta
        (EX sh: share, EX t2: type, EX v2: val,
              !! (typeof_temp Delta id = Some t2 /\
                  is_neutral_cast (typeof e1) t2 = true /\
                  readable_share sh) &&
         |> ( (tc_lvalue Delta e1) &&
              local (`(tc_val (typeof e1) v2)) &&
              (`(mapsto sh (typeof e1)) (eval_lvalue e1) (`v2) * TT) &&
              subst id (`v2) P))
        (Sset id e1) (normal_ret_assert P).
Proof.
  intros.
  eapply semax_pre_simple; [| apply semax_set_ptr_compare_load_cast_load_backward].
  apply orp_right1, orp_right2; auto.
Qed.


Theorem semax_load_forward: forall {CS: compspecs} {Espec: OracleKind} (Delta: tycontext),
  forall  sh id P e1 t2 (v2: val),
    typeof_temp Delta id = Some t2 ->
    is_neutral_cast (typeof e1) t2 = true ->
    readable_share sh ->
    local (tc_environ Delta) && P |-- `(mapsto sh (typeof e1)) (eval_lvalue e1) (` v2) * TT ->
    @semax CS Espec Delta
       (|> ( (tc_lvalue Delta e1) &&
       local (`(tc_val (typeof e1) v2)) &&
          P))
       (Sset id e1)
       (normal_ret_assert (EX old:val, local (`eq (eval_id id) (` v2)) &&
                                          (subst id (`old) P))).
Proof.
  intros.
  eapply semax_pre; [| apply semax_load_backward].
  apply (exp_right sh).
  apply (exp_right t2).
  apply (exp_right v2).
  apply andp_right; [apply prop_right; auto |].
  apply later_ENTAIL.
  rewrite (andp_assoc _ _ (subst _ _ _)).
  apply andp_ENTAIL; [apply ENTAIL_refl |].
  apply andp_right; auto.
  rewrite subst_exp.
  intros rho.
  change (local (tc_environ Delta) rho && P rho
  |-- EX b : val,
       subst id (` v2) (local ((` eq) (eval_id id) (` v2)) && subst id (` b) P) rho).
  apply (exp_right (eval_id id rho)).
  autorewrite with subst.
  unfold local, lift1; unfold_lift; simpl.
  unfold typeof_temp in H.
  destruct ((temp_types Delta) ! id) eqn:?H; inv H.
  normalize.
  apply andp_right; [| erewrite subst_self by eauto; auto].
  apply prop_right.
  unfold subst.
  apply eval_id_same.
Qed.


Lemma semax_post': forall R' Espec {cs: compspecs} Delta R P c,
           local (tc_environ Delta) && R' |-- R ->
      @semax cs Espec Delta P c (normal_ret_assert R') ->
      @semax cs Espec Delta P c (normal_ret_assert R).
Proof. intros. eapply semax_post; eauto.
 simpl RA_normal; auto.
 simpl RA_break; normalize.
 simpl RA_continue; normalize.
 intro vl; simpl RA_return; normalize.
Qed.

Lemma semax_pre_post': forall P' R' Espec {cs: compspecs} Delta R P c,
      local (tc_environ Delta) && P |-- P' ->
      local (tc_environ Delta) && R' |-- R ->
      @semax cs Espec Delta P' c (normal_ret_assert R') ->
      @semax cs Espec Delta P c (normal_ret_assert R).
Proof. intros.
 eapply semax_pre; eauto.
 eapply semax_post'; eauto.
Qed.

(* Copied from canon.v end. *)

Lemma semax_post'': forall R' Espec {cs: compspecs} Delta R P c,
           local (tc_environ Delta) && R' |-- RA_normal R ->
      @semax cs Espec Delta P c (normal_ret_assert R') ->
      @semax cs Espec Delta P c R.
Proof. intros. eapply semax_post; eauto.
 simpl RA_normal; auto.
 simpl RA_break; normalize.
 simpl RA_continue; normalize.
 intro vl; simpl RA_return; normalize.
Qed.

Lemma semax_pre_post'': forall P' R' Espec {cs: compspecs} Delta R P c,
      local (tc_environ Delta) && P |-- P' ->
      local (tc_environ Delta) && R' |-- RA_normal R ->
      @semax cs Espec Delta P' c (normal_ret_assert R') ->
      @semax cs Espec Delta P c R.
Proof. intros.
 eapply semax_pre; eauto.
 eapply semax_post''; eauto.
Qed.


Theorem semax_cast_load_backward: forall {CS: compspecs} {Espec: OracleKind} (Delta: tycontext),
  forall (P: environ->mpred) id e,
    @semax CS Espec Delta
        (EX sh: share, EX e1: expr, EX t1: type, EX v2: val,
              !! (e = Ecast e1 t1 /\
                  typeof_temp Delta id = Some t1 /\
                  cast_pointer_to_bool (typeof e1) t1 = false /\
                  readable_share sh) &&
         |> ( (tc_lvalue Delta e1) &&
              local (`(tc_val t1) (`(eval_cast (typeof e1) t1 v2))) &&
              (`(mapsto sh (typeof e1)) (eval_lvalue e1) (`v2) * TT) &&
              subst id (`(force_val (sem_cast (typeof e1) t1 v2))) P))
        (Sset id e) (normal_ret_assert P).
Proof.
  intros.
  apply semax_extract_exists; intro sh.
  apply semax_extract_exists; intro e1.
  apply semax_extract_exists; intro t2.
  apply semax_extract_exists; intro v2.
  apply semax_extract_prop; intros [He [? [? ?]]].
  subst e.
  rewrite (andp_assoc _ _ (subst _ _ _)).
  eapply semax_pre';[ ..| apply semax_set_ptr_compare_load_cast_load_backward].
  apply orp_right2.
  apply exp_right with (x:=sh).
  apply exp_right with (x:=e1).
  apply exp_right with (x:=t2).
  apply exp_right with (x:=v2).
  apply andp_right.
  { apply prop_right. auto. }
  apply andp_left2. apply andp_left2.
  apply later_derives. solve_andp.
Qed.



Theorem semax_cast_load_forward: forall {CS: compspecs} {Espec: OracleKind} (Delta: tycontext),
  forall sh id P e1 t1 (v2: val),
    typeof_temp Delta id = Some t1 ->
   cast_pointer_to_bool (typeof e1) t1 = false ->
    readable_share sh ->
    local (tc_environ Delta) && P |-- `(mapsto sh (typeof e1)) (eval_lvalue e1) (`v2) * TT ->
    @semax CS Espec Delta
       (|> ( (tc_lvalue Delta e1) &&
       local (`(tc_val t1) (`(eval_cast (typeof e1) t1 v2))) &&
          P))
       (Sset id (Ecast e1 t1))
       (normal_ret_assert (EX old:val, local (`eq (eval_id id) (subst id (`old) (`(eval_cast (typeof e1) t1 v2)))) &&
                                          (subst id (`old) P))).
Proof.
  intros.
  eapply semax_pre; [| apply semax_cast_load_backward].
  apply (exp_right sh).
  apply (exp_right e1).
  apply (exp_right t1).
  apply (exp_right v2).
  apply andp_right; [apply prop_right; auto |].
  apply later_ENTAIL.
  rewrite (andp_assoc _ _ (subst _ _ _)).
  apply andp_ENTAIL; [apply ENTAIL_refl |].
  apply andp_right; auto.
  rewrite subst_exp.
  intros rho.
  change (local (tc_environ Delta) rho && P rho
  |-- EX b : val,
       subst id (` (force_val (sem_cast (typeof e1) t1 v2))) (local ((` eq) (eval_id id) (subst id (` b) (` (eval_cast (typeof e1) t1 v2)))) && subst id (` b) P) rho).
  apply (exp_right (eval_id id rho)).
  autorewrite with subst.
  unfold local, lift1; unfold_lift; simpl.
  unfold typeof_temp in H.
  destruct ((temp_types Delta) ! id) eqn:?H; inv H.
  normalize.
  apply andp_right; [| erewrite subst_self by eauto; auto].
  apply prop_right.
  unfold subst.
  apply eval_id_same.
Qed.


Theorem semax_set_backward: forall {CS: compspecs} {Espec: OracleKind} (Delta: tycontext),
  forall (P: environ->mpred) id e,
    @semax CS Espec Delta
        (|> ( (tc_expr Delta e) &&
             (tc_temp_id id (typeof e) Delta e) &&
             subst id (eval_expr e) P))
          (Sset id e) (normal_ret_assert P).
Proof.
  intros.
  eapply semax_pre_simple; [| apply semax_set_ptr_compare_load_cast_load_backward].
  apply orp_right1, orp_right1; auto.
Qed.

Theorem semax_set_forward: forall {CS: compspecs} {Espec: OracleKind} (Delta: tycontext),
  forall (P: environ->mpred) id e,
    @semax CS Espec Delta
        (|> ( (tc_expr Delta e) &&
             (tc_temp_id id (typeof e) Delta e) &&
          P))
          (Sset id e)
        (normal_ret_assert
          (EX old:val, local (`eq (eval_id id) (subst id (`old) (eval_expr e))) &&
                            subst id (`old) P)).
Proof.
  intros.
  eapply semax_pre; [| apply semax_set_backward].
  apply later_ENTAIL.
  apply andp_right; [solve_andp |].
  rewrite subst_exp.
  intro rho.
  simpl.
  apply (exp_right (eval_id id rho)).
  unfold_lift; unfold local, lift1.
  simpl.
  unfold subst.
  normalize.
  rewrite !env_set_env_set.
  assert (tc_temp_id id (typeof e) Delta e rho |-- !! (env_set rho id (eval_id id rho) = rho)).
  + unfold tc_temp_id, typecheck_temp_id.
    destruct ((temp_types Delta) ! id) eqn:?H; [| apply FF_left].
    apply prop_right.
    eapply env_set_eval_id; eauto.
  + rewrite (add_andp _ _ H0).
    rewrite !andp_assoc.
    apply andp_left2.
    apply andp_left2.
    normalize.
    rewrite H1.
    normalize.
Qed.


Lemma semax_orp:
  forall {CS: compspecs} {Espec: OracleKind},
  forall Delta P1 P2 c Q,
           @semax CS Espec Delta P1 c Q ->
           @semax CS Espec Delta P2 c Q ->
           @semax CS Espec Delta (P1 || P2) c Q.
Proof.
  intros.
  eapply semax_pre with (EX b: bool, if b then P1 else P2).
  + apply andp_left2.
    apply orp_left.
    - apply (exp_right true), derives_refl.
    - apply (exp_right false), derives_refl.
  + apply semax_extract_exists.
    intros.
    destruct x; auto.
Qed.


Theorem semax_set_load_cast_load_backward: forall {CS: compspecs} {Espec: OracleKind} (Delta: tycontext),
  forall (P: environ->mpred) id e,
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
        (Sset id e) (normal_ret_assert P).
Proof.
  intros.
  apply semax_orp; [apply semax_orp  |].
  + apply semax_set_backward.
  + apply semax_load_backward.
  + apply semax_cast_load_backward.
Qed.

Theorem semax_store_backward: forall {CS: compspecs} {Espec: OracleKind} (Delta: tycontext) e1 e2 P,
   @semax CS Espec Delta
          (EX sh: share, !! writable_share sh && |> ( (tc_lvalue Delta e1) &&  (tc_expr Delta (Ecast e2 (typeof e1)))  &&
             ((`(mapsto_ sh (typeof e1)) (eval_lvalue e1)) * (`(mapsto sh (typeof e1)) (eval_lvalue e1) (`force_val (`(sem_cast (typeof e2) (typeof e1)) (eval_expr e2))) -* P))))
          (Sassign e1 e2)
          (normal_ret_assert P).
Proof.
  intros.
  eapply semax_pre';[..|apply semax_assign].
  solve_andp.
Qed.

Theorem semax_store_forward:
  forall {CS: compspecs} {Espec: OracleKind} (Delta: tycontext),
 forall e1 e2 sh P,
   writable_share sh ->
   @semax CS Espec Delta
          (|> ( (tc_lvalue Delta e1) &&  (tc_expr Delta (Ecast e2 (typeof e1)))  &&
             (`(mapsto_ sh (typeof e1)) (eval_lvalue e1) * P)))
          (Sassign e1 e2)
          (normal_ret_assert
             (`(mapsto sh (typeof e1)) (eval_lvalue e1) (`force_val (`(sem_cast (typeof e2) (typeof e1)) (eval_expr e2))) * P)).
Proof.
  intros.
  eapply semax_pre; [| apply semax_store_backward].
  apply (exp_right sh).
  normalize.
  apply andp_left2.
  apply later_derives.
  apply andp_derives; auto.
  apply sepcon_derives; auto.
  apply wand_sepcon_adjoint.
  rewrite sepcon_comm.
  apply derives_refl.
Qed.




Theorem semax_call_forward: forall {CS: compspecs} {Espec: OracleKind} (Delta: tycontext),
    forall A P Q NEP NEQ b id fs ts x (F: environ -> mpred) ret argsig retsig cc a bl,
           Cop.classify_fun (typeof a) =
           Cop.fun_case_f (type_of_params argsig) retsig cc ->
           (retsig = Tvoid -> ret = None) ->
          tc_fn_return Delta ret retsig ->
          precise_context Delta ->
          (glob_specs Delta) ! id = Some fs ->
  @semax CS Espec Delta
          (((tc_expr Delta a) && (tc_exprlist Delta (snd (split argsig)) bl))  &&
         (local (fun rho =>
            gvar_injection (ge_of rho) /\
            eval_expr a rho = Vptr b Ptrofs.zero /\
            global_block rho id b) &&
          `(funspec_sub_si fs (mk_funspec (argsig, retsig) cc A P Q NEP NEQ)) &&
          |>(F * `(P ts x: environ -> mpred) (make_args' (argsig,retsig) (eval_exprlist (snd (split argsig)) bl)))))
         (Scall ret a bl)
         (normal_ret_assert
            (EX old:val, substopt ret (`old) F * maybe_retval (Q ts x) retsig ret)).
Proof.
  intros.
  eapply semax_pre; [| apply semax_call].
  apply (exp_right argsig), (exp_right retsig), (exp_right cc), (exp_right A), (exp_right P), (exp_right Q), (exp_right NEP), (exp_right NEQ), (exp_right b), (exp_right id), (exp_right fs).
  rewrite !andp_assoc.
  apply andp_right; [apply prop_right; auto 6 |].
  apply andp_right; [solve_andp |].
  apply andp_right; [solve_andp |].
  rewrite andp_comm, imp_andp_adjoint.
  apply andp_left2.
  apply andp_left2.
  rewrite <- imp_andp_adjoint, andp_comm.
  apply andp_right. solve_andp.
  apply andp_right. solve_andp.
  rewrite andp_comm, imp_andp_adjoint. apply andp_left2.
  apply andp_left2.
  rewrite <- imp_andp_adjoint, andp_comm.
  apply later_left2.
  rewrite <- corable_andp_sepcon1 by (intro; apply corable_prop).
  apply (exp_right ts), (exp_right x).
  rewrite sepcon_comm.
  apply sepcon_derives; auto.
  eapply derives_trans; [apply (odiaopt_D _ ret) |].
    1: destruct ret; hnf in H1 |- *; [destruct ((temp_types Delta) ! i) |]; auto; congruence.
  rewrite <- oboxopt_odiaopt.
    2: destruct ret; hnf in H1 |- *; [destruct ((temp_types Delta) ! i) |]; auto; congruence.
  apply oboxopt_K.
  rewrite <- wand_sepcon_adjoint.
  rewrite <- exp_sepcon1.
  apply sepcon_derives; auto.
  apply odiaopt_derives_EX_substopt.
Qed.

(* 
Lemma semax_extract_later_prop:
  forall {CS: compspecs} {Espec: OracleKind},
  forall Delta (PP: Prop) P c Q,
           (PP -> @semax CS Espec Delta P c Q) ->
           @semax CS Espec Delta ((|> !!PP) && P) c Q.
Proof.
  intros.
  apply semax_extract_prop in H.
  eapply semax_pre_post_indexed_bupd; [.. | exact H].
  + apply andp_left2.
    eapply derives_trans; [| apply bupd_intro].
    rewrite orp_comm, distrib_andp_orp.
    apply andp_right.
    - apply andp_left1.
      apply later_prop.
    - apply orp_right1.
      solve_andp.
  + apply derives_bupd0_refl.
  + apply derives_bupd0_refl.
  + apply derives_bupd0_refl.
  + intros; apply derives_bupd0_refl.
Qed. *)