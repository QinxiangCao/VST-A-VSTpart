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
Export SeparationLogicAsLogicSoundness.MainTheorem.CSHL_Sound.DeepEmbedded.
Require Import VST.floyd.proofauto.


Lemma nil_cons {A:Type} {a:A} {b: list A}: a :: b <> [].
Proof. intros C. inv C. Qed.


Lemma imp_trans: forall {A B C}, (A -> B) -> (B -> C) -> (A -> C). 
Proof. tauto. Qed.


(** Noreturn Lemmas *)

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

Lemma semax_noreturn_inv {CS: compspecs} {Espec: OracleKind} 
  (Delta: tycontext):
  forall Pre s Post Post',
    noreturn s = true ->
    RA_normal Post = RA_normal Post' ->
    RA_break Post = RA_break Post' ->
    RA_continue Post = RA_continue Post' ->
    @semax CS Espec Delta Pre s Post -> @semax CS Espec Delta Pre s Post'.
Proof.
  intros.
  revert Post' H0 H1 H2.
  induction H3; intros.
  + change (noreturn c && noreturn d = true)%bool in H.
    rewrite andb_true_iff in H.
    specialize (IHsemax1 (proj1 H) _ H0 H1 H2).
    specialize (IHsemax2 (proj2 H) _ H0 H1 H2).
    eapply SeparationLogicAsLogic.AuxDefs.semax_ifthenelse;auto.
  + change (noreturn h && noreturn t = true)%bool in H.
    rewrite andb_true_iff in H.
    specialize (IHsemax1 (proj1 H)).
    specialize (IHsemax2 (proj2 H) _ H0 H1 H2).
    eapply SeparationLogicAsLogic.AuxDefs.semax_seq; [| eauto].
    apply IHsemax1; destruct Post', R; auto.
  + rewrite H1.
    apply SeparationLogicAsLogic.AuxDefs.semax_break.
  + rewrite H2.
    apply SeparationLogicAsLogic.AuxDefs.semax_continue.
  + simpl in H. change (noreturn body && noreturn incr = true)%bool in H.
    rewrite andb_true_iff in H.
    specialize (IHsemax1 (proj1 H) (loop1_ret_assert Q' Post')).
    specialize (IHsemax2 (proj2 H)  (loop2_ret_assert Q Post')).
    eapply SeparationLogicAsLogic.AuxDefs.semax_loop with (Q'0:=Q').
    - destruct Post', R.
      unfold loop1_ret_assert in H3_.
      simpl in *. subst. apply IHsemax1;auto.
    - destruct Post', R.
      simpl in *. subst. apply IHsemax2;auto.
  + apply SeparationLogicAsLogic.AuxDefs.semax_switch; auto.
    intros n; specialize (H2 n).
    simpl in H.
    apply (noreturn_ls_spec' _ (Int.unsigned n)) in H.
    specialize (H2 H).
    apply H2; destruct Post', R; simpl; auto.
  + eapply semax_post with (normal_ret_assert R);
      [intros; apply andp_left2; try apply FF_left; rewrite H0; auto .. |].
    apply SeparationLogicAsLogic.AuxDefs.semax_call_backward.
  + inv H.
  + eapply semax_post with (normal_ret_assert P);
      [intros; apply andp_left2; try apply FF_left; rewrite H0; auto .. |].
    apply SeparationLogicAsLogic.AuxDefs.semax_set_ptr_compare_load_cast_load_backward.
  + eapply semax_post with (normal_ret_assert P);
      [intros; apply andp_left2; try apply FF_left; rewrite H0; auto .. |].
    apply SeparationLogicAsLogic.AuxDefs.semax_store_backward.
  + eapply semax_post with (normal_ret_assert P);
      [intros; apply andp_left2; try apply FF_left; rewrite H0; auto .. |].
    apply SeparationLogicAsLogic.AuxDefs.semax_skip.
  + apply SeparationLogicAsLogic.AuxDefs.semax_builtin.
  + specialize (IHsemax H _ H0 H1 H2).
    apply SeparationLogicAsLogic.AuxDefs.semax_label; auto.
  + apply SeparationLogicAsLogic.AuxDefs.semax_goto.
  + apply (SeparationLogicAsLogic.AuxDefs.semax_conseq _ P' (Build_ret_assert (RA_normal R') (RA_break R') (RA_continue R') (RA_return Post'))).
    - exact H0.
    - rewrite <- H6; exact H1.
    - rewrite <- H7; exact H2.
    - rewrite <- H8; exact H3.
    - intros. apply derives_full_refl.
    - apply IHsemax; auto.
Qed.