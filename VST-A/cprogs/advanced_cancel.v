Require Import VST.floyd.base.
Require Import VST.floyd.seplog_tactics.
Local Open Scope logic.

Inductive syntactic_cancel: list mpred -> list mpred -> list mpred -> list mpred -> Prop :=
| syntactic_cancel_nil: forall R, syntactic_cancel R nil R nil
| syntactic_cancel_cons_succeed_full: forall n R0 R L0 L F Res,
    nth_error R n = Some R0 ->
    R0 |-- L0 ->
    syntactic_cancel (delete_nth n R) L F Res ->
    syntactic_cancel R (L0 :: L) F Res
| syntactic_cancel_cons_succeed_partial: forall n R0 R L0 L F0 F Res,
    nth_error R n = Some R0 ->
    R0 * F0 |-- L0 ->
    syntactic_cancel (delete_nth n R) (F0 :: L) F Res ->
    syntactic_cancel R (L0 :: L) F Res
| syntactic_cancel_cons_fail: forall R L0 L F Res,
    syntactic_cancel R L F Res ->
    syntactic_cancel R (L0 :: L) F (L0 :: Res).

Lemma syntactic_cancel_cons: forall nR0 R L0 L F0 F Res,
  find_nth_preds (fun R0 => R0 * F0 |-- L0) R nR0 ->
  syntactic_cancel match nR0 with
                   | Some (n, _) => delete_nth n R
                   | None => R
                   end
                   L F Res /\ (F0 = emp \/ nR0 = None) \/
  syntactic_cancel match nR0 with
                   | Some (n, _) => delete_nth n R
                   | None => R
                   end
                   (F0 :: L) F Res /\ isSome nR0 ->
  syntactic_cancel R (L0 :: L) F (let Res' := Res in
                                 match nR0 with
                                 | Some _ => Res'
                                 | None => L0 :: Res'
                                 end).
Proof.
  intros.
  destruct nR0 as [[? ?]|]; [destruct H0 |].
  + destruct H0.
    destruct H1; [| congruence].
    subst F0.
    apply find_nth_preds_Some in H.
    destruct H.
    rewrite sepcon_emp in H1.
    eapply syntactic_cancel_cons_succeed_full; eauto.
  + apply find_nth_preds_Some in H.
    destruct H0.
    destruct H.
    eapply syntactic_cancel_cons_succeed_partial; eauto.
  + destruct H0 as [[? _] | [? ?]]; [| tauto].
    eapply syntactic_cancel_cons_fail; eauto.
Qed.

Lemma delete_nth_SEP: forall R n R0,
  nth_error R n = Some R0 ->
  fold_right_sepcon R |-- R0 * fold_right_sepcon (delete_nth n R).
Proof.
  intros.
  revert R H; induction n; intros; destruct R; try solve [inv H].
  + inv H.
    simpl.
    auto.
  + simpl in H.
    apply IHn in H.
    simpl.
    rewrite <- sepcon_assoc, (sepcon_comm _ m), sepcon_assoc.
    apply sepcon_derives; auto.
Qed.

Lemma syntactic_cancel_spec1: forall G1 L1 G2 L2 F,
  syntactic_cancel G1 L1 G2 L2 ->
  fold_right_sepcon G2 |-- fold_right_sepcon L2 * F ->
  fold_right_sepcon G1 |-- fold_right_sepcon L1 * F.
Proof.
  intros.
  revert F H0; induction H; intros.
  + auto.
  + apply IHsyntactic_cancel in H2.
    simpl.
    rewrite sepcon_assoc.
    eapply derives_trans; [| apply sepcon_derives; [apply derives_refl | apply H2]].
    clear IHsyntactic_cancel H2.
    eapply derives_trans; [apply delete_nth_SEP; eauto |].
    apply sepcon_derives; auto.
  + apply IHsyntactic_cancel in H2.
    simpl.
    rewrite sepcon_assoc.
    simpl in H2.
    eapply derives_trans; [| apply sepcon_derives; [apply H0 | apply derives_refl]].
    rewrite sepcon_assoc.
    rewrite <- (sepcon_assoc F0).
    eapply derives_trans; [| apply sepcon_derives; [apply derives_refl | apply H2]].
    clear IHsyntactic_cancel H2.
    eapply derives_trans; [apply delete_nth_SEP; eauto |].
    apply derives_refl.
  + simpl in H0.
    rewrite (sepcon_comm L0), sepcon_assoc in H0.
    apply (IHsyntactic_cancel (L0*F0)) in H0.
    eapply derives_trans; [exact H0 |].
    simpl.
    rewrite <- sepcon_assoc.
    apply sepcon_derives; auto.
    rewrite sepcon_comm; auto.
Qed.

Lemma syntactic_cancel_solve3:
  fold_right_sepcon nil |-- fold_right_sepcon nil.
Proof.
  auto.
Qed.

Lemma syntactic_cancel_spec3: forall G1 L1 G2 L2,
  syntactic_cancel G1 L1 G2 L2 ->
  fold_right_sepcon G2 |-- fold_right_sepcon L2 ->
  fold_right_sepcon G1 |-- fold_right_sepcon L1.
Proof.
  intros.
  rewrite <- (sepcon_emp (fold_right_sepcon L1)).
  eapply syntactic_cancel_spec1; eauto.
  rewrite sepcon_emp; auto.
Qed.

Ltac advanced_syntactic_cancel local_tac :=
  repeat first
         [ simple apply syntactic_cancel_nil
         | simple eapply syntactic_cancel_cons;
           [ find_nth local_tac
           | match goal with
             | |- _ /\ (emp = emp \/ _) \/ _ =>
                    left;
                    split; [| left; reflexivity]
             | |- _ /\ (_ \/ None = None) \/ _ =>
                    left;
                    split; [| left; reflexivity]
                  (* This is intensional "left".
                     This is used to instantiate the unused F0 *)
             | |- _ \/ (_ /\ isSome (Some _)) =>
                    right;
                    split; [| exact I]
             end;
             cbv iota; unfold delete_nth; cbv zeta iota
           ]
         ].

(*
Section Test.

Parameters A B C D E F: mpred.
Axiom Foo1: A * B |-- C.
Axiom Foo2: C * D |-- E.

Ltac foo :=
  idtac;
  match goal with
  | |- ?P * _ |-- ?P => rewrite <- (sepcon_emp P) at 2; apply derives_refl
  | |- D * _ |-- E => eapply derives_trans; [| apply Foo2];
                      rewrite (sepcon_comm C D); apply derives_refl
  | |- A * _ |-- C => eapply derives_trans; [| apply Foo1];
                      apply derives_refl
  end.

Goal A * B * F * D |-- E * F.
eapply symbolic_cancel_setup;
  [ construct_fold_right_sepcon
  | construct_fold_right_sepcon
  | fold_abnormal_mpred
  | cbv iota beta delta [before_symbol_cancel];
    eapply syntactic_cancel_spec3].


  advanced_syntactic_cancel foo.

  cbv iota; cbv zeta beta.

  auto.
Qed.

End Test.
*)
