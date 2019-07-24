Require Export VST.floyd.proofauto.
(* Require Import AClight.AClight. *)

(* Two layers : (1) intro and revert (2) multi-cond *)

Lemma derives_add_Prop_left : forall (P0 : Prop) P Q R Post,
  P0 ->
  (PROPx (P0 :: P) (LOCALx Q (SEPx R))) |-- Post ->
  (PROPx P (LOCALx Q (SEPx R))) |-- Post.
Proof.
  intros.
  eapply derives_trans. 2 : apply H0.
  clear H0.
  apply andp_prop_derives.
  - simpl. tauto.
  - auto.
Qed.

Lemma exp_left_revert : forall A (P: A -> environ -> mpred) Q,
  exp P |-- Q -> (forall a, P a |-- Q).
Proof.
  intros.
  eapply derives_trans. 2 : apply  H.
  eapply exp_right. apply derives_refl.
Qed.

(*Local *)  Ltac entail_evar_post :=
  simple apply andp_left2;
  lazymatch goal with
  | |- _ |-- ?Post =>
    repeat match goal with
    | x : ?T |- _ =>
      first [
        assert_fails constr_eq x Post
      | fail 2 (* break *)
      ];
      ignore (T : Prop);
      refine (derives_add_Prop_left _ _ _ _ _ x _);
      clear x
    end;
    repeat match goal with
    | x : ?T |- _ =>
      first [
        assert_fails constr_eq x Post
      | fail 2 (* break *)
      ];
      first [
        subst x
      | revert x;
        refine (exp_left_revert T (fun x => _) _ _)
      | fail 3 "Fail to revert existentail variables"
      ]
    end;
    subst Post;
    apply derives_refl
  end.

(*Local *) Ltac semax_seq_evar :=
  let Post_name := fresh "Post" in
  evar (Post_name : assert);
  let Post := Post_name in
  first [
    simple apply semax_seq with Post
  | fail 1 "Fail in simple apply semax_seq with Post"
  ];
  only 2: (subst Post_name; abbreviate_semax).

(*Local *)Ltac repeat_Intros :=
  repeat lazymatch goal with
  | |- semax _ (EX x, _) _ _ =>
    first [
      let x := fresh x in Intros x
    | fail 2 "Fail in Intros"
    ]
  | _ =>
    (* This is for existential variables inside SEP. This case occurs in testing with proofs from VST
     * but I don't know whether we still need this for VST-A. *)
    let x := fresh "x" in Intros x
  end.

Ltac forwardE :=
  repeat apply -> seq_assoc;
  lazymatch goal with
  | |- semax _ _ Sbreak _ =>
    repeat_Intros; forward
  | |- semax _ _ Scontinue _ =>
    repeat_Intros; forward
  | |- semax _ _ (Sreturn _) _ =>
    repeat_Intros; forward
  | |- semax _ _ (Ssequence (Sbreak _)) _ =>
    repeat_Intros; forward
  | |- semax _ _ (Ssequence (Scontinue _)) _ =>
    repeat_Intros; forward
  | |- semax _ _ (Ssequence ((Sreturn _) _)) _ =>
    repeat_Intros; forward
  | |- semax _ _ (Ssequence _ _) _ =>
    semax_seq_evar; [
      (* first statement *)
      repeat_Intros;
      forward;
      entail_evar_post
    | ]
  | |- semax _ _ _ _ => (* single statement *)
    repeat_Intros; forward
  end.


