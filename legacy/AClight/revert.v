Require Import VST.floyd.proofauto.

Lemma revert_Prop : forall (P0 : Prop) P Q R Post,
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

Lemma revert_exp : forall A (P: A -> environ -> mpred) Q,
  exp P |-- Q -> (forall a, P a |-- Q).
Proof.
  intros.
  eapply derives_trans. 2 : apply  H.
  eapply exp_right. apply derives_refl.
Qed.

(** revert all Props appear after Post in context to PROP *)
Ltac revert_Props :=
  lazymatch goal with
  | |- _ |-- ?Post =>
    repeat match goal with
    | x : ?T |- _ =>
      first [
        assert_fails constr_eq x Post
      | fail 2 (* break *)
      ];
      ignore (T : Prop);
      refine (revert_Prop _ _ _ _ _ x _);
      clear x
    | _ =>
      fail 2 "Post not found in context"
    end
  end.

(** revert all variables excluding asserts appear after Post in context to EX quantifiers *)
Ltac revert_exps :=
  lazymatch goal with
  | |- _ |-- ?Post =>
    repeat match goal with
    | x : ?T |- _ =>
      first [
        assert_fails constr_eq x Post
      | fail 2 (* break *)
      ];
      first [
        subst x
      | revert x;
        refine (revert_exp T (fun x => _) _ _)
      | fail 3 "Fail to revert existentail variables"
      ]
    end
  end.

Ltac revert_exp_and_Prop :=
  simple apply andp_left2;
  revert_Props;
  revert_exps.

Ltac entail_evar_post :=
  lazymatch goal with
  | |- _ |-- ?Post =>
    revert_exp_and_Prop;
    subst Post;
    apply derives_refl
  end.
