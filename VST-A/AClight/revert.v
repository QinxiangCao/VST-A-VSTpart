Require Import VST.floyd.proofauto.

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

Ltac entail_evar_post :=
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