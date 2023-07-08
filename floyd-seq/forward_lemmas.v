Require Import FloydSeq.base2.
Require Import FloydSeq.client_lemmas.
Require Import FloydSeq.closed_lemmas.
Import Cop.
Import LiftNotation.
Require Import Csplit.strong.
Require Import Csplit.strongFacts.
Local Open Scope logic.

Lemma int_eq_false_e:
  forall i j, Int.eq i j = false -> i <> j.
Proof.
intros.
intro; subst.
rewrite Int.eq_true in H; inv H.
Qed.


Lemma semax_ifthenelse_PQR' :
   forall Espec {cs: compspecs} (v: val) Delta P Q R (b: expr) c d Post,
      bool_type (typeof b) = true ->
     ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
         (tc_expr Delta (Eunop Cop.Onotbool b tint))  ->
     ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
        local (`(eq v) (eval_expr b)) ->
     @semax cs Espec Delta (PROPx (typed_true (typeof b) v :: P) (LOCALx Q (SEPx R)))
                        c Post ->
     @semax cs Espec Delta (PROPx (typed_false (typeof b) v :: P) (LOCALx Q (SEPx R)))
                        d Post ->
     @semax cs Espec Delta (PROPx P (LOCALx Q (SEPx R)))
                         (Sifthenelse b c d) Post.
Proof.
 intros.
 eapply canon.semax_pre;  [ | apply semax_ifthenelse]; auto.
 instantiate (1:=(local (`(eq v) (eval_expr b)) && PROPx P (LOCALx Q (SEPx R)))).
 apply andp_right; try assumption.
 { apply andp_right;[apply prop_right;try assumption|];
   try assumption. } 
 apply andp_right; try assumption.
 apply andp_left2; auto.
 eapply semax_pre; [ | eassumption].
 rewrite <- insert_prop.
 forget ( PROPx P (LOCALx Q (SEPx R))) as PQR.
 go_lowerx. normalize. apply andp_right; auto.
 subst; apply prop_right; repeat split; auto.
 eapply semax_pre; [ | eassumption].
 rewrite <- insert_prop.
 forget ( PROPx P (LOCALx Q (SEPx R))) as PQR.
 go_lowerx. normalize. apply andp_right; auto.
 subst; apply prop_right; repeat split; auto.
Qed.

Definition logical_and_result v1 t1 v2 t2 :=
match (strict_bool_val t1 v1) with
| Some b1 => if b1 then match (strict_bool_val t2 v2) with
                            | Some b2 => if b2 then  Vint Int.one
                                         else Vint Int.zero
                            | None => Vundef end
                   else Vint Int.zero
| None => Vundef
end.

Definition logical_or_result v1 t1 v2 t2 :=
match (strict_bool_val t1 v1) with
| Some b1 => if b1 then Vint Int.one
                   else match (strict_bool_val t2 v2) with
                            | Some b2 => if b2 then  Vint Int.one
                                         else Vint Int.zero
                            | None => Vundef end
| None => Vundef
end.

(* NOTE: In both logical_or and logical_and,
  compcert (up to 2.4) has (Etempvar tid tbool)
  where I conjecture that it should have (Etempvar tid tint).
  That means our lemmas here are incompatible with
  compcert, at the moment.
*)

Definition logical_or tid e1 e2 :=
(Sifthenelse e1
             (Sset tid (Econst_int (Int.repr 1) tint))
             (Ssequence
                (Sset tid (Ecast e2 tbool))
                (Sset tid (Ecast (Etempvar tid tint (*tbool*)) tint)))).



Definition logical_and tid e1 e2 :=
(Sifthenelse e1
            (Ssequence
              (Sset tid (Ecast e2 tbool))
              (Sset tid (Ecast (Etempvar tid tint (*tbool*)) tint)))
            (Sset tid (Econst_int (Int.repr 0) tint))).

Lemma semax_pre_flipped :
 forall (P' : environ -> mpred) (Espec : OracleKind) {cs: compspecs}
         (Delta : tycontext) (P1 : list Prop) (P2 : list localdef)
         (P3 : list mpred) (c : statement)
         (R : ret_assert),
       semax Delta P' c R ->
       ENTAIL Delta, PROPx P1 (LOCALx P2 (SEPx P3)) |-- P' ->
        semax Delta (PROPx P1 (LOCALx P2 (SEPx P3))) c R.
Proof. intros.
eapply semax_pre. apply H0. auto.
Qed.

Lemma forward_setx':
  forall Espec {cs: compspecs} Delta P id e,
  (P |-- (tc_expr Delta e) && (tc_temp_id id (typeof e) Delta e) ) ->
  @semax cs Espec Delta
             P
             (Sset id e)
             (normal_ret_assert
                  (EX old:val,  local (`eq (eval_id id) (subst id (`old) (eval_expr e))) &&
                            subst id (`old) P)).
Proof.
intros.
eapply semax_pre; try apply (semax_set_forward Delta P id e).
+ eapply derives_trans ; [ | apply now_later].
   apply andp_left2; apply andp_right; auto.
Qed.

Lemma modulo_samerepr:
 forall x y, 
  Z.modulo x Int.modulus = Z.modulo y Int.modulus -> 
  Int.repr x = Int.repr y.
Proof.
intros.
apply Int.eqm_samerepr.
apply Zmod_divide_minus in H; [ | reflexivity].
unfold Int.eqm.
unfold Zbits.eqmod.
set (m := Int.modulus) in *.
destruct H as [z ?].
assert (x = y mod m + z * m) by omega.
clear H. subst x.
pose proof (Z.div_mod y m).
spec H. intro Hx; inv Hx.
evar (k: Z).
exists k.
rewrite H at 2; clear H.
rewrite (Z.mul_comm m).
assert (z * m = k*m + (y/m*m))%Z; [ | omega].
rewrite <- Z.mul_add_distr_r.
f_equal.
assert (k = z - y/m); [ | omega].
subst k.
reflexivity.
Qed.

Lemma select_switch_case_signed:
 forall y n x c sl,
 Z.modulo x Int.modulus = Z.modulo y Int.modulus ->
 0 <= x < Int.modulus ->
 select_switch_case n (LScons (Some x) c sl) = 
 if zeq (Int.unsigned (Int.repr y)) n then Some (LScons (Some x) c sl)
 else select_switch_case n sl.
Proof.
intros.
simpl.
apply modulo_samerepr in H.
rewrite <- H.
rewrite Int.unsigned_repr by rep_omega.
auto.
Qed.

Definition signof (e: expr) := 
  match typeof e with
  | Ctypes.Tint _ s _ => s
  | Ctypes.Tlong s _ => s 
  | _ =>  Unsigned
  end.

Definition adjust_for_sign (s: signedness) (x: Z) :=
 match s with
 | Unsigned => x 
 | Signed => if (zlt x Int.half_modulus) then x else x - Int.modulus 
 end.

Transparent tc_andp.  (* ? should leave it opaque, maybe? *)

(*

Lemma forward_setx_weak:
  forall Espec {cs: compspecs} Delta P Q R id e,
  (PROPx P (LOCALx Q (SEPx R)) |-- (tc_expr Delta e) && (tc_temp_id id (typeof e) Delta e) ) ->
  @semax cs Espec Delta
             (PROPx P (LOCALx Q (SEPx R)))
             (Sset id e)
             (normal_ret_assert
                  (EX old:val,
                    PROPx P
                     (LOCALx (`eq (eval_id id) (subst id (`old) (eval_expr e)) ::
                                     map (subst id (`old)) Q)
                      (SEPx R)))).
Proof.
 intros.
 eapply semax_post; [ | apply forward_setx'; auto].
 intros.
 autorewrite with ret_assert subst.
 repeat rewrite normal_ret_assert_eq.
 repeat rewrite exp_andp2. apply exp_derives; intro x.
  autorewrite with subst.
 go_lowerx. repeat apply andp_right; try apply prop_right; auto.
Qed.

Lemma semax_logical_or:
 forall Espec Delta P Q R tid e1 e2 b
   (CLOSQ : Forall (closed_wrt_vars (eq tid)) Q)
   (CLOSR : Forall (closed_wrt_vars (eq tid)) R)
   (CLOSE1 : closed_eval_expr tid e1 = true)
   (CLOSE2 : closed_eval_expr tid e2 = true),
 bool_type (typeof e1) = true ->
 bool_type (typeof e2) = true ->
 (temp_types Delta) ! tid = Some (tint, b) ->
  @semax Espec Delta (PROPx P (LOCALx ((tc_expr Delta e1)::
              (`or (`(typed_true (typeof e1)) (eval_expr Delta e1))  (tc_expr Delta e2))::
              tc_temp_id tid tbool Delta (Ecast e2 tbool) ::
   Q) (SEPx (R))))
    (logical_or tid e1 e2)
  (normal_ret_assert (PROPx P (LOCALx
((`eq (eval_id tid)
   (`logical_or_result
          `(typeof e1) (eval_expr Delta e1) `(typeof e2) (eval_expr Delta e2)))::Q) (SEPx (R))))).
Proof.
intros.
assert (CLOSE1' := closed_eval_expr_e Delta _ _ CLOSE1).
assert (CLOSE2' := closed_eval_expr_e Delta _ _ CLOSE2).
apply semax_ifthenelse_PQR.
  - auto.
  - rewrite <- insert_local; apply andp_left2.
    rewrite <- insert_local; apply andp_left1. auto.
  -  eapply semax_pre. apply derives_refl.
     eapply semax_post_flipped.
     apply forward_setx.
     go_lowerx. apply andp_right; apply prop_right.
    apply Coq.Init.Logic.I.   unfold tc_temp_id, typecheck_temp_id. rewrite H1.
     simpl. apply Coq.Init.Logic.I.
     intros ek vl.
    unfold normal_ret_assert. repeat rewrite exp_andp2.
     apply exp_left;  intro.
     autorewrite with subst.
  rewrite (closed_wrt_subst _ _ (tc_expr Delta e1)) by auto with closed.
  rewrite (closed_wrt_subst _ _ (tc_expr Delta e2)) by auto with closed.
   go_lowerx. subst. apply andp_right; auto. apply prop_right; split; auto.
   rewrite H6.
   unfold logical_or_result.
 destruct (typeof e1) as [ | | | [ | ] |  | | | | ], (eval_expr Delta e1 rho); inv H; inv H8; simpl;
   try rewrite H3; auto.
  - eapply semax_seq'.
      + eapply forward_setx_weak.
         go_lowerx.
         destruct H5. congruence.
         apply andp_right; apply prop_right; auto.
        unfold tc_expr. simpl. rewrite tc_andp_sound.
        simpl. super_unfold_lift. split. auto.
         destruct (typeof e2) as [ | | | [ | ] |  | | | | ] eqn:?;
                                        inv H0; try  apply Coq.Init.Logic.I.
      + simpl update_tycon. apply extract_exists_pre. intro oldval.
          rewrite (@closed_wrt_subst _ tid _ (eval_expr Delta (Ecast e2 tbool)))
    by (simpl; auto with closed).
    rewrite (closed_wrt_map_subst _ _ R) by auto.
   repeat rewrite map_cons.
   rewrite closed_wrt_subst by auto with closed.
   rewrite closed_wrt_subst by auto with closed.
    rewrite (closed_wrt_map_subst _ _ Q) by auto.
    unfold tc_temp_id.
   unfold typecheck_temp_id. rewrite H1.  simpl denote_tc_assert.
   autorewrite with subst.
   repeat apply andp_right; auto.
        eapply semax_post_flipped.
        eapply forward_setx.
        go_lowerx. apply andp_right; apply prop_right; auto.
        unfold tc_expr. simpl. rewrite tc_andp_sound.
        super_unfold_lift. split.
        erewrite temp_types_init_same by eauto. simpl. apply Coq.Init.Logic.I.
         apply Coq.Init.Logic.I.
        simpl. unfold tc_temp_id. unfold typecheck_temp_id.
        erewrite temp_types_init_same by eauto. rewrite tc_andp_sound.
        simpl. super_unfold_lift; auto.
        intros. unfold normal_ret_assert.
        repeat rewrite exp_andp2. apply exp_left; intro.
       simpl eval_expr.
       autorewrite with subst.
       go_lowerx. apply andp_right; auto. apply prop_right; split; auto.
       rewrite H6. rewrite H7.
        unfold logical_or_result. rewrite H8.
        subst ek vl. simpl in  H2.
       apply bool_cast. destruct H10. congruence.
      eapply expr_lemmas.typecheck_expr_sound.
      apply tc_environ_init in H2.
      apply tc_environ_init in H2.
      apply H2.
      apply H3.
Qed.

Lemma semax_logical_and:
 forall Espec Delta P Q R tid e1 e2 b
   (CLOSQ : Forall (closed_wrt_vars (eq tid)) Q)
   (CLOSR : Forall (closed_wrt_vars (eq tid)) R)
   (CLOSE1 : closed_eval_expr tid e1 = true)
   (CLOSE2 : closed_eval_expr tid e2 = true),
 bool_type (typeof e1) = true ->
 bool_type (typeof e2) = true ->
 (temp_types Delta) ! tid = Some (tint, b) ->
  @semax Espec Delta (PROPx P (LOCALx ((tc_expr Delta e1)::
    (`or (`(typed_false (typeof e1)) (eval_expr Delta e1))  (tc_expr Delta e2))::tc_temp_id tid tbool Delta (Ecast e2 tbool) ::
   Q) (SEPx (R))))
    (logical_and tid e1 e2)
  (normal_ret_assert (PROPx P (LOCALx
((`eq (eval_id tid)
   (`logical_and_result
          `(typeof e1) (eval_expr Delta e1) `(typeof e2) (eval_expr Delta e2)))::Q) (SEPx (R)))))
  .
Proof.
intros.
assert (CLOSE1' := closed_eval_expr_e Delta _ _ CLOSE1).
assert (CLOSE2' := closed_eval_expr_e Delta _ _ CLOSE2).
apply semax_ifthenelse_PQR.
  - auto.
  - rewrite <- insert_local; apply andp_left2.
    rewrite <- insert_local; apply andp_left1. auto.
  - eapply semax_seq'.
      + eapply forward_setx_weak.
         go_lowerx. apply andp_right; apply prop_right; auto.
        unfold tc_expr. simpl. rewrite tc_andp_sound.
        simpl. super_unfold_lift. split.
        destruct H5; auto; congruence.
        unfold isCastResultType. destruct (typeof e2) as [ | | | [ | ] |  | | | | ];
                                        inv H0; simpl; apply Coq.Init.Logic.I.
      + simpl update_tycon. apply extract_exists_pre. intro oldval.
          rewrite (@closed_wrt_subst _ tid _ (eval_expr Delta (Ecast e2 tbool)))
    by (simpl; auto with closed).
  autorewrite with subst.
    unfold tc_temp_id.
   unfold typecheck_temp_id. rewrite H1.  simpl denote_tc_assert.
   autorewrite with subst.
        eapply semax_post_flipped.
        eapply forward_setx.
        go_lowerx. apply andp_right; apply prop_right; auto.
        unfold tc_expr. simpl. rewrite tc_andp_sound.
        super_unfold_lift. split.
        erewrite temp_types_init_same by eauto. simpl. apply Coq.Init.Logic.I.
         apply Coq.Init.Logic.I.
        simpl. unfold tc_temp_id. unfold typecheck_temp_id.
        erewrite temp_types_init_same by eauto. rewrite tc_andp_sound.
        simpl. super_unfold_lift; auto.
        intros. unfold normal_ret_assert.
        repeat rewrite exp_andp2. apply exp_left; intro.
       simpl eval_expr.
       autorewrite with subst.
       go_lowerx. apply andp_right; auto. apply prop_right; split; auto.
       rewrite H6. rewrite H7.
        unfold logical_and_result.
        subst ek vl. simpl in  H2.
        rewrite H8.
       apply bool_cast.  destruct H10. congruence.
      eapply expr_lemmas.typecheck_expr_sound.
      apply tc_environ_init in H2.
      apply tc_environ_init in H2.
      apply H2. auto.
- eapply semax_pre. apply derives_refl.
     eapply semax_post_flipped.
     apply forward_setx.
     go_lowerx. apply andp_right; try apply prop_right; auto.
     apply Coq.Init.Logic.I.
     unfold tc_temp_id. unfold typecheck_temp_id. rewrite H1.
     simpl. apply Coq.Init.Logic.I.
     intros ek vl. unfold normal_ret_assert.
   repeat rewrite exp_andp2. apply exp_left; intro x.
   autorewrite with subst.
    go_lowerx. apply andp_right; auto.
  apply prop_right; split; auto.
     unfold logical_and_result. unfold typed_false in *.
    autorewrite with subst in H8. rewrite H8.
    apply H6.
Qed.

Lemma semax_logical_and_PQR:
  forall Espec Delta P Q R PQR tid e1 e2 b
   (CLOSQ : Forall (closed_wrt_vars (eq tid)) Q)
   (CLOSR : Forall (closed_wrt_vars (eq tid)) R)
   (CLOSE1 : closed_eval_expr tid e1 = true)
   (CLOSE2 : closed_eval_expr tid e2 = true),
 bool_type (typeof e1) = true ->
 bool_type (typeof e2) = true ->
 (temp_types Delta) ! tid = Some (tint, b) ->
   PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- local (tc_expr Delta e1) &&
         (local (`(typed_false (typeof e1)) (eval_expr Delta e1)) || local (tc_expr Delta e2)) && local (tc_temp_id tid tbool Delta (Ecast e2 tbool)) ->
  (normal_ret_assert (PROPx P (LOCALx ((`eq (eval_id tid) (`logical_and_result
          `(typeof e1) (eval_expr Delta e1) `(typeof e2) (eval_expr Delta e2)))::Q) (SEPx (R))))) |-- PQR ->
   @semax Espec Delta (PROPx P (LOCALx (Q) (SEPx (R))))
    (logical_and tid e1 e2) PQR.
Proof.
intros.
eapply semax_pre_flipped.
eapply semax_post_flipped.
eapply semax_logical_and; try eassumption.
intros.
specialize (H3 ek vl).
apply andp_left2. apply H3.
intro rho. specialize (H2 rho). normalize. normalize in H2.
apply andp_right; auto.
eapply derives_trans; [ apply H2 | ].
normalize. simpl. apply orp_left; normalize.
Qed.

Lemma semax_logical_or_PQR:
  forall Espec Delta P Q R PQR tid e1 e2 b
   (CLOSQ : Forall (closed_wrt_vars (eq tid)) Q)
   (CLOSR : Forall (closed_wrt_vars (eq tid)) R)
   (CLOSE1 : closed_eval_expr tid e1 = true)
   (CLOSE2 : closed_eval_expr tid e2 = true),
 bool_type (typeof e1) = true ->
 bool_type (typeof e2) = true ->
 (temp_types Delta) ! tid = Some (tint, b) ->
   PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- local (tc_expr Delta e1) &&
        (local (`(typed_true (typeof e1)) (eval_expr Delta e1)) || local (tc_expr Delta e2)) && local (tc_temp_id tid tbool Delta (Ecast e2 tbool)) ->
  (normal_ret_assert (PROPx P (LOCALx ((`eq (eval_id tid) (`logical_or_result
          `(typeof e1) (eval_expr Delta e1) `(typeof e2) (eval_expr Delta e2)))::Q) (SEPx (R))))) |-- PQR ->
   @semax Espec Delta (PROPx P (LOCALx (Q) (SEPx (R))))
    (logical_or tid e1 e2) PQR.
Proof.
intros.
eapply semax_pre_flipped.
eapply semax_post_flipped.
eapply semax_logical_or; try eassumption.
intros.
specialize (H3 ek vl).
apply andp_left2. apply H3.
intro rho. specialize (H2 rho). normalize. normalize in H2.
apply andp_right.
eapply derives_trans. apply H2.
normalize. simpl.
 apply orp_left;
normalize. normalize.
Qed.
*)