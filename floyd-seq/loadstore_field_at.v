Require Import FloydSeq.base2.
Require Import FloydSeq.client_lemmas.
Require Import VST.floyd.nested_field_lemmas.
Require Import VST.floyd.efield_lemmas.
Require Import VST.floyd.mapsto_memory_block.
Require Import VST.floyd.reptype_lemmas.
Require Import VST.floyd.data_at_rec_lemmas.
Require Import VST.floyd.field_at.
Require Import FloydSeq.loadstore_mapsto.
Require Import Csplit.strongFacts.
Require Import Csplit.strong.
Require Import VST.floyd.seplog_tactics.


Import LiftNotation.
Local Open Scope logic.

Lemma is_neutral_cast_by_value: forall t t',
  is_neutral_cast t t' = true ->
  type_is_by_value t = true.
Proof.
  intros.
  destruct t, t'; try inversion H; simpl; auto.
Qed.

(********************************************

Max length gfs field_at load store:
  semax_max_path_field_load_nth_ram.
  semax_max_path_field_cast_load_nth_ram.
  semax_max_path_field_store_nth_ram.

********************************************)

Section LOADSTORE_FIELD_AT.

Context {cs: compspecs}.

Lemma self_ramify_trans: forall {A} `{SepLog A} (g m l: A), g |-- m * TT -> m |-- l * TT -> g |-- l * TT.
Proof.
  intros A ND SL ? ? ? ? ?.
  eapply derives_trans; [exact H |].
  eapply derives_trans; [apply sepcon_derives; [exact H0 | apply derives_refl] |].
  rewrite sepcon_assoc.
  apply sepcon_derives; auto.
Qed.

Lemma semax_load_nth_ram_field_at :
  forall {Espec: OracleKind}{cs: compspecs} n (Delta: tycontext) sh id P Q R e1 Pre
    t_id t_root gfs (p v_val: val) (v_reptype: reptype (nested_field_type t_root gfs)),
    typeof e1 = nested_field_type t_root gfs ->
    typeof_temp Delta id = Some t_id ->
    is_neutral_cast (nested_field_type t_root gfs) t_id = true ->
    type_is_volatile (nested_field_type t_root gfs) = false ->
    ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
       local (`(eq (field_address t_root gfs p)) (eval_lvalue e1)) ->
    nth_error R n = Some Pre ->
    readable_share sh ->
    Pre |-- field_at sh t_root gfs v_reptype p * TT ->
    JMeq v_reptype v_val ->
    ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
      (tc_lvalue Delta e1) && local (`(tc_val (nested_field_type t_root gfs) v_val)) ->
    @semax cs Espec Delta (|> PROPx P (LOCALx Q (SEPx R)))
      (Sset id e1)
      (normal_ret_assert
         (PROPx P
           (LOCALx (temp id v_val :: remove_localdef_temp id Q)
             (SEPx R)))).
Proof.
  intros.
  pose proof is_neutral_cast_by_value _ _ H1.
  eapply semax_load_nth_ram.
  1: eassumption.
  1: eassumption.
  1: rewrite H; assumption.
  1: eassumption.
  1: eassumption.
  1: eassumption.
  2: eassumption.
  eapply self_ramify_trans; [exact H6 |].
  eapply RAMIF_PLAIN.weak_ramif_spec.
  apply mapsto_field_at_ramify; auto.
  eapply JMeq_sym; exact H7.
Qed.

Lemma semax_cast_load_nth_ram_field_at :
  forall {Espec: OracleKind}{cs: compspecs} n (Delta: tycontext) sh id P Q R e1 Pre
    t_to t_root gfs (p v_val: val) (v_reptype: reptype (nested_field_type t_root gfs)),
    typeof e1 = nested_field_type t_root gfs ->
    type_is_by_value (nested_field_type t_root gfs) = true ->
    type_is_volatile (nested_field_type t_root gfs) = false ->
    typeof_temp Delta id = Some t_to ->
    ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
      local (`(eq (field_address t_root gfs p)) (eval_lvalue e1)) ->
    nth_error R n = Some Pre ->
     cast_pointer_to_bool (nested_field_type t_root gfs) t_to = false ->
    readable_share sh ->
    Pre |-- field_at sh t_root gfs v_reptype p * TT ->
    JMeq v_reptype v_val ->
    ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
     (tc_lvalue Delta e1) && local (`(tc_val t_to (eval_cast (nested_field_type t_root gfs) t_to v_val))) ->
    @semax cs Espec Delta (|> PROPx P (LOCALx Q (SEPx R)))
     (Sset id (Ecast e1 t_to))
     (normal_ret_assert
         (PROPx P
           (LOCALx (temp id (eval_cast (nested_field_type t_root gfs) t_to v_val) :: remove_localdef_temp id Q)
             (SEPx R)))).
Proof.
  intros.
  eapply semax_cast_load_nth_ram.
  1: eassumption.
  1: eassumption.
  1: eassumption.
  1: eassumption.
  1: eassumption.
  1: eassumption.
  2: eassumption.
  eapply self_ramify_trans; [exact H7 |].
  eapply RAMIF_PLAIN.weak_ramif_spec.
  apply mapsto_field_at_ramify; auto.
  eapply JMeq_sym; exact H8.
Qed.

Lemma lower_andp_lifted_val:
  forall (P Q: val->mpred) v,
  (`(P && Q) v) = (`P v && `Q v).
Proof. reflexivity. Qed.

Lemma remove_one_LOCAL_left: forall P Q0 Q R S,
  PROPx P (LOCALx Q R) |-- S -> PROPx P (LOCALx (Q0 :: Q) R) |-- S.
Proof.
  intros.
  simpl in H |- *.
  intro rho; specialize (H rho).
  unfold PROPx, LOCALx, SEPx in *.
  normalize.
  autorewrite with subst norm1 norm2; normalize.
  normalize in H.
  autorewrite with subst norm1 norm2 in H; normalize in H; normalize.
Qed.

Lemma semax_store_nth_ram_field_at:
  forall {Espec: OracleKind} {cs: compspecs} n Delta sh P Q R e1 e2 Pre Post
    t_root gfs (p v_val: val) (v_reptype: reptype (nested_field_type t_root gfs)),
    typeof e1 = nested_field_type t_root gfs ->
    type_is_by_value (nested_field_type t_root gfs) = true ->
    type_is_volatile (nested_field_type t_root gfs) = false ->
    ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
       local (`(eq (field_address t_root gfs p)) (eval_lvalue e1)) ->
    ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
       local (`(eq v_val) (eval_expr (Ecast e2 (nested_field_type t_root gfs)))) ->
    JMeq v_val v_reptype ->
    nth_error R n = Some Pre ->
    writable_share sh ->
    Pre |-- field_at_ sh t_root gfs p * (field_at sh t_root gfs v_reptype p -* Post) ->
    ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
     (tc_lvalue Delta e1) && (tc_expr Delta (Ecast e2 (nested_field_type t_root gfs))) ->
    semax Delta
     (|> PROPx P (LOCALx Q (SEPx R)))
     (Sassign e1 e2)
     (normal_ret_assert
        (PROPx P (LOCALx Q (SEPx (replace_nth n R Post))))).
Proof.
  intros.
  eapply semax_store_nth_ram.
  1: eassumption.
  1: eassumption.
  1: eassumption.
  1: eassumption.
  1: eassumption.
  2: eassumption.
  eapply RAMIF_PLAIN.trans; [exact H7 |].
  apply mapsto_field_at_ramify; auto.
  apply JMeq_sym; apply by_value_default_val; auto.
Qed.

(* TODO: delete it *)
Lemma semax_no_path_field_store_nth_ram:
  forall {Espec: OracleKind},
    forall n Delta sh P Q R (e1 e2 : expr) Pre Post
      (t_root: type) (gfs: list gfield)
      (a v : val) (v' : reptype (nested_field_type t_root gfs)),
      type_is_by_value (typeof e1) = true ->
      writable_share sh ->
      type_is_volatile (typeof e1) = false ->
      typeof e1 = nested_field_type t_root gfs ->
      JMeq v v' ->
      nth_error R n = Some Pre ->
      Pre |-- field_at_ sh t_root gfs a *
        (field_at sh t_root gfs v' a -* Post) ->
      ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
        local (`(eq (field_address t_root gfs a)) (eval_lvalue e1)) ->
      ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
        local (`(eq v) (eval_expr (Ecast e2 (typeof e1)))) ->
      ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |--
        (tc_lvalue Delta e1) && 
        (tc_expr Delta (Ecast e2 (typeof e1))) ->
      semax Delta (|>PROPx P (LOCALx Q (SEPx R))) 
        (Sassign e1 e2)
          (normal_ret_assert
            (PROPx P
              (LOCALx Q
                (SEPx
                  (replace_nth n R Post))))).
Proof.
  intros *. intros ByVal Wsh Volatile EqT JM GetR F Evale1 Evale2 Tc.
  rewrite EqT in ByVal.
  eapply semax_store_nth_ram with (p := (field_address t_root gfs a)).
  + exact EqT.
  + exact Evale1.
  + rewrite <- EqT. exact Evale2.
  + exact GetR.
  + exact Wsh.
  + eapply RAMIF_PLAIN.trans; [exact F |].
    apply mapsto_field_at_ramify; [auto | rewrite <- EqT; auto | | auto].
    apply JMeq_sym; apply by_value_default_val; auto.
  + rewrite <- EqT. exact Tc.
Qed.

End LOADSTORE_FIELD_AT.
