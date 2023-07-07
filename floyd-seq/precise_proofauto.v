Require Import VST.msl.seplog.
Require Import VST.veric.mpred.
Require Import VST.veric.seplog.
Require Import VST.veric.lift.
Require Import VST.floyd.SeparationLogicFacts.
Require Import Csplit.model_lemmas.
Require Import Csplit.strong.
Require Import FloydSeq.precise_lemmas.
Require Import FloydSeq.proofauto.

Local Open Scope logic.

Ltac destruct_all :=
  repeat lazymatch goal with
  | x : _ * _ |- _ => destruct x
  | H : _ /\ _ |- _ => destruct H
  | H : (_, _) = (_, _) |- _ =>
      injection H; intros; clear H
  end.

Ltac prove_int_eq :=
  match goal with
  | |- _ = _ =>
    subst; solve
    [ reflexivity
    | apply repr_inj_signed; [rep_omega | rep_omega | auto using Vint_injective]
    | apply repr_inj_unsigned; [rep_omega | rep_omega | auto using Vint_injective]
    ]
  end.

Ltac precise_extract_prop :=
  lazymatch goal with
  | |- PROPx (_ :: _) (LOCALx _ (SEPx _)) |-- _ =>
    apply canon_extract_prop; intro
  end.

Ltac subst_local_sametemp :=
  repeat match goal with
  | |- (PROPx _ (LOCALx (temp ?x _ :: _) (SEPx _)) * TT) &&
       (PROPx _ (LOCALx (temp ?x _ :: _) (SEPx _)) * TT)
       |-- _ =>
    apply local_sametemp_eq;
    intros ->
  end.

Tactic Notation "do_on_both_canon" tactic3(tac) :=
  apply imp_andp_adjoint;
  apply wand_sepcon_adjoint;
  tac;
  apply wand_sepcon_adjoint;
  apply imp_andp_adjoint;
  try rewrite andp_comm;
  apply imp_andp_adjoint;
  apply wand_sepcon_adjoint;
  tac;
  apply wand_sepcon_adjoint;
  apply imp_andp_adjoint;
  try rewrite andp_comm.

Tactic Notation "do_on_both" tactic3(tac) :=
  apply imp_andp_adjoint;
  tac;
  apply imp_andp_adjoint;
  try rewrite andp_comm;
  apply imp_andp_adjoint;
  tac;
  apply imp_andp_adjoint;
  try rewrite andp_comm.

Ltac left_assoc_sepcon_to_list P acc :=
  match P with
  | ?P * ?x =>
      left_assoc_sepcon_to_list P (x :: acc)
  | _ => constr:(P :: acc)
  end.

Ltac left_assoc_sepcon_TT_to_fold_right :=
  repeat match goal with
  | |- context [?P * TT] =>
    let pl := left_assoc_sepcon_to_list P (@nil mpred) in
    replace (P * TT) with (fold_right sepcon TT pl) by
      (simpl fold_right; repeat rewrite sepcon_assoc; reflexivity)
  end.

Ltac unfold_data_at_composite :=
  repeat match goal with
  | |- context [@data_at ?cs ?sh (Tstruct ?id ?attr) ?v ?p] =>
    unfold_data_at (@data_at cs sh (Tstruct id attr) v p)
  | |- context [@data_at_ ?cs ?sh (Tstruct ?id ?attr) ?p] =>
    unfold_data_at (@data_at_ cs sh (Tstruct id attr) p)
  end;
  repeat rewrite field_at_data_at;
  simpl nested_field_type.

Ltac pull_first_data_at_sameloc_aux S1 S2 cnt :=
  lazymatch constr:(pair S1 S2) with
  | pair (@data_at ?cs ?sh ?t ?v1 ?p :: _) (@data_at ?cs ?sh ?t ?v2 ?p :: _) =>
      match cnt with
      | 0%nat => idtac
      | _ => let cnt := eval compute in (Z.of_nat cnt) in
          do_on_both (gather_SEP cnt)
      end
  | pair (_ :: ?S1') (_ :: ?S2') =>
      pull_first_data_at_sameloc_aux S1' S2' (S cnt)
  | _ => idtac
  end.

Tactic Notation "pull_first_data_at_sameloc" constr(S1) constr(S2) :=
  pull_first_data_at_sameloc_aux S1 S2 0%nat.

Ltac subst_data_at_sameloc_eq :=
  repeat lazymatch goal with
  | |- fold_right sepcon TT nil &&
       fold_right sepcon TT nil
       |-- _ => idtac
  | |- fold_right sepcon TT ?S1 &&
       fold_right sepcon TT ?S2
       |-- _ =>
    pull_first_data_at_sameloc S1 S2;
    match goal with
    | |- fold_right sepcon TT (_ :: _) &&
         fold_right sepcon TT (_ :: _)
         |-- _ =>
      eapply precise_extract_prop_from_sep;
      [ solve [eauto with precise_rel1 | eauto with precise_rel]
      | intro
      ]
    | |- fold_right sepcon TT (?s :: _) &&
         fold_right sepcon TT (?s :: _)
         |-- _ =>
      apply precise_ignore_same_sep
    | |- fold_right sepcon TT (data_at Tsh _ (Vint _) ?p :: _) &&
         fold_right sepcon TT (data_at Tsh _ (Vint _) ?p :: _)
         |-- _ =>
      let H := fresh "H" in
      apply data_at_tint_sameloc_eq; intro H;
      try match type of H with
      | z_equiv ?n1 ?n2 =>
          assert (n1 = n2) by prove_int_eq; subst n1
      end
    | |- fold_right sepcon TT (data_at Tsh (tptr _) _ ?p :: _) &&
         fold_right sepcon TT (data_at Tsh (tptr _) _ ?p :: _)
         |-- _ =>
      apply data_at_tptr_sameloc_eq;
      [intuition | intros ->]
    | _ => idtac
    end
  end.

Ltac generate_int_eq :=
  match goal with
  | H: z_equiv ?n1 ?n2 |- _ =>
      assert (n1 = n2) by prove_int_eq;
      clear H
  | H: Int.repr ?n1 = Int.repr ?n2 |- _ =>
      assert (n1 = n2) by prove_int_eq;
      clear H
  | H: Vint (Int.repr _) = Vint (Int.repr _) |- _ =>
      apply Vint_injective in H;
      generate_int_eq
  end.

(** extensible
    Ltac construct_rel ::= solve [ ... | ... | ... ]
 *)
Ltac construct_rel v1 v2 := exact (z_equiv v1 v2).

Ltac construct_R x1 x2 :=
  lazymatch constr:(pair x1 x2) with
  | pair (pair ?x1' ?v) (pair ?x2' ?v) =>
      apply and; [construct_R x1' x2' | exact (v = v)]
  | pair (pair ?x1' ?v1) (pair ?x2' ?v2) =>
      apply and; [construct_R x1' x2' | construct_rel v1 v2]
  | pair ?v ?v => exact (v = v)
  | pair ?v1 ?v2 => construct_rel v1 v2
  end.

Ltac rewrite_R P t1 t2 :=
  lazymatch P with
  | ?P' /\ ?R ?v1 ?v2 =>
      change (P' /\ R v1 v2)
        with (P' /\ R (snd t1) (snd t2));
      rewrite_R P' (fst t1) (fst t2)
  | ?R ?v1 ?v2 =>
      change (R v1 v2)
        with (R t1 t2)
  end.

Ltac construct_relation :=
  match goal with
  | |- ?P |-- !! ?Q =>
    lazymatch Q with
    | _ ?x ?x =>
        only [R]: exact eq;
        apply prop_right; reflexivity
    | _ ?x1 ?x2 =>
        match type of x1 with
        | unit => only [R]: exact (fun _ _ => True); apply prop_right; auto
        | _ =>
            assert (exists R0, (P |-- !! R0) /\ R0 = Q) as [? [? ?]];
            [ exists ltac:(construct_R x1 x2); split;
              [apply prop_right; subst; intuition |]
            | subst; auto
            ];
            let t1 := fresh "TUPLE" in
            let t2 := fresh "TUPLE" in
            set (t1 := x1);
            set (t2 := x2);
            match goal with
            | |- ?R = _ =>
                rewrite_R R t1 t2
            end;
            generalize t1, t2;
            intros ? ?; reflexivity
        end
    end
  end.

Ltac rewrite_z_equiv :=
  match goal with
  | H: z_equiv _ _ |- _ => rewrite (z_equiv_Vint_eq _ _ H)
  end.

(** extensible
    Ltac generate_equiv_rels ::= first [ ... | ... | ... ]
    Ltac rewrite_equiv_rels ::= first [ ... | ... | ... ] *)
Ltac generate_equiv_rels := generate_int_eq.
Ltac rewrite_equiv_rels := rewrite_z_equiv.

Ltac prove_precise_spec1a :=
  unfold precise_spec1a; intros;
  destruct_all;
  do_on_both_canon (repeat precise_extract_prop);
  unfold_data_at_composite;
  do_on_both_canon Intros;
  subst_local_sametemp;
  apply precise_rel_only_sep;
  simpl fold_right; repeat rewrite <- sepcon_assoc;
  do_on_both saturate_local;
  left_assoc_sepcon_TT_to_fold_right; subst;
  subst_data_at_sameloc_eq; subst;
  repeat (generate_equiv_rels; subst);
  construct_relation.

Ltac EX_eq_intro :=
  repeat match goal with
  | |- exp _ = exp _ =>
    f_equal; apply functional_extensionality; intro
  end.

Ltac prove_precise_spec1b :=
  unfold precise_spec1b; intros;
  destruct_all;
  simpl fst in *;
  simpl snd in *;
  EX_eq_intro;
  repeat generate_equiv_rels;
  repeat first
  [ match goal with
    | H: _ = _ |- _ => rewrite H
    end
  | rewrite_equiv_rels
  ];
  reflexivity.

Ltac prove_precise_pred_sepcon :=
  lazymatch goal with
  | |- precise_pred (_ * _) =>
    apply sepcon_precise; prove_precise_pred_sepcon
  | |- precise_pred (data_at Tsh _ _ _) =>
    apply precise_data_at_value_nonvolatile; reflexivity
  | |- precise_pred (data_at_ Tsh _ _) =>
    apply precise_data_at_value_nonvolatile; reflexivity
  | |- precise_pred emp => apply precise_emp
  | |- precise_pred _ => auto with precise_pred
  end.

Ltac prove_precise_spec2 :=
  unfold precise_spec2; intros;
  apply environ_precise;
  destruct_all;
  apply precise_sep_precise;
  simpl fold_right_sepcon;
  unfold_data_at_composite;
  prove_precise_pred_sepcon.

Ltac prove_precise_funspec :=
  apply precise_funspec_equiv;
  eapply (precise_funspec_intro _ ?[R]);
  [ prove_precise_spec1a
  | prove_precise_spec1b
  | prove_precise_spec1b
  | prove_precise_spec2
  ].

(** For user defined predicates *)
Ltac unfold_once ind := unfold ind; fold ind.

Ltac data_at_nullval_left :=
  entailer!;
  repeat match goal with
  | H: field_compatible _ _ nullval |- _ => inv H
  | H: isptr nullval |- _ => inv H
  end.
