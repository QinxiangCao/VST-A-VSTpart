
Require Import VST.floyd.proofauto.
Require Import cprogs.mytest_prog.
Require Import cprogs.mytest_def.
Require Import FloydSeq.AClight.
Import AClightNotations.
Require Import CSplit.strong.

Instance CompSpecs : compspecs. make_compspecs prog. Defined. 
Definition Vprog : varspecs. mk_varspecs prog. Defined.


Definition f_is_leap_year_spec_annotation :=
  ANNOTATION_WITH  year : Z, ((
      PROP (Int.min_signed <= year <= Int.max_signed)
      LOCAL (temp _year (Vint (Int.repr year)))
      SEP ()),
  (
      PROP ()
      LOCAL (temp ret_temp (Val.of_bool (is_leap_year year)))
      SEP ())).

Definition f_is_leap_year_spec_complex :=
  ltac:(uncurry_funcspec f_is_leap_year_spec_annotation).

Definition f_is_leap_year_funsig: funsig :=
  (((_year, tint) :: nil), tint).

Definition is_leap_year_spec :=
  ltac:(make_funcspec _is_leap_year f_is_leap_year_funsig f_is_leap_year_spec_complex).

Definition Gprog : funspecs :=
  ltac:(with_library prog [is_leap_year_spec]).

Print semax.


Ltac forward_setx :=
  ensure_normal_ret_assert;
  (* hoist_later_in_pre; *)
 match goal with
 | |- semax ?Delta ((PROPx ?P (LOCALx ?Q (SEPx ?R)))) (Sset _ ?e) _ =>
        eapply semax_PTree_set;
        [ reflexivity
        | reflexivity
        | check_cast_assignment
        | solve_msubst_eval; simplify_casts; reflexivity
        | first [ quick_typecheck3
                | pre_entailer; try solve [entailer!]]
        ]
        end.

Lemma append_verif: 
  semax_body Vprog Gprog f_is_leap_year is_leap_year_spec.
Proof.
  leaf_function.
  floyd.forward.start_function.
  check_precondition.
  eapply  semax_seq'.
  {

    
    (* forward1 ((Sset _a
    (Ebinop Oadd (Etempvar _year tint) (Econst_int (Int.repr (Zpos xH)) tint)
       tint))). *)
    apply semax_derives.
    eapply semax_PTree_set.
        [ reflexivity
        | reflexivity
        | check_cast_assignment
        | solve_msubst_eval; simplify_casts; reflexivity
        | first [ quick_typecheck3
                | pre_entailer; try solve [entailer!]]
        ]

     forward_setx.

    clear_Delta_specs.

    no_loads_expr (Ebinop Oadd (Etempvar _year tint) (Econst_int (Int.repr (Zpos xH)) tint)
    tint) false.

    forward.ensure_normal_ret_assert.
    Locate hoist_later_in_pre.




  }
  [ forward1 c
  | fwd_result;
    Intros;
    abbreviate_semax;
    try fwd_skip ]

  Locate forward.
  forward.forward.



  forward_setx.
  Locate forward_setx.
  apply semax_derives.
  forward_setx.
  forward.
  admit.
  forward. admit.
  forward. admit.
  forward. admit.
  forward_if. admit.
  


