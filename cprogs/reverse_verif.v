(************************************************************)
(************************************************************)
(**                                                        **)
(**                                                        **)
(**      Definitions and tactics for decorated program.    **)
(**                                                        **)
(**                                                        **)
(************************************************************)
(************************************************************)


Require Import AClight.proofauto.
Require Import cprogs.reverse_prog.
Require Import cprogs.reverse_def.
Require Import cprogs.reverse_annot.

(************************************************************)
(************************************************************)
(**                                                        **)
(**                                                        **)
(**                       THE  PROOF                       **)
(**                                                        **)
(**                                                        **)
(************************************************************)
(************************************************************)

Lemma body_reverse: semax_body Vprog Gprog f_reverse reverse_spec.
Proof.
start_function f_reverse_hint.
verify.
+ listrep_entailer.
+ listrep_entailer.
+ listrep_entailer.
  subst; simpl. rewrite app_ass. auto.
+ listrep_entailer.
  subst l2; rewrite <- app_nil_end, rev_involutive. auto.
Qed.

Ltac listrep_cancel :=
  eapply symbolic_cancel_setup;
  [ construct_fold_right_sepcon
  | construct_fold_right_sepcon
  | fold_abnormal_mpred
  | cbv iota beta delta [before_symbol_cancel];
    aggresive_syntactic_cancel
      local_listrep_attempt
      local_listrep_cancel;
    first [ simple apply syntactic_cancel_solve3
          | match goal with
            | |- fold_right_sepcon ?A |-- fold_right_sepcon ?B => rewrite <- (fold_left_sepconx_eq A), <- (fold_left_sepconx_eq B)
            end;
            unfold fold_left_sepconx; cbv iota beta;
            first
            [ simple apply derives_refl
            | global_listrep_cancel ] ]].

Ltac pre_process :=
  let RHS := fresh "RHS" in 
  match goal with
  | |- _ |-- ?P => set (RHS := P)
  end;
  repeat
  match goal with
  | H: isptr ?p |- context [listrep ?sh ?l ?p] =>
         sep_apply (listrep_isptr sh l p);
         let x := fresh "x" in
         let ll := fresh "l" in
         let pp := fresh "p" in
         Intros x ll pp
  | H: ?p = nullval |- context [listrep ?sh ?l ?p] =>
         sep_apply (listrep_is_null sh l p);
         Intros
  | |- context [listrep ?sh ?l nullval] =>
         sep_apply (listrep_is_null sh l nullval);
         Intros
  end;
  subst RHS.

Ltac listrep_entailer :=
  pre_process;
  match goal with
  | |- ENTAIL _, PROPx _ (LOCALx _ (SEPx _)) |-- _ =>
         repeat EExists; go_lower
  | |- @derives mpred _ _ (exp _) =>
         repeat EExists
  end;
  saturate_local;
  first [ apply andp_right; [apply prop_right | try listrep_cancel];
          [repeat split; auto | ..]
        | try listrep_cancel].  


  

Lemma body_reverse_long: semax_body Vprog Gprog f_reverse reverse_spec.
Proof.
start_function f_reverse_hint.
forwardD.
forwardD.
forwardD.
forwardD.
{
  listrep_entailer.
}
{
  forwardD.
  forwardD.
  forwardD.
  forwardD.
  forwardD.
  {
    forwardD.
  }
  {
    forwardD.
  }
  forwardD.
  {
    Intros. listrep_entailer.
  }
  {
    forwardD.
    forwardD.
    forwardD.
    forwardD.
    forwardD.
    forwardD.
    forwardD.
    forwardD.
    listrep_entailer.
    subst; simpl. rewrite app_ass. auto.
  }
}
forwardD.
forwardD.
listrep_entailer.
subst l2.
rewrite <- app_nil_end, rev_involutive.
auto.
Qed.

