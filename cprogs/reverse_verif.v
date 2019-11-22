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
Ltac local_listrep_cancel' :=
  idtac;
  match goal with
  | |- listrep ?sh ?l ?p * _ |--
       listrep ?sh ?u ?p =>simpl
         
  end.

Lemma body_reverse: semax_body Vprog Gprog f_reverse reverse_spec.
Proof.
start_function f_reverse_hint.
verify.
+ listrep_entailer.         
+  listrep_entailer.
+ listrep_entailer.
  subst; simpl. rewrite app_ass. auto. 
+  listrep_entailer.  
 Intros;
  pre_process;
  match goal with
  | |- ENTAIL _, PROPx _ (LOCALx _ (SEPx _)) |-- _ =>
         repeat EExists; go_lower
  | |- @derives mpred _ _ _ =>
         repeat EExists; unify_for_already_lower
  end;
  saturate_local.
  first [ apply andp_right; [apply prop_right | try listrep_cancel];
          [repeat split; auto | ..]
        | try listrep_cancel].
eapply symbolic_cancel_setup.
  ++ construct_fold_right_sepcon.
  ++ construct_fold_right_sepcon.
  ++ fold_abnormal_mpred.
  ++ cbv iota beta delta [before_symbol_cancel].
    conservative_syntactic_cancel
      local_listrep_cancel.
  subst l2; rewrite <- app_nil_end, rev_involutive. auto. listrep_entailer. auto. 
Qed.
repeat
   progress
    (eapply advanced_cancel.syntactic_cancel_spec3;
      [ advanced_syntactic_cancel local_ctac | cbv iota; cbv beta zeta ])
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

