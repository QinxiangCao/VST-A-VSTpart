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

Ltac pre :=
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
         sep_apply (listrep_q_null sh l p); [exact H |];
         Intros
  | |- context [listrep ?sh ?l nullval] =>
         sep_apply (listrep_q_null sh l nullval); [exact eq_refl |];
         Intros
  end;
  subst RHS.

Lemma body_reverse: semax_body Vprog Gprog f_reverse reverse_spec.
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
    forwardD.
    {
      pre.
      listrep_entailer.
    }
    forwardD.
  }
  {
    forwardD.
    forwardD.
    forwardD.
    forwardD.
    forwardD.
    forwardD.
    forwardD.
    intro. (** FIXME why need this. *)
    listrep_entailer.
    subst; simpl. rewrite app_ass. auto.
  }
}
forwardD.
forwardD.
forwardD.
forwardD.
forwardD.
pre.
match goal with
  | |- context [listrep ?sh ?l nullval] =>
         sep_apply (listrep_q_null sh l nullval)
end.
         Intros.

EExists.
apply andp_right; [apply prop_right | try listrep_cancel].
Abort.

