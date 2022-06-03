
Require Import VST.floyd.proofauto.
Require Import cprogs.append_prog.
Require Import cprogs.append_def.
Require Import FloydSeq.AClight.
Import AClightNotations.

Instance CompSpecs : compspecs. make_compspecs prog. Defined. 
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition f_append_spec_annotation :=
  ANNOTATION_WITH  sh x y s1 s2, ((
       PROP(writable_share sh)
       LOCAL (temp _x x; temp _y y)
       SEP (listrep sh s1 x; listrep sh s2 y)),
  (
      EX r: val,
       PROP()
       LOCAL(temp ret_temp r)
       SEP (listrep sh (s1++s2) r))).

Definition f_append_spec_complex :=
  ltac:(uncurry_funcspec f_append_spec_annotation).

Definition f_append_funsig: funsig :=
  (((_x, (tptr (Tstruct _list noattr))) ::
    (_y, (tptr (Tstruct _list noattr))) :: nil),
   (tptr (Tstruct _list noattr))).

Definition append_spec :=
  ltac:(make_funcspec _append f_append_funsig f_append_spec_complex).


Definition Gprog : funspecs :=
  ltac:(with_library prog [append_spec]).

Locate start_function.
Locate forward_if_tac.

(* 
Tactic Notation "forward_if" constr(post) :=
  lazymatch type of post with
  | Prop =>
      match goal with
      | |- semax _ (PROPx (?P) ?Q) _ _ =>
      floyd.forward.forward_if_tac (PROPx (post :: P) Q)
      end
  | list Prop =>
      match goal with
      | |- semax _ (PROPx (?P) ?Q) _ _ =>
          let P' := eval cbv iota zeta beta delta [app] in (post ++ P) in
          floyd.forward.forward_if_tac (PROPx P' Q)
      end
  | localdef =>
      match goal with
      | |- semax _ (PROPx (?P) (LOCALx ?Q ?R)) _ _ =>
          let Q' := remove_LOCAL2 constr:(cons post nil) Q in
          floyd.forward.forward_if_tac (PROPx (P) (LOCALx (post :: Q') R))
      end
  | list localdef =>
      match goal with
      | |- semax _ (PROPx (?P) (LOCALx ?Q ?R)) _ _ =>
          let Q' := remove_LOCAL2 post Q in
          let Q'' := eval cbv iota zeta beta delta [app] in (post ++ Q') in
          floyd.forward.forward_if_tac (PROPx (P) (LOCALx Q'' R))
      end
  | _ => floyd.forward.forward_if_tac post
  end.

Tactic Notation "forward_if" constr(post) :=
  lazymatch type of post with
  | Prop =>
      match goal with
      | |- semax _ (PROPx (?P) ?Q) _ _ =>
          forward_if_tac (PROPx (post :: P) Q)
      end
  | list Prop =>
      match goal with
      | |- semax _ (PROPx (?P) ?Q) _ _ =>
          let P' := eval cbv iota zeta beta delta [app] in (post ++ P) in
          forward_if_tac (PROPx P' Q)
      end
  | localdef =>
      match goal with
      | |- semax _ (PROPx (?P) (LOCALx ?Q ?R)) _ _ =>
          let Q' := remove_LOCAL2 constr:(cons post nil) Q in
          forward_if_tac (PROPx (P) (LOCALx (post :: Q') R))
      end
  | list localdef =>
      match goal with
      | |- semax _ (PROPx (?P) (LOCALx ?Q ?R)) _ _ =>
          let Q' := remove_LOCAL2 post Q in
          let Q'' := eval cbv iota zeta beta delta [app] in (post ++ Q') in
          forward_if_tac (PROPx (P) (LOCALx Q'' R))
      end
  | _ => forward_if_tac post
  end. *)

Lemma append_verif: 
  semax_body Vprog Gprog f_append append_spec.
Proof.
  leaf_function.
  floyd.forward.start_function.
  forward_if.
  forward.
  admit.
  forward.
  

