Require Import VST.floyd.proofauto.
Require Import cprogs.min_prog.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

Require Import ZArith.
Require Import List.
Import ListNotations.
Open Scope Z.


Theorem fold_min_general:
  forall (al: list Z)(i: Z),
  In i (al) ->
  forall x, List.fold_right Z.min x al <= i.
Proof.
induction al; intros.
inversion H.
destruct H.
subst a.
simpl.
apply Z.le_min_l.
simpl. rewrite Z.le_min_r.
apply IHal.
apply H.
Qed.

Theorem fold_min:
  forall (al: list Z)(i: Z),
  In i (al) ->
  List.fold_right Z.min (hd 0 al) al <= i.
Proof.
intros.
apply fold_min_general.
apply H.
Qed.

Lemma Forall_fold_min:
  forall (f: Z -> Prop) (x: Z) (al: list Z),
    f x -> Forall f al -> f (fold_right Z.min x al).
Proof.
 intros.
 induction H0.
 simpl. auto.
 simpl.
 unfold Z.min at 1.
 destruct (Z.compare x0 (fold_right Z.min x l)) eqn:?; auto.
Qed.

Lemma fold_min_another:
  forall x al y,
    fold_right Z.min x (al ++ [y]) = Z.min (fold_right Z.min x al) y.
Proof.
 intros.
 revert x; induction al; simpl; intros.
 apply Z.min_comm.
 rewrite <- Z.min_assoc. f_equal.
 apply IHal.
Qed.

Lemma is_int_I32_Znth_map_Vint:
 forall i s al,
  0 <= i < Zlength al ->
  is_int I32 s (Znth i (map Vint al)).
Proof.
intros. rewrite Znth_map; auto.
Qed.
Hint Extern 3 (is_int I32 _ (Znth _ (map Vint _))) =>
  (apply  is_int_I32_Znth_map_Vint; rewrite ?Zlength_map; omega).