Require Import FloydSeq.precise_lemmas.
Require Import FloydSeq.precise_proofauto.
Require Import FloydSeq.proofauto.
Require Import cprogs.dlist.program.
Local Open Scope logic.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Notation "'IntRepr'" := (Int.repr).
Notation "'store_int' p x" :=
  (@data_at CompSpecs Tsh tint (Vint(IntRepr(x))) p)
  (x at level 0, p at level 0, at level 0).
Notation "'store_list_cell' p x q1 q2" :=
  (@data_at CompSpecs Tsh (Tstruct _list noattr) (Vint(IntRepr(x)), (q1, q2)) p)
  (x at level 0, q1 at level 0, q2 at level 0, p at level 0, at level 0).
Notation "'store_list_cell_' p" :=
  (@data_at_ CompSpecs Tsh (Tstruct _list noattr) p)
  (p at level 0, at level 0).
Notation "'store_list_box' p q1 q2" :=
  (@data_at CompSpecs Tsh (Tstruct _listbox noattr) (q1, q2) p)
  (q1 at level 0, q2 at level 0, p at level 0, at level 0).

Definition singleton (x: Z): list Z := x :: nil.

Fixpoint listrep_pre (contents: list Z) (x t: val) : mpred :=
  match contents with
  | nil => !!(x = nullval) && emp
  | h::hs => EX y:val,
      store_list_cell x h y t *
      listrep_pre hs y x
  end.

Definition listrep (contents: list Z) (x: val): mpred :=
  listrep_pre contents x nullval.

Arguments listrep contents x : simpl never.

Fixpoint lseg_pre (contents: list Z) (x y t s: val): mpred :=
  match contents with
  | nil => !!(x = y) && !!(t = s) && emp
  | h::hs => EX u:val,
      store_list_cell x h u t *
      lseg_pre hs u y x s
  end.

Definition lseg (contents: list Z) (x y: val): mpred :=
  EX t:val, lseg_pre contents x y nullval t.

Arguments lseg contents x y : simpl never.

Definition lbrep (contents: list Z) (l: val): mpred :=
  EX p q: val,
    store_list_box l p q *
    lseg_pre contents p nullval nullval q.

Arguments lbrep contents l : simpl never.

Lemma listrep_pre_local_facts:
  forall contents p q,
    listrep_pre contents p q
    |-- !!(is_pointer_or_null p).
Proof.
  induction contents.
  - intros. unfold listrep_pre. entailer!.
  - intros. unfold listrep_pre; fold listrep_pre.
    Intros y. entailer!.
Qed.

Hint Resolve listrep_pre_local_facts : saturate_local.

Lemma lseg_pre_local_facts:
  forall contents x y t s,
    lseg_pre contents x y t s
    |-- !!((is_pointer_or_null y -> is_pointer_or_null x) /\
           (is_pointer_or_null t -> is_pointer_or_null s)).
Proof.
  induction contents.
  - intros. unfold lseg_pre. entailer!.
  - intros. unfold lseg_pre; fold lseg_pre.
    Intros u.
    sep_apply IHcontents.
    entailer!.
Qed.

Hint Resolve lseg_pre_local_facts : saturate_local.

Lemma lseg_pre_valid_pointer1:
  forall contents x s t,
    lseg_pre contents x nullval s t
    |-- valid_pointer x.
Proof.
  destruct contents; intros.
  + unfold lseg_pre; entailer!.
  + unfold lseg_pre; fold lseg_pre.
    Intros u.
    auto with valid_pointer.
Qed.

Hint Resolve lseg_pre_valid_pointer1 : valid_pointer.

Lemma listrep_pre_valid_pointer:
  forall contents p q,
    listrep_pre contents p q |-- valid_pointer p.
Proof.
  destruct contents; unfold listrep_pre; fold listrep_pre;
  intros; normalize.
  auto with valid_pointer.
  apply sepcon_valid_pointer1.
  apply data_at_valid_ptr; auto.
  simpl; computable.
Qed.

Hint Resolve listrep_pre_valid_pointer : valid_pointer.

Lemma listrep_valid_pointer:
  forall contents p,
    listrep contents p |-- valid_pointer p.
Proof.
  intros. unfold listrep.
  apply listrep_pre_valid_pointer.
Qed.

Hint Resolve listrep_valid_pointer : valid_pointer.

Lemma listrep_pre_null:
  forall contents t,
    listrep_pre contents nullval t = !!(contents = nil) && emp.
Proof.
  destruct contents; unfold listrep_pre; fold listrep_pre.
  normalize.
  intros. apply pred_ext.
  Intros y. entailer!. destruct H; contradiction.
  Intros.
Qed.

Lemma listrep_pre_is_null:
  forall l p t, p = nullval ->
  listrep_pre l p t
  |-- !!(p = nullval /\ l = nil) && emp.
Proof.
  intros.
  subst.
  destruct l.
  + unfold listrep_pre.
    entailer!.
  + unfold listrep_pre.
    fold listrep_pre.
    Intros y.
    entailer!.
    destruct H; tauto.
Qed.

Lemma listrep_pre_isptr:
  forall l p t, isptr p ->
    listrep_pre l p t
    |-- EX a l' (q:val), !!(l = a :: l') &&
      store_list_cell p a q t *
      listrep_pre l' q p.
Proof.
  intros.
  destruct l.
  - unfold listrep_pre.
    entailer!.
  - Exists z l.
    unfold listrep_pre; fold listrep_pre.
    Intros q; Exists q.
    entailer!.
Qed.

Lemma listrep_pre_is_not_null:
  forall l p t, p <> nullval ->
  listrep_pre l p t
  |-- EX x l' (q:val),
    !!(l = x :: l') &&
    store_list_cell p x q t *
    listrep_pre l' q p.
Proof.
  intros.
  intros.
  destruct l.
  - unfold listrep_pre.
    entailer!.
  - Exists z l.
    unfold listrep_pre; fold listrep_pre.
    Intros q; Exists q.
    entailer!.
Qed.

Lemma lseg_pre_null:
  forall contents t x y,
    lseg_pre contents nullval t x y |-- !!(contents = nil /\ t = nullval) && emp.
Proof.
  intros.
  destruct contents; unfold lseg_pre; fold lseg_pre.
  + entailer!.
  + Intros u.
    entailer!.
    destruct H; contradiction.
Qed.

Lemma lseg_pre_neq_head:
  forall contents t s x y,
    t <> s ->
    lseg_pre contents t s x y |--
    EX h l0 (u: val),
      !!(contents = h :: l0) &&
        store_list_cell t h u x *
        lseg_pre l0 u s t y.
Proof.
  intros.
  destruct contents; unfold lseg_pre; fold lseg_pre.
  + entailer!.
  + Intros u.
    Exists z contents u.
    entailer!.
Qed.

Lemma lseg_pre_neq_tail_aux:
  forall contents t s x y,
    contents = nil \/
    lseg_pre contents t s x y |--
    EX a l0 (u: val),
      !!(contents = l0 ++ [a]) &&
        lseg_pre l0 t y x u *
        store_list_cell y a s u.
Proof.
  induction contents; intros.
  + left; auto.
  + right.
    unfold lseg_pre; fold lseg_pre.
    Intros u.
    specialize (IHcontents u s t y).
    destruct IHcontents.
    - subst contents.
      unfold lseg_pre at 1.
      entailer!.
      Exists a (@nil Z) x.
      unfold lseg_pre.
      entailer!.
    - sep_apply H.
      Intros c lb v.
      Exists c (a :: lb) v.
      unfold lseg_pre; fold lseg_pre.
      Exists u.
      entailer!.
Qed.
  
Lemma lseg_pre_neq_tail:
  forall contents t s x y,
    t <> s ->
    lseg_pre contents t s x y |--
    EX a l0 (u: val),
      !!(contents = l0 ++ [a]) &&
        lseg_pre l0 t y x u *
        store_list_cell y a s u.
Proof.
  intros.
  destruct contents.
  + unfold lseg_pre.
    entailer!.
  + pose proof lseg_pre_neq_tail_aux (z :: contents) t s x y.
    destruct H0; [congruence |].
    tauto.
Qed.

Lemma singleton_lseg_pre:
  forall a x y z,
    store_list_cell x a y z
    |-- lseg_pre [a] x y z x .
Proof.
  intros. unfold lseg_pre. Exists y.
  entailer!.
Qed.

Lemma lseg_pre_listrep_pre:
  forall l p t s,
    lseg_pre l p nullval t s
    |-- listrep_pre l p t.
Proof.
  induction l.
  - intros. simpl. entailer!.
  - intros. simpl. Intros u. Exists u. entailer!.
Qed.

Lemma lseg_nullval_listrep:
  forall contents x,
    lseg contents x nullval
    |-- listrep contents x.
Proof.
  intros. unfold lseg. Intros t. apply lseg_pre_listrep_pre.
Qed.

Lemma lseg_pre_lseg_pre:
  forall l1 l2 x y z w u v,
    lseg_pre l1 x y w u * lseg_pre l2 y z u v
    |-- lseg_pre (l1 ++ l2) x z w v.
Proof.
  induction l1.
  - simpl. intros. entailer!.
  - simpl. intros.
    Intros u0. Exists u0.
    entailer!. entailer!.
Qed.

Lemma lseg_pre_listrep_pre_app:
  forall l1 l2 a b c d,
    lseg_pre l1 a b c d * listrep_pre l2 b d
    |-- listrep_pre (l1 ++ l2) a c.
Proof.
  induction l1.
  - intros. unfold lseg_pre. simpl. entailer!.
  - intros. unfold lseg_pre; fold lseg_pre.
    Intros u. simpl. Exists u. entailer!.
    apply IHl1.
Qed.

Lemma lseg_pre_local_facts_lemma:
  forall contents (a: Z) (u: val) v q p t,
    store_list_cell q a u v * lseg_pre contents u p q t
    |-- !!(is_pointer_or_null t).
Proof.
  simpl. induction contents; intros.
  - unfold lseg_pre. Intros. subst q. entailer!.
  - unfold lseg_pre; fold lseg_pre.
    Intros u0. sep_apply (IHcontents a u0 q u p t).
    entailer!.
Qed.

Lemma lseg_pre_store:
  forall l a x y z w u,
    lseg_pre l x y w u * store_list_cell y a z u
    |-- lseg_pre (l ++ [a]) x z w y.
Proof.
  intros.
  sep_apply singleton_lseg_pre.
  sep_apply (lseg_pre_lseg_pre l [a]).
  entailer!.
Qed.

Inductive zlist_equiv: list Z -> list Z -> Prop :=
| zlist_equiv_nil: zlist_equiv nil nil
| zlist_equiv_cons: forall x1 x2 l1 l2,
    z_equiv x1 x2 ->
    zlist_equiv l1 l2 ->
    zlist_equiv (x1 :: l1) (x2 :: l2).

Hint Constructors zlist_equiv: core.

Lemma zlist_equiv_refl:
  forall l, zlist_equiv l l.
Proof.
  intros. induction l; auto.
Qed.

Lemma zlist_equiv_symm:
  forall l1 l2,
    zlist_equiv l1 l2 -> zlist_equiv l2 l1.
Proof.
  intros. induction H; auto.
Qed.

Lemma zlist_equiv_trans:
  forall l1 l2 l3,
    zlist_equiv l1 l2 ->
    zlist_equiv l2 l3 ->
    zlist_equiv l1 l3.
Proof.
  intros.
  generalize dependent l3.
  induction H; auto.
  intros. inv H1.
  constructor; auto.
  eapply z_equiv_trans; eauto.
Qed.

Lemma zlist_equiv_app:
  forall l1 l2 l3 l4,
    zlist_equiv l1 l2 ->
    zlist_equiv l3 l4 ->
    zlist_equiv (l1 ++ l3) (l2 ++ l4).
Proof.
  intros.
  induction H; simpl; auto.
Qed.

Lemma zlist_equiv_rev:
  forall l1 l2,
    zlist_equiv l1 l2 ->
    zlist_equiv (rev l1) (rev l2).
Proof.
  intros.
  induction H; simpl.
  - auto.
  - apply zlist_equiv_app; auto.
Qed.

Lemma zlist_equiv_singleton:
  forall n1 n2,
    z_equiv n1 n2 ->
    zlist_equiv (singleton n1) (singleton n2).
Proof.
  intros. unfold singleton; auto.
Qed.

Lemma zlist_equiv_app_inv:
  forall l1 l2 l,
    zlist_equiv (l1 ++ l2) l ->
    exists l3 l4,
      l = l3 ++ l4 /\
      zlist_equiv l1 l3 /\
      zlist_equiv l2 l4.
Proof.
  intros l1.
  induction l1; simpl; intros.
  - exists [], l. intuition.
  - inv H. apply IHl1 in H4.
    destruct H4 as [? [? [? [? ?]]]].
    subst. exists (x2 :: x), x0.
    intuition.
Qed.

Lemma zlist_equiv_rev_inv:
  forall l1 l,
    zlist_equiv (rev l1) l ->
    exists l2,
      l = rev l2 /\
      zlist_equiv l1 l2.
Proof.
  intros l1.
  induction l1; simpl; intros.
  - inv H. exists []. intuition.
  - apply zlist_equiv_app_inv in H.
    destruct H as [? [? [? [? ?]]]].
    subst. inv H1. inv H5.
    apply IHl1 in H0. destruct H0 as [? [? ?]].
    subst. exists (x2 :: x0).
    intuition.
Qed.

Lemma listrep_pre_sameloc_zlist_equiv:
  forall p t l1 l2,
    is_pointer_or_null t ->
    (listrep_pre l1 p t * TT) && (listrep_pre l2 p t * TT)
    |-- !! zlist_equiv l1 l2.
Proof.
  intros.
  generalize dependent p.
  generalize dependent t.
  generalize dependent l2.
  induction l1; destruct l2; intros.
  - apply prop_right; auto.
  - unfold_once listrep_pre; normalize.
    data_at_nullval_left.
  - unfold_once listrep_pre; normalize.
    data_at_nullval_left.
  - do_on_both saturate_local.
    unfold_once listrep_pre. Intros y1 y2.
    unfold_data_at_composite.
    do_on_both saturate_local.
    repeat rewrite <- sepcon_assoc.
    left_assoc_sepcon_TT_to_fold_right.
    subst_data_at_sameloc_eq.
    apply prop_right; auto.
Qed.

Lemma listrep_sameloc_zlist_equiv:
  forall p l1 l2,
    (listrep l1 p * TT) && (listrep l2 p * TT)
    |-- !! zlist_equiv l1 l2.
Proof.
  intros. unfold listrep.
  apply listrep_pre_sameloc_zlist_equiv.
  auto.
Qed.

Hint Resolve listrep_sameloc_zlist_equiv: precise_rel.

Lemma lbrep_sameloc_zlist_equiv:
  forall p l1 l2,
    (lbrep l1 p * TT) && (lbrep l2 p * TT)
    |-- !! zlist_equiv l1 l2.
Proof.
  intros. unfold lbrep.
  Intros p1 q1 p2 q2.
  do_on_both saturate_local.
  apply derives_trans with (
    (store_list_box p p1 q1 * listrep_pre l1 p1 nullval * TT) &&
    (store_list_box p p2 q2 * listrep_pre l2 p2 nullval * TT)
  ).
  { apply andp_derives; entailer!;
    apply sepcon_derives; auto using lseg_pre_listrep_pre. }
  do_on_both saturate_local.
  unfold_data_at_composite.
  left_assoc_sepcon_TT_to_fold_right.
  subst_data_at_sameloc_eq.
  apply prop_right; auto.
Qed.

Hint Resolve lbrep_sameloc_zlist_equiv: precise_rel.

Lemma zlist_equiv_listrep_pre_eq:
  forall l1 l2 p t,
    zlist_equiv l1 l2 ->
    listrep_pre l1 p t = listrep_pre l2 p t.
Proof.
  intros.
  generalize dependent p.
  generalize dependent t.
  induction H; intros.
  - reflexivity.
  - unfold_once listrep_pre.
    EX_eq_intro.
    rewrite_equiv_rels.
    rewrite IHzlist_equiv.
    reflexivity.
Qed.

Lemma zlist_equiv_listrep_eq:
  forall l1 l2 p,
    zlist_equiv l1 l2 ->
    listrep l1 p = listrep l2 p.
Proof.
  intros. unfold listrep.
  apply zlist_equiv_listrep_pre_eq.
  auto.
Qed.

Lemma zlist_equiv_lseg_pre_eq:
  forall l1 l2 x y t s,
    zlist_equiv l1 l2 ->
    lseg_pre l1 x y t s = lseg_pre l2 x y t s.
Proof.
  intros.
  generalize dependent x.
  generalize dependent y.
  generalize dependent t.
  generalize dependent s.
  induction H; intros.
  - reflexivity.
  - unfold_once lseg_pre.
    EX_eq_intro.
    rewrite_equiv_rels.
    rewrite IHzlist_equiv.
    reflexivity.
Qed.

Lemma zlist_equiv_lbrep_eq:
  forall l1 l2 p,
    zlist_equiv l1 l2 ->
    lbrep l1 p = lbrep l2 p.
Proof.
  intros. unfold lbrep.
  EX_eq_intro. f_equal.
  apply zlist_equiv_lseg_pre_eq.
  auto.
Qed.

Ltac construct_rel v1 v2 ::= solve
  [ exact (zlist_equiv v1 v2)
  | exact (z_equiv v1 v2)
  ].

Ltac find_zlist_equiv_aux l :=
  match l with
  | rev ?l =>
      find_zlist_equiv_aux l;
      match goal with
      | H: zlist_equiv l _ |- _ =>
          pose proof zlist_equiv_rev _ _ H
      end
  | ?l1 ++ ?l2 =>
      find_zlist_equiv_aux l1;
      find_zlist_equiv_aux l2;
      match goal with
      | H1: zlist_equiv l1 _,
        H2: zlist_equiv l2 _ |- _ =>
          pose proof zlist_equiv_app _ _ _ _ H1 H2
      end
  | ?n :: ?l =>
      find_zlist_equiv_aux l;
      match goal with
      | H1: z_equiv n _,
        H2: zlist_equiv l _ |- _ =>
          pose proof zlist_equiv_cons _ _ _ _ H1 H2
      end
  | singleton ?n =>
      match goal with
      | H: z_equiv n _ |- _ =>
          pose proof zlist_equiv_singleton _ _ H
      end
  | _ => idtac
  end.

Ltac find_zlist_equiv l :=
  match goal with
  | H: zlist_equiv l _ |- _ => idtac
  | |- _ => find_zlist_equiv_aux l
  end.

Ltac generate_zlist_equiv :=
  match goal with
  | H1: zlist_equiv (_ :: ?l1) (_ :: ?l2) |- _ =>
      lazymatch goal with
      | H2: zlist_equiv l1 l2 |- _ => fail
      | |- _ => inversion H1; subst
      end
  | |- ?LHS = _ =>
    match LHS with
    | context [listrep ?l _] => find_zlist_equiv l
    | context [lbrep ?l _] => find_zlist_equiv l
    end
  end.

Ltac rewrite_zlist_equiv :=
  match goal with
  | H: zlist_equiv _ _ |- _ =>
      rewrite (zlist_equiv_listrep_eq _ _ _ H)
  | H: zlist_equiv _ _ |- _ =>
      rewrite (zlist_equiv_lbrep_eq _ _ _ H)
  end.

Ltac generate_equiv_rels ::= first
  [ generate_zlist_equiv
  | generate_int_eq
  ].

Ltac rewrite_equiv_rels ::= first
  [ rewrite_zlist_equiv
  | rewrite_z_equiv
  ].

Lemma precise_listrep_pre:
  forall l p t,
    precise_pred (listrep_pre l p t).
Proof.
  intros l.
  induction l; intros.
  - unfold listrep_pre.
    apply andp_prop_precise.
    apply precise_emp.
  - unfold_once listrep_pre.
    apply exp_precise.
    + intros.
      unfold_data_at_composite.
      do_on_both saturate_local.
      repeat rewrite <- sepcon_assoc.
      left_assoc_sepcon_TT_to_fold_right.
      subst_data_at_sameloc_eq.
      apply prop_right; auto.
    + intros.
      unfold_data_at_composite.
      prove_precise_pred_sepcon.
Qed.

Lemma precise_listrep:
  forall l p,
    precise_pred (listrep l p).
Proof.
  intros. unfold listrep.
  apply precise_listrep_pre.
Qed.

Hint Resolve precise_listrep: precise_pred.

Lemma precise_lseg_pre:
  forall l x y t s,
    is_pointer_or_null y ->
    precise_pred (lseg_pre l x y t s).
Proof.
  intros l.
  induction l; intros.
  - unfold lseg_pre. rewrite andp_assoc.
    apply andp_prop_precise.
    apply andp_prop_precise.
    apply precise_emp.
  - unfold_once lseg_pre.
    apply exp_precise.
    + intros.
      unfold_data_at_composite.
      do_on_both saturate_local.
      repeat rewrite <- sepcon_assoc.
      left_assoc_sepcon_TT_to_fold_right.
      subst_data_at_sameloc_eq.
      apply prop_right; auto.
    + intros.
      unfold_data_at_composite.
      prove_precise_pred_sepcon.
Qed.

Lemma precise_lbrep:
  forall l p,
    precise_pred (lbrep l p).
Proof.
  intros. unfold lbrep.
  repeat rewrite exp_uncurry.
  apply exp_precise.
  - intros. destruct_all.
    simpl fst in *. simpl snd in *.
    unfold_data_at_composite.
    do_on_both saturate_local.
    left_assoc_sepcon_TT_to_fold_right.
    subst_data_at_sameloc_eq.
    apply prop_right; auto.
  - intros.
    unfold_data_at_composite.
    prove_precise_pred_sepcon.
    apply precise_lseg_pre. auto.
Qed.

Hint Resolve precise_lbrep: precise_pred.
