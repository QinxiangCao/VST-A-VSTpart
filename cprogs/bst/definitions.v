Require Import Lia.
Require Import FloydSeq.precise_lemmas.
Require Import FloydSeq.precise_proofauto.
Require Import FloydSeq.proofauto.
Require Import cprogs.bst.program.
Local Open Scope logic.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Notation "'IntRepr'" := (Int.repr).
Notation "'store_int' p x" :=
  (@data_at CompSpecs Tsh tint (Vint(IntRepr(x))) p)
  (x at level 0, p at level 0, at level 0).
Notation "'store_tree_cell' p k v q1 q2" :=
  (@data_at CompSpecs Tsh (Tstruct _tree noattr) (Vint(IntRepr(k)), (v, (q1, q2))) p)
  (k at level 0, v at level 0, q1 at level 0, q2 at level 0, p at level 0, at level 0).
Notation "'store_tree_cell_' p" :=
  (@data_at_ CompSpecs Tsh (Tstruct _tree noattr) p)
  (p at level 0, at level 0).
Notation "'store_tree_ptr' p q" :=
  (@data_at CompSpecs Tsh (tptr (Tstruct _tree noattr)) q p)
  (q at level 0, p at level 0, at level 0).
Notation "'store_void_ptr' p q" :=
  (@data_at CompSpecs Tsh (tptr Tvoid) q p)
  (q at level 0, p at level 0, at level 0).
Notation "'tc_val_ptr'" := (tc_val (tptr Tvoid)).

Ltac simpl_if :=
  repeat
    match goal with
    | |- context [?n <? ?m] =>
      match goal with
      | H: n < m |- _ => replace (n <? m) with true; [| symmetry; apply Zaux.Zlt_bool_true; lia]
      | H: m > n |- _ => replace (n <? m) with true; [| symmetry; apply Zaux.Zlt_bool_true; lia]
      | H: n >= m |- _ => replace (n <? m) with false; [| symmetry; apply Zaux.Zlt_bool_false; lia]
      | H: m >= n |- _ => replace (n <? m) with false; [| symmetry; apply Zaux.Zlt_bool_false; lia]
      | H: ~ n < m |- _ => replace (n <? m) with false; [| symmetry; apply Zaux.Zlt_bool_false; lia]
      | H: ~ m < n |- _ => replace (n <? m) with false; [| symmetry; apply Zaux.Zlt_bool_false; lia]
      end
    end.

Definition key := Z.

Inductive tree : Type :=
  | E : tree
  | T : tree -> key -> val -> tree -> tree.

Fixpoint lookup (x : key) (t : tree) : val :=
  match t with
  | E => nullval
  | T tl k v tr =>
      if x <? k
      then lookup x tl
      else if k <? x
              then lookup x tr
              else v
  end.

Fixpoint insert (x: key) (v: val) (t: tree) : tree :=
  match t with
  | E => T E x v E
  | T a y v' b => if x <? y then T (insert x v a) y v' b
                  else if y <? x then T a y v' (insert x v b)
                  else T a x v b
  end.

Fixpoint pushdown_left (a: tree) (bc: tree) : tree :=
  match bc with
  | E => a
  | T b y vy c => T (pushdown_left a b) y vy c
  end.

Fixpoint delete (x: key) (s: tree) : tree :=
  match s with
  | E => E
  | T a y v' b => if x <? y then T (delete x a) y v' b
                  else if y <? x then T a y v' (delete x b)
                  else pushdown_left a b
  end.

Fixpoint tree_rep (t : tree) (p : val) : mpred :=
  match t with
  | E => !!(p = nullval) && emp
  | T a x v b =>
      !!(Int.min_signed <= x <= Int.max_signed /\ tc_val (tptr Tvoid) v) &&
      EX pa:val, EX pb:val,
        store_tree_cell p x v pa pb *
        tree_rep a pa *
        tree_rep b pb
  end.

Definition treebox_rep (t: tree) (b: val) : mpred :=
  EX p: val, store_tree_ptr b p * tree_rep t p.

Lemma tree_rep_local_facts:
  forall t p,
    tree_rep t p |--
    !!(is_pointer_or_null p /\ (p = nullval <-> t = E)).
Proof.
  induction t; unfold tree_rep; fold tree_rep; intros; normalize.
  - apply prop_right; split; simpl; auto. tauto.
  - entailer!.
    split; intros.
    inv H2. inv H7.
    congruence.
Qed.

Hint Resolve tree_rep_local_facts: saturate_local.

Lemma tree_rep_valid_pointer:
  forall t p,
    tree_rep t p
    |-- valid_pointer p.
Proof.
  intros.
  destruct t; simpl; normalize; auto with valid_pointer.
Qed.

Hint Resolve tree_rep_valid_pointer: valid_pointer.

Lemma treebox_rep_local_facts:
  forall t b,
    treebox_rep t b
    |-- !! field_compatible (tptr (Tstruct _tree noattr)) [] b.
Proof.
  intros. unfold treebox_rep.
  Intros p. entailer!.
Qed.

Hint Resolve treebox_rep_local_facts: saturate_local.

Lemma tree_rep_nullval:
  forall t,
    tree_rep t nullval
    |-- !!(t = E).
Proof.
  intros.
  destruct t; [entailer! |].
  simpl tree_rep.
  Intros pa pb. entailer!.
Qed.

Hint Resolve tree_rep_nullval: saturate_local.

Lemma treebox_rep_E:
  forall b:val,
    store_tree_ptr b nullval
    |-- treebox_rep E b.
Proof.
  intros. unfold treebox_rep. Exists nullval.
  simpl. entailer!.
Qed.

Lemma tree_rep_is_not_null:
  forall t p,
    p <> nullval ->
    tree_rep t p |--
      EX k v tl tr (pl:val) (pr:val),
        !!((t = T tl k v tr) /\ (Int.min_signed <= k <= Int.max_signed) /\ tc_val (tptr Tvoid) v) &&
        store_tree_cell p k v pl pr *
        tree_rep tl pl *
        tree_rep tr pr.
Proof.
  intros. saturate_local.
  destruct t; simpl.
  - pose proof proj2 H0 eq_refl.
    subst; tauto.
  - Intros pa pb. Exists k v t1 t2 pa pb.
    entailer!.
Qed.

Lemma store_tree_rep:
  forall k v (pl:val) (pr:val) tl tr p,
    !!(Int.min_signed <= k <= Int.max_signed /\ tc_val (tptr Tvoid) v) &&
    store_tree_cell p k v pl pr *
    tree_rep tl pl *
    tree_rep tr pr
    |-- tree_rep (T tl k v tr) p.
Proof.
  intros.
  unfold tree_rep; fold tree_rep.
  entailer!.
  Exists pl pr.
  entailer!.
Qed.

Lemma treerep_treebox_rep:
  forall t p b,
    tree_rep t p * store_tree_ptr b p
    |-- treebox_rep t b.
Proof.
  intros. unfold treebox_rep.
  Exists p. entailer!.
Qed.

Lemma treebox_rep_leaf:
  forall n p b (v: val),
    is_pointer_or_null v ->
    Int.min_signed <= n <= Int.max_signed ->
    store_tree_cell p n v nullval nullval * store_tree_ptr b p
    |-- treebox_rep (T E n v E) b.
Proof.
  intros.
  unfold treebox_rep, tree_rep. Exists p nullval nullval. entailer!.
Qed.

Lemma bst_left_entail:
  forall (t1 t1' t2: tree) k (v p1 p2 p b: val),
    Int.min_signed <= k <= Int.max_signed ->
    is_pointer_or_null v ->
    store_tree_ptr b p *
    store_tree_cell p k v p1 p2 *
    tree_rep t1 p1 * tree_rep t2 p2
    |-- treebox_rep t1 (field_address (Tstruct _tree noattr) [StructField _left] p) *
        (treebox_rep t1'
          (field_address (Tstruct _tree noattr) [StructField _left] p) -*
          treebox_rep (T t1' k v t2) b).
Proof.
  intros.
  unfold_data_at (data_at _ _ _ p).
  rewrite (field_at_data_at _ _ [StructField _left]).
  unfold treebox_rep at 1. Exists p1. cancel.
  rewrite <- wand_sepcon_adjoint.
  clear p1.
  unfold treebox_rep.
  Exists p.
  simpl.
  Intros p1.
  Exists p1 p2.
  entailer!.
  unfold_data_at (data_at _ _ _ p).
  rewrite (field_at_data_at _ _ [StructField _left]).
  cancel.
Qed.

Lemma bst_right_entail:
  forall (t1 t2 t2': tree) k (v p1 p2 p b: val),
    Int.min_signed <= k <= Int.max_signed ->
    is_pointer_or_null v ->
    store_tree_ptr b p *
    store_tree_cell p k v p1 p2 *
    tree_rep t1 p1 * tree_rep t2 p2
    |-- treebox_rep t2 (field_address (Tstruct _tree noattr) [StructField _right] p) *
        (treebox_rep t2'
          (field_address (Tstruct _tree noattr) [StructField _right] p) -*
          treebox_rep (T t1 k v t2') b).
Proof.
  intros.
  unfold_data_at (data_at _ _ _ p).
  rewrite (field_at_data_at _ _ [StructField _right]).
  unfold treebox_rep at 1. Exists p2. cancel.
  rewrite <- wand_sepcon_adjoint.
  clear p2.
  unfold treebox_rep.
  Exists p.
  simpl.
  Intros p2.
  Exists p1 p2.
  entailer!.
  unfold_data_at (data_at _ _ _ p).
  rewrite (field_at_data_at _ _ [StructField _right]).
  cancel.
Qed.

Lemma tree_rep_sameloc_eq:
  forall p t1 t2,
    (tree_rep t1 p * TT) && (tree_rep t2 p * TT)
    |-- !! (t1 = t2).
Proof.
  intros.
  generalize dependent p.
  generalize dependent t2.
  induction t1; destruct t2; intros.
  - apply prop_right; auto.
  - unfold_once tree_rep; normalize.
    data_at_nullval_left.
  - unfold_once tree_rep; normalize.
    data_at_nullval_left.
  - do_on_both saturate_local.
    unfold_once tree_rep. Intros pa1 pb1 pa2 pb2.
    unfold_data_at_composite.
    do_on_both saturate_local.
    repeat rewrite <- sepcon_assoc.
    left_assoc_sepcon_TT_to_fold_right.
    subst_data_at_sameloc_eq.
    apply prop_right. congruence.
Qed.

Lemma treebox_rep_sameloc_eq:
  forall b t1 t2,
    (treebox_rep t1 b * TT) && (treebox_rep t2 b * TT)
    |-- !! (t1 = t2).
Proof.
  intros. unfold treebox_rep.
  Intros p1 p2.
  do_on_both saturate_local.
  repeat rewrite <- sepcon_assoc.
  left_assoc_sepcon_TT_to_fold_right.
  subst_data_at_sameloc_eq.
  simpl fold_right. apply tree_rep_sameloc_eq.
Qed.

Hint Resolve tree_rep_sameloc_eq: precise_rel.
Hint Resolve treebox_rep_sameloc_eq: precise_rel.

Lemma precise_tree_rep:
  forall t p,
    precise_pred (tree_rep t p).
Proof.
  intros t.
  induction t; intros.
  - unfold tree_rep.
    apply andp_prop_precise.
    apply precise_emp.
  - unfold_once tree_rep.
    apply andp_prop_precise.
    rewrite exp_uncurry. apply exp_precise.
    + intros. destruct_all.
      simpl fst; simpl snd.
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

Lemma precise_treebox_rep:
  forall t p,
    precise_pred (treebox_rep t p).
Proof.
  intros. unfold treebox_rep.
  apply exp_precise.
  - intros.
    do_on_both saturate_local.
    repeat rewrite <- sepcon_assoc.
    left_assoc_sepcon_TT_to_fold_right.
    subst_data_at_sameloc_eq.
    apply prop_right; auto.
  - intros. prove_precise_pred_sepcon.
    apply precise_tree_rep.
Qed.

Hint Resolve precise_tree_rep: precise_pred.
Hint Resolve precise_treebox_rep: precise_pred.
