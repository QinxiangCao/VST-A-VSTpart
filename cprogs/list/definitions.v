Require Import Coq.Sorting.Permutation.
Require Import FloydSeq.precise_lemmas.
Require Import FloydSeq.precise_proofauto.
Require Import FloydSeq.proofauto.
Require Import Coq.Init.Datatypes.
Require Import Coq.micromega.Psatz.
Require Export SetsClass.SetsClass.
Require Import cprogs.list.program.
Local Open Scope logic.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Notation "'IntRepr'" := (Int.repr).
Notation "'store_int' p x" :=
  (@data_at CompSpecs Tsh tint (Vint(IntRepr(x))) p)
  (x at level 0, p at level 0, at level 0).
Notation "'store_list_ptr' p q" :=
  (@data_at CompSpecs Tsh (tptr (Tstruct _list noattr)) q p)
  (q at level 0, p at level 0, at level 0).
Notation "'store_list_ptr_' p" :=
  (@data_at_ CompSpecs Tsh (tptr (Tstruct _list noattr)) p)
  (p at level 0, at level 0).
Notation "'store_list_cell' p x y" :=
  (@data_at CompSpecs Tsh (Tstruct _list noattr) (Vint(IntRepr(x)), y) p)
  (x at level 0, y at level 0, p at level 0, at level 0).
Notation "'store_list_cell_' p" :=
  (@data_at_ CompSpecs Tsh (Tstruct _list noattr) p)
  (p at level 0, at level 0).
Notation "'store_queue' p q1 q2" :=
  (@data_at CompSpecs Tsh (Tstruct _queue noattr) (q1, q2) p)
  (q1 at level 0, q2 at level 0, p at level 0, at level 0).

Definition singleton (x: Z): list Z := x :: nil.

Fixpoint listrep (l: list Z) (x: val) : mpred :=
  match l with
  | nil => !!(x = nullval) && emp
  | h :: l0 =>
      EX y:val, store_list_cell x h y * listrep l0 y
  end.

Arguments listrep l x : simpl never.

Fixpoint lseg (l: list Z) (x y: val) : mpred :=
  match l with
  | nil => !! (x = y) && emp
  | h :: l0 =>
      EX y':val, store_list_cell x h y' * lseg l0 y' y
  end.

Arguments lseg l x y : simpl never.

Fixpoint lbseg (l: list Z) (x y: val) : mpred :=
  match l with
  | nil => !! (x = y) && emp
  | h :: l0 =>
      EX y':val, store_list_ptr x y' * store_int (field_address (Tstruct _list noattr) [StructField _head] y') h * lbseg l0 (field_address (Tstruct _list noattr) [StructField _tail] y') y
  end.

Arguments lbseg l x y : simpl never.

Definition qrep (l: list Z) (p: val): mpred :=
  EX (l1 l2: list Z) (q1 q2: val),
    !! (l1 ++ rev l2 = l) &&
    store_queue p q1 q2 * listrep l1 q1 * listrep l2 q2.

Arguments qrep l p : simpl never.

Lemma listrep_local_facts:
  forall l p,
     listrep l p
     |-- !! (is_pointer_or_null p).
Proof.
  intros.
  revert p; induction l; intros.
  + unfold listrep; entailer!.
  + unfold listrep; fold listrep.
    Intros y.
    sep_apply IHl.
    entailer!.
Qed.

Hint Resolve listrep_local_facts : saturate_local.

Lemma listrep_valid_pointer:
  forall contents p,
    listrep contents p |-- valid_pointer p.
Proof.
  destruct contents; unfold listrep; fold listrep; intros.
  + Intros.
    subst.
    auto with valid_pointer.
  + Intros y.
    auto with valid_pointer.
Qed.

Hint Resolve listrep_valid_pointer : valid_pointer.

Lemma listrep_null: forall contents,
  listrep contents nullval = !!(contents = nil) && emp.
Proof.
  destruct contents; unfold listrep; fold listrep.
  + apply pred_ext; entailer!.
  + apply pred_ext.
    - Intros y. entailer!. destruct H; contradiction.
    - Intros.
Qed.

Lemma listrep_is_null: forall l p,
  p = nullval ->
  listrep l p |-- !!(l = nil) && emp.
Proof.
  intros.
  destruct l.
  + entailer!.
    unfold listrep.
    entailer!.
  + subst p.
    unfold listrep; fold listrep.
    Intros y.
    entailer.
    destruct H; contradiction.
Qed.

Lemma listrep_isptr: forall l p,
  isptr p ->
  listrep l p
  |-- EX x l' q, !!(l = x :: l') &&
      store_list_cell p x q *
      listrep l' q.
Proof.
  intros.
  destruct l.
  + unfold listrep.
    entailer!.
  + unfold listrep at 1; fold listrep.
    Intros y.
    Exists z l y.
    entailer!.
Qed.

Lemma listrep_is_not_null: forall l p,
  p <> nullval ->
  listrep l p
  |-- EX x l' q, !!(l = x :: l') &&
      store_list_cell p x q *
      listrep l' q.
Proof.
  intros.
  destruct l.
  + unfold listrep.
    entailer!.
  + unfold listrep at 1; fold listrep.
    Intros y.
    Exists z l y.
    entailer!.
Qed.

Lemma listrep_is_not_null_no_expand: forall l p,
  p <> nullval ->
  listrep l p
  |-- EX x l', !!(l = x :: l') &&
      listrep l p.
Proof.
  intros.
  destruct l.
  + unfold listrep.
    entailer!.
  + Exists z l.
    entailer!.
Qed.

Lemma store_listrep: forall (x: Z) (l': list Z) (p q: val),
  store_list_cell p x q *
  listrep l' q
  |-- listrep (x :: l') p.
Proof.
  intros.
  unfold listrep at 2; fold listrep.
  Exists q.
  entailer!.
Qed.

Lemma lseg_listrep: forall l1 l2 p q,
  lseg l1 p q * listrep l2 q
  |-- listrep (l1 ++ l2) p.
Proof.
  intros.
  revert p; induction l1; intros.
  - unfold lseg.
    simpl app.
    entailer!.
  - unfold lseg; fold lseg.
    Intros y'.
    sep_apply IHl1.
    simpl app.
    unfold listrep at 2; fold listrep.
    Exists y'.
    entailer!.
Qed.

Lemma lseg_lseg: forall l1 l2 p q r,
  lseg l1 p q * lseg l2 q r
  |-- lseg (l1 ++ l2) p r.
Proof.
  intros.
  revert p; induction l1; intros.
  - unfold lseg.
    simpl app.
    entailer!.
  - unfold lseg; fold lseg.
    Intros y'.
    sep_apply IHl1.
    simpl app.
    unfold lseg at 2; fold lseg.
    Exists y'.
    entailer!.
Qed.

Lemma store_lseg: forall (x: Z) (l: list Z) (p q r: val),
  store_list_cell p x q *
  lseg l q r
  |-- lseg (x :: l) p r.
Proof.
  intros.
  unfold lseg at 2; fold lseg.
  Exists q.
  entailer!.
Qed.

Lemma lseg_store: forall (l: list Z) (x: Z) (p q r: val),
  lseg l p q *
  store_list_cell q x r
  |-- lseg (l ++ x :: nil) p r.
Proof.
  intros.
  assert (store_list_cell q x r |-- lseg (x :: nil) q r).
  {
    unfold lseg.
    Exists r.
    entailer!.
  }
  sep_apply H.
  sep_apply (lseg_lseg l (x :: nil)).
  entailer!.
Qed.

Lemma lseg_nullval_ending: forall (l: list Z) (p: val),
  lseg l p nullval |-- listrep l p.
Proof.
  intros.
  revert p; induction l; intros.
  + unfold lseg, listrep.
    entailer!.
  + unfold lseg; fold lseg.
    unfold listrep; fold listrep.
    Intros q.
    Exists q.
    sep_apply IHl.
    entailer!.
Qed.

Lemma lbseg_listrep: forall l1 l2 p q r,
  lbseg l1 p q * store_list_ptr q r * listrep l2 r
  |-- EX p', store_list_ptr p p' * listrep (l1 ++ l2) p'.
Proof.
  intros.
  change val in r.
  revert p; induction l1; intros.
  - unfold lbseg.
    simpl app.
    Exists r.
    entailer!.
  - unfold lbseg; fold lbseg.
    Intros y'.
    sep_apply IHl1.
    Intros y''.
    Exists y'.
    simpl app.
    unfold listrep at 2; fold listrep.
    Exists y''.
    change val in y''.
    entailer!.
    unfold_data_at (store_list_cell y' a y'').
    entailer!.
Qed.

Lemma lbseg_store: forall (l: list Z) (x: Z) (p q r: val),
  (field_at Tsh (Tstruct _list noattr) [StructField _head] (Vint (IntRepr x)) r *
   lbseg l p q * store_list_ptr q r)%logic
  |-- lbseg (l ++ [x]) p
        (field_address (Tstruct _list noattr) [StructField _tail] r).
Proof.
  intros.
  revert p; induction l; intros.
  + unfold lbseg; simpl.
    Exists r.
    entailer!.
  + simpl.
    unfold lbseg; fold lbseg.
    Intros y.
    Exists y.
    sep_apply (IHl (field_address (Tstruct _list noattr) [StructField _tail] y)).
    entailer!.
Qed.

Fixpoint max_aux (l: list Z) (default: Z): Z :=
  match l with
  | nil => default
  | h :: l0 => max_aux l0 (Z.max default h)
  end.

Definition max (l: list Z): Z := max_aux l 0.

Fixpoint all_nonneg (l: list Z): Prop :=
  match l with
  | nil => True
  | h :: l0 => 0 <= h <= Int.max_signed /\ all_nonneg l0
  end.

Lemma all_nonneg_app: forall l1 l2,
  all_nonneg (l1 ++ l2) <-> all_nonneg l1 /\ all_nonneg l2.
Proof.
  intros.
  induction l1; simpl.
  + tauto.
  + tauto.
Qed.

Fixpoint increasing_aux (l: list Z) (x: Z): Prop :=
  match l with
  | nil => True
  | y :: l0 => x <= y /\ increasing_aux l0 y
  end.

Definition increasing (l: list Z): Prop :=
  match l with
  | nil => True
  | x :: l0 => increasing_aux l0 x
  end.

Inductive merge_step:
  (list Z * list Z * list Z) -> (list Z * list Z * list Z) -> Prop :=
| merge_step_l: forall x1 x2 l1 l2 l3,
    x1 <= x2 ->
    merge_step (x1 :: l1, x2 :: l2, l3) (l1, x2 :: l2, l3 ++ [x1])
| merge_step_r: forall x1 x2 l1 l2 l3,
    x2 <= x1 ->
    merge_step (x1 :: l1, x2 :: l2, l3) (x1 :: l1, l2, l3 ++ [x2]).

Definition merge_steps l1 l2 l3 l1' l2' l3': Prop :=
  clos_refl_trans merge_step (l1, l2, l3) (l1', l2', l3').

Inductive merge_rel l1 l2: list Z -> Prop :=
| merge_l: forall l1' l3',
    merge_steps l1 l2 nil l1' nil l3' ->
    merge_rel l1 l2 (l3' ++ l1')
| merge_r: forall l2' l3',
    merge_steps l1 l2 nil nil l2' l3' ->
    merge_rel l1 l2 (l3' ++ l2').

Inductive split_rec:
  list Z -> list Z -> list Z -> list Z -> list Z -> Prop :=
| split_rec_rec:
    forall a l l1 l2 l1' l2',
      split_rec l l2 (a :: l1) l2' l1' ->
      split_rec (a :: l) l1 l2 l1' l2'
| split_rec_nil:
    forall l1 l2,
      split_rec nil l1 l2 l1 l2.

Definition split_rel l l1 l2: Prop :=
  split_rec l nil nil l1 l2.

Inductive merge_sort: list Z -> list Z -> Prop :=
| merge_sort_base: forall l l1,
    split_rel l l1 [] ->
    merge_sort l l1
| merge_sort_rec: forall l l1 l2 l1' l2' l',
    split_rel l l1 l2 ->
    l2 <> [] ->
    merge_sort l1 l1' ->
    merge_sort l2 l2' ->
    merge_rel l1' l2' l' ->
    merge_sort l l'.

Lemma increasing_app_cons: forall l1 x l2,
  increasing (l1 ++ [x]) ->
  increasing (x :: l2) ->
  increasing (l1 ++ x :: l2).
Proof.
  intros.
  simpl in H0.
  destruct l1 as [| a l1]; simpl in *.
  { tauto. }
  revert a H; induction l1; simpl; intros.
  + tauto.
  + split; [tauto |].
    apply IHl1.
    tauto.
Qed.

Lemma increasing_app_cons_inv1: forall l1 x l2,
  increasing (l1 ++ x :: l2) ->
  increasing (l1 ++ [x]).
Proof.
  intros.
  destruct l1 as [| a l1]; simpl in *.
  { tauto. }
  revert a H; induction l1; simpl; intros.
  + tauto.
  + split; [tauto |].
    apply IHl1.
    tauto.
Qed.

Lemma increasing_app_cons_inv2: forall l1 x l2,
  increasing (l1 ++ x :: l2) ->
  increasing (x :: l2).
Proof.
  intros.
  simpl.
  induction l1; simpl in *.
  + tauto.
  + apply IHl1.
    destruct l1; simpl in *; tauto.
Qed.

Lemma merge_step_increasing1: forall l1 l2 l3 l1' l2' l3',
  merge_step (l1, l2, l3) (l1', l2', l3') ->
  increasing (l3 ++ l1) ->
  increasing (l3 ++ l2) ->
  increasing (l3' ++ l1').
Proof.
  intros.
  inversion H; subst.
  + rewrite <- app_assoc.
    apply H0.
  + rewrite <- app_assoc.
    simpl.
    apply increasing_app_cons.
    - eapply increasing_app_cons_inv1.
      apply H1.
    - apply increasing_app_cons_inv2 in H0.
      simpl in H0.
      simpl.
      tauto.
Qed.

Lemma merge_step_increasing2: forall l1 l2 l3 l1' l2' l3',
  merge_step (l1, l2, l3) (l1', l2', l3') ->
  increasing (l3 ++ l1) ->
  increasing (l3 ++ l2) ->
  increasing (l3' ++ l2').
Proof.
  intros.
  inversion H; subst.
  + rewrite <- app_assoc.
    simpl.
    apply increasing_app_cons.
    - eapply increasing_app_cons_inv1.
      apply H0.
    - apply increasing_app_cons_inv2 in H1.
      simpl in H1.
      simpl.
      tauto.
  + rewrite <- app_assoc.
    apply H1.
Qed.

Lemma merge_step_perm: forall l1 l2 l3 l1' l2' l3',
  merge_step (l1, l2, l3) (l1', l2', l3') ->
  Permutation (l3 ++ l1 ++ l2) (l3' ++ l1' ++ l2').
Proof.
  intros.
  inversion H; subst.
  + rewrite <- !app_assoc.
    reflexivity.
  + rewrite <- !app_assoc.
    apply Permutation_app; [reflexivity |].
    rewrite Permutation_app_comm.
    simpl.
    apply perm_skip.
    rewrite Permutation_app_comm.
    reflexivity.
Qed.

Lemma merge_steps_increasing: forall l1 l2 l3 l1' l2' l3',
  merge_steps l1 l2 l3 l1' l2' l3' ->
  increasing (l3 ++ l1) /\ increasing (l3 ++ l2) ->
  increasing (l3' ++ l1') /\ increasing (l3' ++ l2') .
Proof.
  unfold merge_steps.
  intros.
  induction_1n H.
  + tauto.
  + pose proof merge_step_increasing1 _ _ _ _ _ _ H1.
    pose proof merge_step_increasing2 _ _ _ _ _ _ H1.
    tauto.
Qed.

Lemma merge_steps_perm: forall l1 l2 l3 l1' l2' l3',
  merge_steps l1 l2 l3 l1' l2' l3' ->
  Permutation (l3 ++ l1 ++ l2) (l3' ++ l1' ++ l2').
Proof.
  unfold merge_steps.
  intros.
  induction_1n H.
  + reflexivity.
  + pose proof merge_step_perm _ _ _ _ _ _ H0.
    rewrite H1.
    tauto.
Qed.

Lemma merge_rel_increasing: forall l1 l2 l,
  merge_rel l1 l2 l ->
  increasing l1 ->
  increasing l2 ->
  increasing l.
Proof.
  intros.
  inversion H; subst.
  + pose proof merge_steps_increasing _ _ _ _ _ _ H2.
    simpl in H3.
    tauto.
  + pose proof merge_steps_increasing _ _ _ _ _ _ H2.
    simpl in H3.
    tauto.
Qed.

Lemma merge_rel_perm: forall l1 l2 l,
  merge_rel l1 l2 l ->
  Permutation (l1 ++ l2) l.
Proof.
  intros.
  inversion H; subst.
  + pose proof merge_steps_perm _ _ _ _ _ _ H0.
    simpl in H1.
    rewrite app_nil_r in H1.
    tauto.
  + pose proof merge_steps_perm _ _ _ _ _ _ H0.
    simpl in H1.
    tauto.
Qed.

Lemma split_rec_perm: forall l l1 l2 l1' l2',
  split_rec l l1 l2 l1' l2' ->
  Permutation (l ++ l1 ++ l2) (l1' ++ l2').
Proof.
  intros.
  induction H.
  + rewrite (Permutation_app_comm l1' l2'), <- IHsplit_rec.
    rewrite !app_assoc.
    rewrite (Permutation_app_comm (l ++ l2)).
    simpl.
    apply perm_skip.
    rewrite !app_assoc.
    apply Permutation_app; [| reflexivity].
    apply Permutation_app_comm.
  + reflexivity.
Qed.

Lemma split_rel_perm: forall l l1 l2,
  split_rel l l1 l2 ->
  Permutation l (l1 ++ l2).
Proof.
  intros.
  apply split_rec_perm in H.
  rewrite !app_nil_r in H.
  tauto.
Qed.

Lemma split_rec_length: forall l l1 l2 l1' l2',
  split_rec l l1 l2 l1' l2' ->
  (length l1 = length l2 -> length l1' <= S (length l2'))%nat /\
  (S (length l1) = length l2 -> length l2' <= S (length l1'))%nat.
Proof.
  intros.
  induction H.
  + simpl in *; lia.
  + simpl; lia.
Qed.

Lemma merge_base_fact: forall l l',
  split_rel l l' nil ->
  (exists x, l = [x] /\ l' = [x]) \/
  (l = [] /\ l' = []).
Proof.
  intros.
  pose proof split_rec_length _ _ _ _ _ H.
  destruct H0 as [? _].
  specialize (H0 eq_refl).
  pose proof split_rec_perm _ _ _ _ _ H.
  rewrite !app_nil_r in H1.
  pose proof Permutation_length H1.
  unfold split_rel in H0.
  inversion H; subst; clear H.
  + inversion H3; subst; clear H3.
    - simpl in *; lia.
    - left; exists a; tauto.
  + right; tauto.
Qed.

Lemma merge_sort_increasing: forall l l',
  merge_sort l l' ->
  increasing l'.
Proof.
  intros.
  induction H.
  + apply merge_base_fact in H.
    destruct H as [ [x [? ?] ] | [? ?] ]; subst.
    - simpl; tauto.
    - simpl; tauto.
  + pose proof merge_rel_increasing _ _ _ H3.
    tauto.
Qed.

Lemma merge_sort_perm: forall l l',
  merge_sort l l' ->
  Permutation l l'.
Proof.
  intros.
  induction H.
  + apply merge_base_fact in H.
    destruct H as [ [x [? ?] ] | [? ?] ]; subst.
    - reflexivity.
    - reflexivity.
  + pose proof merge_rel_perm _ _ _ H3.
    pose proof split_rel_perm _ _ _ H.
    rewrite H5, IHmerge_sort1, IHmerge_sort2, H4.
    reflexivity.
Qed.

Lemma merge_steps_all_nonneg: forall l1 l2 l3 l1' l2' l3',
  merge_steps l1 l2 l3 l1' l2' l3' ->
  all_nonneg l1 ->
  all_nonneg l2 ->
  all_nonneg l3 ->
  all_nonneg l1' /\ all_nonneg l2' /\ all_nonneg l3'.
Proof.
  unfold merge_steps.
  intros.
  induction_1n H.
  + tauto.
  + inversion H3; subst.
    - rewrite all_nonneg_app in IHrt.
      simpl in *.
      tauto.
    - rewrite all_nonneg_app in IHrt.
      simpl in *.
      tauto.
Qed.      

Lemma merge_rel_all_nonneg: forall l1 l2 l,
  merge_rel l1 l2 l ->
  all_nonneg l1 ->
  all_nonneg l2 ->
  all_nonneg l.
Proof.
  intros.
  inversion H; subst.
  + pose proof merge_steps_all_nonneg _ _ _ _ _ _ H2.
    rewrite all_nonneg_app.
    simpl in H3.
    tauto.
  + pose proof merge_steps_all_nonneg _ _ _ _ _ _ H2.
    rewrite all_nonneg_app.
    simpl in H3.
    tauto.
Qed.

Lemma split_rec_all_nonneg: forall l l1 l2 l1' l2',
  split_rec l l1 l2 l1' l2' ->
  all_nonneg l ->
  all_nonneg l1 ->
  all_nonneg l2 ->
  all_nonneg l1' /\ all_nonneg l2'.
Proof.
  intros.
  induction H.
  + simpl in H0, IHsplit_rec.
    tauto.
  + tauto.
Qed.

Lemma split_rel_all_nonneg: forall l l1 l2,
  split_rel l l1 l2 ->
  all_nonneg l ->
  all_nonneg l1 /\ all_nonneg l2.
Proof.
  intros.
  unfold split_rel in H.
  pose proof split_rec_all_nonneg _ _ _ _ _ H.
  simpl in H1.
  tauto.
Qed.

Lemma merge_sort_all_nonneg: forall l l',
  merge_sort l l' ->
  all_nonneg l ->
  all_nonneg l'.
Proof.
  intros.
  induction H.
  + pose proof split_rel_all_nonneg _ _ _ H.
    tauto.
  + pose proof merge_rel_all_nonneg _ _ _ H4.
    pose proof split_rel_all_nonneg _ _ _ H.
    tauto.
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

Lemma all_nonneg_zlist_equiv_eq:
  forall l1 l2,
    all_nonneg l1 ->
    all_nonneg l2 ->
    zlist_equiv l1 l2 ->
    l1 = l2.
Proof.
  intros.
  induction H1; simpl.
  - auto.
  - simpl in H, H0. destruct_all.
    assert (x1 = x2) by prove_int_eq.
    rewrite H7.
    rewrite IHzlist_equiv; auto.
Qed.

Lemma listrep_sameloc_zlist_equiv:
  forall p l1 l2,
    (listrep l1 p * TT) && (listrep l2 p * TT)
    |-- !! zlist_equiv l1 l2.
Proof.
  intros.
  generalize dependent p.
  generalize dependent l2.
  induction l1; destruct l2; intros.
  - apply prop_right.
    apply zlist_equiv_nil.
  - unfold_once listrep; normalize.
    data_at_nullval_left.
  - unfold_once listrep; normalize.
    data_at_nullval_left.
  - unfold_once listrep.
    Intros y1 y2.
    unfold_data_at_composite.
    do_on_both saturate_local.
    left_assoc_sepcon_TT_to_fold_right.
    subst_data_at_sameloc_eq.
    apply prop_right; auto.
Qed.

Lemma listrep_sameloc_all_nonneg_eq:
  forall p l1 l2,
    all_nonneg l1 ->
    all_nonneg l2 ->
    (listrep l1 p * TT) && (listrep l2 p * TT)
    |-- !! (l1 = l2).
Proof.
  intros.
  assert_PROP (zlist_equiv l1 l2) by apply listrep_sameloc_zlist_equiv.
  apply prop_right. apply all_nonneg_zlist_equiv_eq; auto.
Qed.

Hint Resolve listrep_sameloc_zlist_equiv: precise_rel.
Hint Resolve listrep_sameloc_all_nonneg_eq: precise_rel1.

Lemma qrep_sameloc_zlist_equiv:
  forall p l1 l2,
    (qrep l1 p * TT) && (qrep l2 p * TT)
    |-- !! zlist_equiv l1 l2.
Proof.
  intros. unfold qrep.
  Intros l3 l4 q1 q2 l5 l6 q3 q4.
  unfold_data_at_composite.
  do_on_both saturate_local.
  left_assoc_sepcon_TT_to_fold_right.
  subst_data_at_sameloc_eq.
  subst l1 l2.
  apply prop_right.
  apply zlist_equiv_app; auto.
  apply zlist_equiv_rev; auto.
Qed.

Hint Resolve qrep_sameloc_zlist_equiv: precise_rel.

Ltac construct_rel v1 v2 ::= solve
  [ exact (zlist_equiv v1 v2)
  | exact (z_equiv v1 v2)
  ].

Lemma zlist_equiv_listrep_eq:
  forall l1 l2 p,
    zlist_equiv l1 l2 ->
    listrep l1 p = listrep l2 p.
Proof.
  intros. generalize dependent p.
  induction H; intros.
  - reflexivity.
  - unfold_once listrep.
    EX_eq_intro.
    rewrite_equiv_rels.
    rewrite IHzlist_equiv.
    reflexivity.
Qed.

Lemma zlist_equiv_qrep_eq:
  forall l1 l2 p,
    zlist_equiv l1 l2 ->
    qrep l1 p = qrep l2 p.
Proof.
  assert (
    forall l1 l2 p,
      zlist_equiv l1 l2 ->
      qrep l1 p |-- qrep l2 p
  ).
  { intros.
    unfold qrep. normalize.
    apply zlist_equiv_app_inv in H.
    destruct H as [? [? [? [? ?]]]]. subst.
    apply zlist_equiv_rev_inv in H1.
    destruct H1 as [? [? ?]]. subst.
    rewrite (zlist_equiv_listrep_eq _ _ _ H0).
    rewrite (zlist_equiv_listrep_eq _ _ _ H1).
    Exists x1 x3 q1 q2.
    entailer!. }
  intros. apply pred_ext; apply H; auto.
  apply zlist_equiv_symm; auto.
Qed.

Lemma zlist_equiv_split_rec_eq:
  forall l1 l2 l3 l4 l5 l6,
    zlist_equiv l1 l4 ->
    zlist_equiv l2 l5 ->
    zlist_equiv l3 l6 ->
    ( exists l l',
        split_rec l1 l2 l3 l l' ) ->
    exists l l',
      split_rec l4 l5 l6 l l'.
Proof.
  intros.
  generalize dependent l4.
  generalize dependent l5.
  generalize dependent l6.
  destruct H2 as [? [? ?]].
  induction H; intros.
  - inv H2.
    edestruct IHsplit_rec as [? [? ?]]; eauto.
    repeat econstructor; eassumption.
  - inv H. exists l5, l6.
    constructor.
Qed.

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
    | context [qrep ?l _] => find_zlist_equiv l
    end
  end.

Ltac rewrite_zlist_equiv :=
  match goal with
  | H: zlist_equiv _ _ |- _ =>
      rewrite (zlist_equiv_listrep_eq _ _ _ H)
  | H: zlist_equiv _ _ |- _ =>
      rewrite (zlist_equiv_qrep_eq _ _ _ H)
  end.

Ltac generate_equiv_rels ::= first
  [ generate_zlist_equiv
  | generate_int_eq
  ].

Ltac rewrite_equiv_rels ::= first
  [ rewrite_zlist_equiv
  | rewrite_z_equiv
  ].

Lemma precise_listrep:
  forall l p,
    precise_pred (listrep l p).
Proof.
  intros l.
  induction l; intro p.
  - unfold listrep.
    apply andp_prop_precise.
    apply precise_emp.
  - unfold_once listrep.
    apply exp_precise.
    + intros.
      unfold_data_at_composite.
      do_on_both saturate_local.
      left_assoc_sepcon_TT_to_fold_right.
      subst_data_at_sameloc_eq.
      apply prop_right; auto.
    + intros.
      unfold_data_at_composite.
      prove_precise_pred_sepcon.
Qed.

Hint Resolve precise_listrep: precise_pred.

Lemma rev_inj {A: Type}:
  forall (l1 l2: list A),
    rev l1 = rev l2 ->
    l1 = l2.
Proof.
  intros l1.
  induction l1; simpl; intros.
  - destruct l2; auto.
    simpl in H.
    destruct (rev l2); discriminate.
  - destruct l2; simpl in H.
    + destruct (rev l1); discriminate.
    + apply app_inj_tail in H. destruct H.
      apply IHl1 in H.
      congruence.
Qed.

Lemma app_inv_zlist_equiv:
  forall l1 l2 l3 l4,
    zlist_equiv l1 l3 ->
    l1 ++ l2 = l3 ++ l4 ->
    l1 = l3 /\ l2 = l4.
Proof.
  intros.
  generalize dependent l2.
  generalize dependent l4.
  induction H; simpl; intros.
  - tauto.
  - inv H1. apply IHzlist_equiv in H4.
    destruct H4. split; congruence.
Qed.

Lemma precise_qrep:
  forall l p,
    precise_pred (qrep l p).
Proof.
  intros. unfold qrep.
  repeat rewrite exp_uncurry.
  apply exp_precise.
  - intros. destruct_all.
    simpl fst. simpl snd. normalize.
    unfold_data_at_composite.
    do_on_both saturate_local.
    left_assoc_sepcon_TT_to_fold_right.
    subst_data_at_sameloc_eq.
    apply prop_right.
    apply app_inv_zlist_equiv in H.
    2: apply zlist_equiv_symm; auto.
    destruct H. apply rev_inj in H8.
    congruence.
  - intro. unfold_data_at_composite.
    normalize. apply andp_prop_precise.
    prove_precise_pred_sepcon.
Qed.

Hint Resolve precise_qrep: precise_pred.
