Require Import AClight.proofauto.
Require Import cprogs.reverse_prog.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.
Definition t_struct_list := Tstruct _list noattr.

Fixpoint listrep (sh: share)
            (contents: list val) (x: val) : mpred :=
 match contents with
 | h::hs =>
              EX y:val,
                data_at sh t_struct_list (h,y) x * listrep sh hs y
 | nil => !! (x = nullval) && emp
 end.

Arguments listrep sh contents x : simpl never.

Lemma listrep_local_facts:
  forall sh contents p,
     listrep sh contents p |--
     !! (is_pointer_or_null p /\ (p=nullval <-> contents=nil)).
Proof.
intros.
revert p; induction contents; unfold listrep; fold listrep; intros; normalize.
apply prop_right; split; simpl; auto. intuition.
entailer!.
split; intro. subst p. destruct H; contradiction. inv H2.
Qed.

Hint Resolve listrep_local_facts : saturate_local.

Lemma listrep_valid_pointer:
  forall sh contents p,
   sepalg.nonidentity sh ->
   listrep sh contents p |-- valid_pointer p.
Proof.
 destruct contents; unfold listrep; fold listrep; intros; normalize.
 auto with valid_pointer.
 apply sepcon_valid_pointer1.
 apply data_at_valid_ptr; auto. simpl;  computable.
Qed.

Hint Resolve listrep_valid_pointer : valid_pointer.

Lemma listrep_null: forall sh contents,
    listrep sh contents nullval = !! (contents=nil) && emp.
Proof.
destruct contents; unfold listrep; fold listrep.
normalize.
apply pred_ext.
Intros y. entailer. destruct H; contradiction.
Intros.
Qed.

Lemma is_pointer_or_null_not_null:
 forall x, is_pointer_or_null x -> x <> nullval -> isptr x.
Proof.
intros.
 destruct x; try contradiction. hnf in H; subst i. contradiction H0; reflexivity.
 apply I.
Qed.

Lemma listrep_q_null: forall sh l p,
  p = nullval ->
  listrep sh l p |-- !! (p = nullval /\ l = nil) && emp.
Proof.
  intros.
  saturate_local.
  assert (l = nil) by tauto.
  entailer!.
  unfold listrep.
  entailer!.
Qed.

Lemma listrep_isptr: forall sh l p,
  isptr p ->
  listrep sh l p |--
    EX x l' q, !! (l = x :: l') &&
      data_at sh t_struct_list (x, q) p *
      listrep sh l' q.
Proof.
  intros.
  saturate_local.
  destruct l; [pose proof proj2 H0 eq_refl; subst; tauto |].
  clear H0 PNp.
  Exists v l.
  unfold listrep at 1; fold listrep.
  Intros t; Exists t.
  entailer!.
Qed.

Lemma ecancel_cell: forall sh p xq,
  data_at sh t_struct_list xq p * emp |-- data_at sh t_struct_list xq p.
Proof.
  intros.
  rewrite sepcon_emp; auto.
Qed.

Lemma ecancel_list: forall sh p l,
  listrep sh l p * emp |-- listrep sh l p.
Proof.
  intros.
  rewrite sepcon_emp; auto.
Qed.

Lemma ecancel_head: forall sh (p q x: val) l,
  data_at sh t_struct_list (x, q) p * listrep sh l q |-- listrep sh (x :: l) p.
Proof.
  intros.
  unfold listrep at 2; fold listrep.
  Exists q.
  entailer!.
Qed.

Ltac local_listrep_cancel :=
  idtac;
  match goal with
  | |- data_at ?sh t_struct_list ?v ?p * _ |--
       data_at ?sh t_struct_list _ ?p =>
         exact (ecancel_cell sh p v)
  | |- listrep ?sh ?l ?p * _ |--
       listrep ?sh _ ?p =>
         exact (ecancel_list sh p l)
  | |- data_at ?sh t_struct_list (?x, ?q) ?p * _ |--
       listrep ?sh (_ :: ?l) ?p =>
         exact (ecancel_head sh p q x l)
  end.

Ltac listrep_cancel :=
  eapply symbolic_cancel_setup;
  [ construct_fold_right_sepcon
  | construct_fold_right_sepcon
  | fold_abnormal_mpred
  | cbv iota beta delta [before_symbol_cancel];
    eapply syntactic_cancel_spec3;
    advanced_syntactic_cancel local_listrep_cancel;
    cbv iota; cbv zeta beta;
    first [ simple apply syntactic_cancel_solve3
          | match goal with
            | |- fold_right_sepcon ?A |-- fold_right_sepcon ?B => rewrite <- (fold_left_sepconx_eq A), <- (fold_left_sepconx_eq B)
            end;
            unfold fold_left_sepconx; cbv iota beta ]].

Goal forall sh (p q x: val) l,
  data_at sh t_struct_list (x, q) p * listrep sh l q |-- listrep sh (x :: l) p.
intros.
listrep_cancel.
Qed.
