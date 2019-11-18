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

Lemma listrep_is_null: forall sh l p,
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

Lemma ecancel_nil_list: forall sh p,
  p = nullval ->
  emp |-- listrep sh nil p.
Proof.
  intros.
  subst; unfold listrep.
  entailer!.
Qed.

Lemma ecancel_head: forall sh (p q x: val) l,
  data_at sh t_struct_list (x, q) p * listrep sh l q |-- listrep sh (x :: l) p.
Proof.
  intros.
  unfold listrep at 2; fold listrep.
  Exists q.
  entailer!.
Qed.

Lemma listrep_unify: forall sh p l1 l2,
  l1 = l2 ->
  listrep sh l1 p |-- listrep sh l2 p.
Proof.
  intros.
  subst.
  auto.
Qed.

Ltac local_listrep_cancel :=
  idtac;
  match goal with
  | |- data_at ?sh t_struct_list ?v ?p * _ |--
       data_at ?sh t_struct_list _ ?p =>
         exact (ecancel_cell sh p v)
  | |- emp |-- listrep ?sh nil ?p =>
         refine (ecancel_nil_list sh p _); solve [auto]
  | |- listrep ?sh ?l ?p * _ |--
       listrep ?sh _ ?p =>
         exact (ecancel_list sh p l)
  | |- data_at ?sh t_struct_list (?x, ?q) ?p * _ |--
       listrep ?sh (_ :: ?l) ?p =>
         exact (ecancel_head sh p q x l)
  end.

Ltac local_listrep_attempt :=
  idtac;
  match goal with
  | |- data_at ?sh t_struct_list ?v ?p * _ |--
       data_at ?sh t_struct_list _ _ =>
         exact (ecancel_cell sh p v)
  | |- emp |-- listrep ?sh _ ?p =>
         refine (ecancel_nil_list sh p _); solve [auto]
  | |- listrep ?sh ?l ?p * _ |--
       listrep ?sh _ _ =>
         exact (ecancel_list sh p l)
  | |- data_at ?sh t_struct_list (?x, ?q) ?p * _ |--
       listrep ?sh _ _ =>
         refine (ecancel_head sh p q x _)
  end.

Ltac global_listrep_cancel :=
  idtac;
  match goal with
  | |- listrep ?sh ?l1 ?p |--
       listrep ?sh ?l2 _ =>
         refine (listrep_unify sh p l1 l2 _)
  end.

Ltac listrep_cancel :=
  eapply symbolic_cancel_setup;
  [ construct_fold_right_sepcon
  | construct_fold_right_sepcon
  | fold_abnormal_mpred
  | cbv iota beta delta [before_symbol_cancel];
    (*aggresive_syntactic_cancel
      local_listrep_attempt
      local_listrep_cancel; *)
    conservative_syntactic_cancel local_listrep_cancel;
    first [ simple apply syntactic_cancel_solve3
          | match goal with
            | |- fold_right_sepcon ?A |-- fold_right_sepcon ?B => rewrite <- (fold_left_sepconx_eq A), <- (fold_left_sepconx_eq B)
            end;
            unfold fold_left_sepconx; cbv iota beta;
            first
            [ simple apply derives_refl
            | global_listrep_cancel ] ]].

Ltac unify_for_already_lower :=
  idtac;
  match goal with
  | |- _ |--  andp (prop ?A) _ =>
        repeat
         match A with
         | context [ (?x = ?y) /\ _ ] => has_evar y; progress unify x y
         | (?x = ?y) => has_evar y; progress unify x y
         end
  | _ => idtac
  end.

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
  Intros;
  pre_process;
  match goal with
  | |- ENTAIL _, PROPx _ (LOCALx _ (SEPx _)) |-- _ =>
         repeat EExists; go_lower
  | |- @derives mpred _ _ (exp _) =>
         repeat EExists; unify_for_already_lower
  end;
  saturate_local;
  first [ apply andp_right; [apply prop_right | try listrep_cancel];
          [repeat split; auto | ..]
        | try listrep_cancel].

Goal forall sh (p q x r: val) l,
  r = nullval ->
  exists z w: val,
  data_at sh t_struct_list (x, q) p * listrep sh l q |--
  listrep sh (x :: l) w * listrep sh nil r * listrep sh nil z.
intros.
eexists.
eexists.

listrep_cancel.

Qed.

Goal forall sh (p q x r: val) l,
  r = nullval ->
  data_at sh t_struct_list (x, q) p * listrep sh l q |--
  EX z w: val,
  listrep sh (x :: l) w * listrep sh nil r * listrep sh nil z.
intros.
listrep_entailer.

Qed.
