Require Import AClight.proofauto.
Require Import VFA.Maps.
Require Import VFA.SearchTree.
Require Import WandDemo.SearchTree_ext.
(* Require Import WandDemo.VST_lemmas. *)
(* Require Import WandDemo.spec_bst. *)
Require Import cprogs.bst_prog.
Require Import cprogs.bst_def.
Require Import cprogs.bst_annot.


Lemma if_trueb: forall {A: Type} b (a1 a2: A), b = true -> (if b then a1 else a2) = a1.
Proof. intros; subst; auto. Qed.

Lemma if_falseb: forall {A: Type} b (a1 a2: A), b = false -> (if b then a1 else a2) = a2.
Proof. intros; subst; auto. Qed.

Ltac simpl_compb := first [ rewrite if_trueb by (apply NPeano.Nat.ltb_lt; rewrite Nat2Z.inj_lt; omega)
                          | rewrite if_falseb by (apply NPeano.Nat.ltb_nlt; rewrite Nat2Z.inj_lt; omega)].

Lemma body_insert: semax_body Vprog Gprog f_insert insert_spec.
Proof.
  start_function f_insert_hint.
  forwardD.
  { (* abstract assertion to concrete *)
    rewrite !Mapbox_rep_unfold.
    Intros t0.
    entailer!. EExists. entailer!. ecancel.
  }
  forwardD.
  forwardD.
  { (* initial loop invariant *)
    Exists p0 t0 (fun t: tree val => t). entailer!.
    apply emp_partial_treebox_rep_H.
  }
  forwardD.
  forwardD.
  forwardD.
  forwardD.
  {
    rewrite treebox_rep_tree_rep at 1. Intros q. Exists q.
    entailer!.
  }
  forwardD.
  forwardD.
  forwardD.
  intro d.
  forward_call (sizeof t_struct_tree).
  forwardD.
  forwardD.
  
  
  apply insert_concrete_to_abstract; intros.
  abbreviate_semax.
  forward_loop (EX p: val, EX t: tree val, EX P: tree val -> tree val,
       PROP(P (insert x v t) = (insert x v t0))
       LOCAL(temp _p p; temp _x (Vint (Int.repr (Z.of_nat x)));   temp _value v)
       SEP(treebox_rep t p;  partial_treebox_rep P p0 p)).
  * (* Precondition *)
    Exists p0 t0 (fun t: tree val => t). entailer!.
    apply emp_partial_treebox_rep_H.
  * (* Loop body *)
    Intros p t P.
    rewrite treebox_rep_tree_rep at 1. Intros q.
    forward. (* q = * p; *)
    forward_if.
    + (* then clause *)
      subst q.
      forward_call (sizeof t_struct_tree).
        1: simpl; rep_omega.
      Intros q.
      rewrite memory_block_data_at_ by auto.
      forward. (* q->key=x; *)
      forward. (* q->value=value; *)
      forward. (* q->left=NULL; *)
      forward. (* q->right=NULL; *)
      assert_PROP (t = (@E _)) by entailer!.
      subst t. rewrite tree_rep_treebox_rep. normalize.
      forward. (* * p = q; *)
      forward. (* return; *)
      entailer!.  clear - H1 H0 H.
      sep_apply (treebox_rep_leaf x q p v); auto.
      rewrite <- H1. apply treebox_rep_partial_treebox_rep.
    + (* else clause *)
      destruct t; rewrite tree_rep_treebox_rep.
      { normalize. }
      Intros. clear H2.
      forward. (* y=q->key; *)
      forward_if; [ | forward_if ].
      - (* Inner if, then clause: x<k *)
        forward. (* p=&q->left *)
        Exists (field_address t_struct_tree [StructField _left] q) t1 (fun t1 => P (T t1 k v0 t2)).
        entailer!.
       ** rewrite <- H1.
          simpl; simpl_compb; auto.
       ** sep_apply (partial_treebox_rep_singleton_left t2 k v0 q p); auto.
          apply partial_treebox_rep_partial_treebox_rep.
      - (* Inner if, second branch:  k<x *)
        forward. (* p=&q->right *)
        Exists (field_address t_struct_tree [StructField _right] q) t2 (fun t2 => P (T t1 k v0 t2)).
        entailer!.
       ** rewrite <- H1.
          simpl; simpl_compb; simpl_compb; auto.
       ** sep_apply (partial_treebox_rep_singleton_right t1 k v0 q p); auto.
          cancel; apply partial_treebox_rep_partial_treebox_rep.
      - (* Inner if, third branch: x=k *)
        assert (x=k) by omega.
        subst x. clear H H2 H5.
        forward. (* q->value=value *)
        forward. (* return *)
        entailer!.
        rewrite <- H1.
        simpl insert. simpl_compb; simpl_compb.
        sep_apply (treebox_rep_internal t1 k v t2 p q); auto.
        apply treebox_rep_partial_treebox_rep.
Qed.
