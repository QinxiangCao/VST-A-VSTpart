Require Import AClight.proofauto.
Require Import VFA.Maps.
Require Import VFA.SearchTree.
Require Import WandDemo.SearchTree_ext.
(* Require Import WandDemo.VST_lemmas. *)
(* Require Import WandDemo.spec_bst. *)
Require Import cprogs.bst_prog.
Require Import cprogs.bst_def.
Require Import cprogs.bst_annot.

(* Currently we don't support specification for external functions in C files. So we have to write specification here. *)

Definition mallocN_spec :=
 DECLARE _mallocN
  WITH n: Z
  PRE [ 1%positive OF tint]
     PROP (4 <= n <= Int.max_unsigned)
     LOCAL (temp 1%positive (Vint (Int.repr n)))
     SEP ()
  POST [ tptr tvoid ]
     EX v: val,
     PROP (malloc_compatible n v)
     LOCAL (temp ret_temp v)
     SEP (memory_block Tsh n v).

Definition freeN_spec :=
 DECLARE _freeN
  WITH p : val , n : Z
  PRE [ 1%positive OF tptr tvoid , 2%positive OF tint]
     (* we should also require natural_align_compatible (eval_id 1) *)
      PROP() LOCAL (temp 1%positive p; temp 2%positive (Vint (Int.repr n)))
      SEP (memory_block Tsh n p)
  POST [ tvoid ]
    PROP () LOCAL () SEP ().

Definition Gprog : funspecs :=
    ltac:(with_library prog [
    mallocN_spec; freeN_spec;
    insert_spec
  ]).

Lemma if_trueb: forall {A: Type} b (a1 a2: A), b = true -> (if b then a1 else a2) = a1.
Proof. intros; subst; auto. Qed.

Lemma if_falseb: forall {A: Type} b (a1 a2: A), b = false -> (if b then a1 else a2) = a2.
Proof. intros; subst; auto. Qed.

Ltac simpl_compb := first [ rewrite if_trueb by (apply NPeano.Nat.ltb_lt; rewrite Nat2Z.inj_lt; omega)
                          | rewrite if_falseb by (apply NPeano.Nat.ltb_nlt; rewrite Nat2Z.inj_lt; omega)].

Lemma concrete_post_to_abstart: forall x v t0 p0 m0,
  Abs val nullval t0 m0 ->
  SearchTree val t0 ->
  treebox_rep (insert x v t0) p0 |-- Mapbox_rep (t_update m0 x v) p0.
Proof.
  intros.
  rewrite !Mapbox_rep_unfold.
  Exists (insert x v t0).
  entailer!.
  split; [apply insert_relate | apply insert_SearchTree]; auto.
Qed.

Lemma body_insert: semax_body Vprog Gprog f_insert insert_spec.
Proof.
  start_function f_insert_hint.
  verify.
  { (* abstract assertion to concrete *)
    rewrite !Mapbox_rep_unfold.
    Intros t0. Exists t0.
    entailer!.
  }
  { (* initial loop invariant *)
    Exists p0 t0 (fun t: tree val => t). entailer!.
    apply emp_partial_treebox_rep_H.
  }
  { rewrite treebox_rep_tree_rep at 1. Intros q. Exists q. entailer!. }
  { rep_omega. }
  { Exists vret. subst q. entailer!. }
  { rewrite memory_block_data_at_ by auto. entailer!. }
  { (* return in null branch *)
    eapply derives_trans. 2 : { apply concrete_post_to_abstart; eauto. }
    rewrite tree_rep_treebox_rep. normalize.
    sep_apply (treebox_rep_leaf x q p v); auto.
    rewrite <- H3. apply treebox_rep_partial_treebox_rep.
  }
  { (* unfold treerep when q is not null *)
    destruct t; rewrite tree_rep_treebox_rep.
    { Intros. congruence. }
    Exists t1 k v0 t2. entailer!.
  }
  { (* preserved loop invariant case 1 *)
    Exists (field_address t_struct_tree [StructField _left] q) t1 (fun t1 => P (T t1 k v0 t2)).
    entailer!.
    - rewrite <- H3. simpl; simpl_compb; auto.
    - sep_apply (partial_treebox_rep_singleton_left t2 k v0 q p); auto.
      apply partial_treebox_rep_partial_treebox_rep.
  }
  { (* preserved loop invariant case 1 *)
    Exists (field_address t_struct_tree [StructField _right] q) t2 (fun t2 => P (T t1 k v0 t2)).
    entailer!.
    - rewrite <- H3. simpl; simpl_compb; simpl_compb; auto.
    - sep_apply (partial_treebox_rep_singleton_right t1 k v0 q p); auto.
      cancel; apply partial_treebox_rep_partial_treebox_rep.
  }
  { (* return in x=k branch *)
    eapply derives_trans. 2 : { apply concrete_post_to_abstart; eauto. }
    rewrite <- H3. simpl insert. simpl_compb; simpl_compb.
    sep_apply (treebox_rep_internal t1 k v t2 p q); auto.
    assert (x=k) by omega. subst x.
    apply treebox_rep_partial_treebox_rep.
  }
Qed.
