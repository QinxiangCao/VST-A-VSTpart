Require Import AClight.AClight.
Require Import VST.floyd.proofauto.
Require Import split.vst_ext.
Require Import split.defs.
Require Import split.rule.
Require Import split.strong.
Section Semantics.

Context {CS: compspecs} {Espec: OracleKind} (Delta: tycontext).

Definition split_atom_to_statement (x : (expr + atom_statement)):=
  match x with
  | inl e => (Clight.Sifthenelse e Clight.Sskip Clight.Sbreak)
  | inr s => to_Clight s
  end.


Fixpoint path_to_statement (p:path):  Clight.statement :=
  match p with
  | nil => Clight.Sskip
  | inl e :: p' => Clight.Ssequence 
              (Clight.Sifthenelse e Clight.Sskip Clight.Sbreak) 
              (path_to_statement p')
  | inr s :: p' => Clight.Ssequence
              (to_Clight s) (path_to_statement p')
  end.

Fixpoint path_to_statement'  (p:path):  Clight.statement :=
    fold_Ssequence (map split_atom_to_statement p).


Lemma path_to_statement_app: forall P Q l1 l2,
  SeparationLogicAsLogic.AuxDefs.semax Delta P (Clight.Ssequence (path_to_statement l1)
    (path_to_statement l2)) Q <->
    SeparationLogicAsLogic.AuxDefs.semax Delta P (path_to_statement (l1++l2)) Q.
Proof.
  intros. generalize dependent P.
  generalize dependent Q.
  induction l1.
  + simpl. intros;split;intros.
    - apply semax_skip_seq. apply H.
    - apply semax_skip_seq in H. apply H.
  + intros. destruct a; simpl in *.
    { split;intro.
      - apply seq_assoc in H.
        apply semax_seq_inv in H.
        destruct H as [Q0 [E1 E2]].
        eapply semax_seq. apply E1. apply IHl1. auto.
      - apply seq_assoc. apply semax_seq_inv in H.
        destruct H as [Q0 [E1 E2]].
        eapply semax_seq. apply E1. apply IHl1. auto.
    }
    {
      split;intro.
      - apply seq_assoc in H.
        apply semax_seq_inv in H.
        destruct H as [Q0 [E1 E2]].
        eapply semax_seq. apply E1. apply IHl1. auto.
      - apply seq_assoc. apply semax_seq_inv in H.
        destruct H as [Q0 [E1 E2]].
        eapply semax_seq. apply E1. apply IHl1. auto.
    }
Qed.

Lemma path_to_statement_app': forall P Q l1 l2,
  semax Delta P (Clight.Ssequence (path_to_statement l1)
    (path_to_statement l2)) Q <->
    semax Delta P (path_to_statement (l1++l2)) Q.
Proof.
  intros. split;intro.
  - apply semax_equiv. apply path_to_statement_app. apply semax_equiv. auto.
  - apply semax_equiv. apply path_to_statement_app. apply semax_equiv. auto.
Qed.

Lemma path_to_statement_app_aux: forall P Q l1 l2,
  semax_aux Delta P (Clight.Ssequence (path_to_statement l1)
    (path_to_statement l2)) Q <->
    semax_aux Delta P (path_to_statement (l1++l2)) Q.
Proof.
Admitted.

Inductive extract_exp_from_path (X:Type): 
  (X -> split_assert) -> (X -> split_assert) -> Prop :=
(* extract the first EX out from pre condition *)
| extract_exp_from_path_basic: forall (pre' post': X -> assert),
    extract_exp_from_path X
      (fun x:X => Basic_assert (exp pre') (post' x))
      (fun x:X => Basic_assert (pre' x) (post' x))
| extract_exp_from_path_given: forall Y (HY:Non_empty_Type Y) 
    (ass ass_extracted: Y -> X -> split_assert),
    (forall y:Y, extract_exp_from_path X
         (ass y) (ass_extracted y)) ->
    extract_exp_from_path X
      (fun x:X => (Given_assert Y HY (fun y:Y => ass y x)))
      (fun x:X => (Given_assert Y HY (fun y:Y => ass_extracted y x))).


Inductive path_to_semax : path_statement -> Prop :=
| path_to_semax_given: forall X (HX:Non_empty_Type X)
    (path_ass path_ass': X -> split_assert) path,
    extract_exp_from_path X path_ass path_ass' ->
    (forall x:X, path_to_semax (path_ass' x, path)) ->
    path_to_semax (Given_assert X HX path_ass', path)
| path_to_semax_basic: forall pre path post ,
    @semax CS Espec Delta pre (path_to_statement path)
    {| RA_normal := post;
       RA_break := FALSE;
       RA_continue := FALSE;
       RA_return := fun _ => FALSE|} ->
    path_to_semax (Basic_assert pre post, path)
| path_to_semax_binded: forall X (HX:Non_empty_Type X)  ass' path, 
    (forall x:X, path_to_semax (ass' x, path)) ->
    path_to_semax (Binded_assert X HX ass', path)
.

Inductive add_post_to_semax (post: assert):
  partial_path_statement -> Prop :=
| add_post_to_semax_basic: forall pre path,
    @semax_aux CS Espec Delta pre (path_to_statement path)
    {| RA_normal := post;
      RA_break := FALSE;
      RA_continue := FALSE;
      RA_return := fun _ => FALSE|} ->
      add_post_to_semax post (Basic_partial pre, path)
| add_post_to_semax_binded: forall X (HX:Non_empty_Type X)  pre' path,
    (forall x:X, add_post_to_semax post (pre' x, path)) ->
    add_post_to_semax post (Binded_partial X HX pre', path)
.

Inductive add_return_to_semax (post: option val -> assert):
  return_post_statement -> Prop :=
| add_return_to_semax_basic: forall pre path ret_val,
    @semax_aux CS Espec Delta pre (Clight.Ssequence 
        (path_to_statement path) (Clight.Sreturn ret_val))
    {| RA_normal := FALSE;
      RA_break := FALSE;
      RA_continue := FALSE;
      RA_return := post|} ->
      add_return_to_semax post (Basic_partial pre, path, ret_val)
| add_return_to_semax_binded: forall X(HX:Non_empty_Type X)  pre' path ret_val,
    (forall x:X, add_return_to_semax post (pre' x, path, ret_val)) ->
    add_return_to_semax post (Binded_partial X HX pre', path, ret_val)
.

Inductive add_pre_to_semax (pre: assert):
  partial_path_statement -> Prop :=
| add_pre_to_semax_basic: forall post path,
    @semax CS Espec Delta pre (path_to_statement path)
    {| RA_normal := post;
      RA_break := FALSE;
      RA_continue := FALSE;
      RA_return := fun _ => FALSE|} ->
    add_pre_to_semax pre (Basic_partial post, path)
| add_pre_to_semax_binded: forall X (HX:Non_empty_Type X) post' path,
    (forall x:X, add_pre_to_semax pre (post' x, path)) ->
    add_pre_to_semax pre (Binded_partial X (HX:Non_empty_Type X)  post', path)
.

Inductive atom_to_semax (pre:assert)  (post:assert) : path -> Prop :=
| atom_to_semax_intro: forall path,
    @semax_aux CS Espec Delta pre (path_to_statement path)
    {| RA_normal := post;
       RA_break := FALSE;
       RA_continue := FALSE;
       RA_return := fun _ => FALSE|} ->
    atom_to_semax pre post path.

Inductive atom_return_to_semax (pre:assert)  (post: option val -> assert) :
  path * option expr -> Prop :=
| atom_return_to_semax_intro: forall path ret_val,
    @semax_aux CS Espec Delta pre (Clight.Ssequence 
      (path_to_statement path) (Clight.Sreturn ret_val))
    {| RA_normal := FALSE;
        RA_break := FALSE;
        RA_continue := FALSE;
        RA_return := post|} ->
    atom_return_to_semax pre post (path, ret_val).



Definition split_Semax (P: assert) (Q: ret_assert) (res:split_result) :=
  Forall (add_pre_to_semax P) (pre res)
  /\ Forall path_to_semax (paths res)
  /\ Forall (add_post_to_semax (RA_normal Q)) (normal_post res)
  /\ Forall (add_post_to_semax (RA_break Q)) (break_post res)
  /\ Forall (add_post_to_semax (RA_continue Q)) (continue_post res)
  /\ Forall (add_return_to_semax (RA_return Q)) (return_post res)
  /\ Forall (atom_to_semax P (RA_normal Q)) (normal_atom res)
  /\ Forall (atom_to_semax P (RA_break Q)) (break_atom res)
  /\ Forall (atom_to_semax P (RA_continue Q)) (continue_atom res)
  /\ Forall (atom_return_to_semax P (RA_return Q)) (return_atom res).

Lemma add_pre_to_semax_inv: forall X (HX:Non_empty_Type X)  P pre0 pre',
  Forall (add_pre_to_semax P) pre0 ->
  bind_partial_add X HX pre0 pre' ->
  forall x, Forall (add_pre_to_semax P) (pre' x).
Proof.
  intros.
  induction H0.
  - constructor.
  - inv H. constructor.
    * inv H3. apply inj_pair2 in H2;subst. auto.
    * apply IHbind_partial_add. auto.
Qed.

Lemma add_post_to_semax_inv: forall X (HX:Non_empty_Type X)  Q post post',
  Forall (add_post_to_semax Q) post ->
  bind_partial_add X HX post post' ->
  forall x, Forall (add_post_to_semax Q) (post' x).
Proof.
  intros.
  induction H0.
    - constructor.
    - inv H. constructor.
      * inv H3. apply inj_pair2 in H2;subst. auto.
      * apply IHbind_partial_add. auto.
Qed.

Lemma add_return_to_semax_inv: forall X (HX:Non_empty_Type X) Q post post',
  Forall (add_return_to_semax Q) post ->
  bind_return_add X HX post post' ->
  forall x, Forall (add_return_to_semax Q) (post' x).
Proof.
  intros.
  induction H0.
    - constructor.
    - inv H. constructor.
      * inv H3. apply inj_pair2 in H2;subst. auto.
      * apply IHbind_return_add. auto.
Qed.

Lemma path_to_semax_inv: forall X (HX:Non_empty_Type X) path path',
  Forall path_to_semax path ->
  bind_path_add X HX path path' ->
  forall x, Forall path_to_semax (path' x).
Proof.
  intros.
  induction H0.
  - constructor.
  - inv H. constructor.
    * inv H3. apply inj_pair2 in H2;subst. auto.
    * apply IHbind_path_add. auto.
Qed.

Lemma bind_result_add_inv: forall X (HX:Non_empty_Type X)  P Q res res',
  split_Semax P Q res ->
  bind_result_add X HX res res' -> 
  forall x:X, split_Semax P Q (res' x).
Proof.
  intros.
  inv H0.
  destruct H as [? [? [? [? [? [? [? [? [? ?]]]]]]]]];simpl in *.
  repeat split;simpl;auto.
  + eapply add_pre_to_semax_inv with (HX:=HX). apply H. auto. 
  + eapply path_to_semax_inv with (HX:=HX). apply H0. auto.
  + eapply add_post_to_semax_inv  with (HX:=HX). apply H7. auto. 
  + eapply add_post_to_semax_inv with (HX:=HX). apply H8. auto. 
  + eapply add_post_to_semax_inv with (HX:=HX). apply H9. auto. 
  + eapply add_return_to_semax_inv with (HX:=HX). apply H10. auto.
Qed.

Lemma add_pre_to_semax_derives: forall P Q (x:partial_path_statement),
  ENTAIL Delta, ((allp_fun_id Delta) && Q) |-- |==> |> FF || P ->
  add_pre_to_semax P x ->
  add_pre_to_semax Q x.
Proof.
  intros. destruct x as [post path].
  induction H0.
  + constructor.
    eapply semax_conseq with (P':=P)(R':={|
      RA_normal:=post0; RA_break:=FALSE; RA_continue:=FALSE;RA_return:=(fun v=>FALSE)
    |});
      unfold RA_normal, RA_break, RA_continue, RA_return;
      intros;try apply derives_full_refl.
    { eapply derives_trans;[|apply H];solve_andp. }
    apply H0.
  + constructor. intros x.
    apply H1.
Qed.

Lemma add_post_to_semax_derives: forall P Q (x:partial_path_statement),
  ENTAIL Delta, Q |--  P ->
  add_post_to_semax Q x ->
  add_post_to_semax P x.
Proof.
  intros. destruct x as [pre path].
  induction H0.
  + constructor.
    eapply semax_aux_conseq with (P':=pre0)(R':={|
    RA_normal:=Q; RA_break:=FALSE; RA_continue:=FALSE;RA_return:=(fun v=>FALSE)
  |});
    unfold RA_normal, RA_break, RA_continue, RA_return;
    intros;try apply ENTAIL_refl.
    { eapply derives_trans;[|apply H]. solve_andp. }
    auto.
  + constructor. auto.
Qed.

(* Lemma add_post_to_semax_derives: forall P Q (x:partial_path_statement),
  ENTAIL Delta, ((allp_fun_id Delta) && Q) |-- |==> |> FF || P ->
  add_post_to_semax Q x ->
  add_post_to_semax P x.
Proof.
  intros. destruct x as [pre path].
  induction H0.
  + constructor.
    eapply semax_conseq with (P':=pre0)(R':={|
    RA_normal:=Q; RA_break:=FALSE; RA_continue:=FALSE;RA_return:=(fun v=>FALSE)
  |});
    unfold RA_normal, RA_break, RA_continue, RA_return;
    intros;try apply derives_full_refl;
    auto.
  + constructor. auto.
Qed. *)

Lemma atom_to_semax_derives: forall P1 P2 Q1 Q2 a,
  P2 |-- P1 ->
  ENTAIL Delta, Q1 |-- Q2 ->
  atom_to_semax P1 Q1 a ->
  atom_to_semax P2 Q2 a.
Proof.
  intros.
  constructor.
  inv H1.
  eapply semax_aux_conseq with (P':=P1)(R':={|
    RA_normal:=Q1; RA_break:=FALSE; RA_continue:=FALSE;RA_return:=(fun v=>FALSE)
  |});
  unfold RA_normal, RA_break, RA_continue, RA_return;
  intros;try apply ENTAIL_refl.
  - eapply derives_trans;[|apply H]. solve_andp. 
  - eapply derives_trans;[|apply H0]. solve_andp.
  - auto. 
Qed.

Lemma atom_return_to_semax_derives: forall P1 P2 Q1 Q2 a,
  P2 |-- P1 ->
  (forall v, ENTAIL Delta, Q1 v  |-- Q2 v ) ->
  atom_return_to_semax P1 Q1 a ->
  atom_return_to_semax P2 Q2 a.
Proof.
  intros. destruct a as [p r].
  constructor.
  inv H1.
  eapply semax_aux_conseq with (P':=P1)(R':={|
    RA_normal:=FALSE; RA_break:=FALSE; RA_continue:=FALSE;RA_return:=Q1
  |});
  unfold RA_normal, RA_break, RA_continue, RA_return;
  intros;try apply ENTAIL_refl.
  - eapply derives_trans;[|apply H]. solve_andp.
  - eapply derives_trans;[|apply H0]. solve_andp.
  - auto.
Qed.

(* Lemma atom_return_to_semax_derives: forall P1 P2 Q1 Q2 a,
  ENTAIL Delta, (allp_fun_id Delta) && P2 |-- |==> |> FF || P1 ->
  (forall v, ENTAIL Delta, (allp_fun_id Delta) && Q1 v  |-- |==> |> FF ||Q2 v ) ->
  atom_return_to_semax P1 Q1 a ->
  atom_return_to_semax P2 Q2 a.
Proof.
  intros. destruct a as [p r].
  constructor.
  inv H1.
  eapply semax_conseq with (P':=P1)(R':={|
    RA_normal:=FALSE; RA_break:=FALSE; RA_continue:=FALSE;RA_return:=Q1
  |});
  unfold RA_normal, RA_break, RA_continue, RA_return;
  intros;try apply derives_full_refl;auto.
Qed. *)


Lemma add_pre_to_semax_sem: forall (x:partial_path_statement),
  (add_pre_to_semax
        (EX Q : assert,
          !! (add_pre_to_semax Q x) && Q)) 
      x.
Proof.
  intros. destruct x as [post path].
  induction post.
  - constructor.
    apply semax_equiv.
    apply extract_exists_pre.
    intros Q.
    apply semax_extract_prop.
    intros. inv H.
    apply semax_equiv. auto.
  - constructor.
    intros x.
    specialize (H x).
    eapply add_pre_to_semax_derives;[|apply H].
    Intros Q. apply aux1_reduceR. apply aux2_reduceR. Exists Q.
    apply andp_right.
    + apply prop_right. inv H0. apply inj_pair2 in H3. subst.
      auto.
    + solve_andp.
Qed.

Lemma add_post_to_semax_reverse: forall post atom R,
  add_post_to_semax R (post_conn_atom post atom) ->
  add_post_to_semax (EX Q, Q && !! ( atom_to_semax Q R atom)) post.
Proof.
  intros. destruct post as [post path].
  induction post.
  - simpl in H. inv H.
    apply path_to_statement_app_aux in H1.
    apply semax_aux_seq_inv in H1.
    destruct H1 as [Q [? ?]].
    eapply add_post_to_semax_derives.
    2: { constructor.
          apply H. }
    Exists Q.
    apply andp_right.
    + apply ENTAIL_refl.
    + apply prop_right.
      constructor. auto.
  - constructor. intros.
    apply H0. inv H. apply inj_pair2 in H3. subst. simpl. auto.
Qed.

Lemma path_conn_to_semax_reverse_simple: forall pre a1,
  path_to_semax (post_conn_bind_pre pre [] a1) ->
    add_pre_to_semax a1 pre.
Proof.
  intros.
  destruct pre as [a2 p2]. induction a2.
  - inv H. constructor. auto.
  - inv H. apply inj_pair2 in H2. subst.
    constructor. intros. apply H0. simpl. auto.
Qed.
End Semantics.