Require Export CSplit.AClight.

Require Import VST.floyd.proofauto.
Require Import CSplit.strong.


Section Semantics.

Context {CS: compspecs} {Espec: OracleKind} (Delta: tycontext).

Fixpoint to_Clight  (a: atom_statement) : Clight.statement :=
match a with
| Askip => Clight.Sskip
| Aassign e1 e2 => Clight.Sassign e1 e2
| Aset id e => Clight.Sset id e
| Acall id e elis => Clight.Scall id e elis
end.

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



Lemma path_to_statement_app_aux: forall P Q l1 l2,
  semax Delta P (Clight.Ssequence (path_to_statement l1)
    (path_to_statement l2)) Q <->
    semax Delta P (path_to_statement (l1++l2)) Q.
Proof.
  intros. revert P. induction l1.
  { intros. simpl. split;intro.
    + apply semax_seq_inv in H.
      destruct H as [R1 [E1 E3]].
      apply semax_skip_inv in E1.
      eapply semax_pre' with (P':=RA_normal (overridePost R1 Q)).
      { eapply derives_trans;[|apply E1]. solve_andp. }
      unfold overridePost. unfold RA_normal. destruct Q. auto.
    + eapply semax_seq. 2:{ apply H. } 
      destruct Q;unfold_der.
      eapply semax_simple_inv with (Post:=normal_ret_assert P);auto.
      constructor.
  }
  { intros. destruct a; simpl.
    { split;intro.
      + apply semax_seq_inv in H.
        destruct H as [R2 [E1 E3]].
        apply semax_seq_inv in E1.
        destruct E1 as [R1 [E1 E2]].
        pose proof semax_seq _ _ _ _ _ _ E2 E3.
        apply IHl1 in H.
        eapply semax_seq with (Q0:=R1);auto.
        rewrite overridePost_overridePost in E1.
        auto.
      + apply semax_seq_inv in H.
        destruct H as [R1 [E1 E3]].
        apply IHl1 in E3.
        apply semax_seq_inv in E3.
        destruct E3 as [R2 [E2 E3]].
        eapply semax_seq.
        { eapply semax_seq.
          + rewrite overridePost_overridePost. apply E1.
          + apply E2. }
        apply E3.
    }
    { split;intro.
      + apply semax_seq_inv in H.
        destruct H as [R2 [E1 E3]].
        apply semax_seq_inv in E1.
        destruct E1 as [R1 [E1 E2]].
        pose proof semax_seq _ _ _ _ _ _ E2 E3.
        apply IHl1 in H.
        eapply semax_seq with (Q0:=R1);auto.
        rewrite overridePost_overridePost in E1.
        auto.
      + apply semax_seq_inv in H.
        destruct H as [R1 [E1 E3]].
        apply IHl1 in E3.
        apply semax_seq_inv in E3.
        destruct E3 as [R2 [E2 E3]].
        eapply semax_seq.
        { eapply semax_seq.
          + rewrite overridePost_overridePost. apply E1.
          + apply E2. }
        apply E3.
    }
  }
Qed.


Fixpoint path_to_semax { s_path: S_full_path }
  (c_path: C_full_path s_path) : Prop :=
  match c_path with
  | mk_C_full_path pre path post =>
      @semax CS Espec Delta pre (path_to_statement path)
      (normal_ret_assert post)
  | bind_C_full_path A HA s_path' c_path' =>
      forall (a:A), path_to_semax (c_path' a)
  end.

Fixpoint post_to_semax post { s_post : S_partial_post }
  (c_post: C_partial_post s_post) : Prop :=
  match c_post with
  | mk_C_partial_post pre path =>
      @semax CS Espec Delta pre (path_to_statement' path)
      (normal_ret_assert post)
  | bind_C_partial_post A HA s_post' c_post' =>
      forall (a:A), post_to_semax post (c_post' a)
  end.


Definition return_ret_assert (Q: option val -> environ->mpred) : ret_assert :=
  {| RA_normal := seplog.FF; RA_break := seplog.FF; RA_continue := seplog.FF; RA_return := Q |}.


Fixpoint post_ret_to_semax post { s_post : S_partial_post_ret }
  (c_post: C_partial_post_ret s_post) : Prop :=
  match c_post with
  | mk_C_partial_post_ret pre path retval =>
      @semax CS Espec Delta pre 
        (Clight.Ssequence 
          (path_to_statement' path)
          (Clight.Sreturn retval))
      (return_ret_assert post)
  | bind_C_partial_post_ret A HA s_post' c_post' =>
      forall (a:A), post_ret_to_semax post (c_post' a)
  end.

Definition atom_to_semax pre post atom := 
  match atom with
  | mk_atom path =>
      @semax CS Espec Delta pre 
        (path_to_statement path)
        (normal_ret_assert post)
  end.


Definition atom_ret_to_semax pre post atom := 
  match atom with
  | mk_atom_ret path retval =>
      @semax CS Espec Delta pre 
        (Clight.Ssequence (path_to_statement path) (Clight.Sreturn retval))
        (normal_ret_assert post)
  end.


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
    * simpl. auto.
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
      * simpl in H3. apply H3.
      * auto.
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
      * simpl. auto.
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
    * inv H3. apply inj_pair2 in H2. subst. auto.
    (* apply H3. *)
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
  ENTAIL Delta, ((allp_fun_id Delta) && Q) |--  P ->
  add_pre_to_semax P x ->
  add_pre_to_semax Q x.
Proof.
  intros. destruct x as [post path].
  induction post.
  + simpl. eapply semax_pre';[..|apply H0].
    auto.
  + simpl in *. auto.
Qed.

Lemma add_pre_to_semax_derives_aux: forall P Q post path,
  ENTAIL Delta, ((allp_fun_id Delta) && Q) |--  P ->
  add_pre_to_semax post P path ->
  add_pre_to_semax post Q path.
Proof.
  intros.
  induction post.
  + simpl. eapply semax_pre';[..|apply H0].
    auto.
  + simpl in *. auto.
Qed.

Lemma add_pre_to_semax_derives_weak: forall P Q (x:partial_path_statement),
  Q |--  P ->
  add_pre_to_semax P x ->
  add_pre_to_semax Q x.
Proof.
  intros.
  eapply add_pre_to_semax_derives;[|apply H0].
  (* apply aux1_reduceR. apply aux2_reduceR. *)
  eapply derives_trans;[|apply H];solve_andp.
Qed.

Lemma add_post_to_semax_derives: forall P Q (x:partial_path_statement),
  ENTAIL Delta, Q |--  P ->
  add_post_to_semax Q x ->
  add_post_to_semax P x.
Proof.
  intros. destruct x as [pre path]. induction pre.
  + simpl in H0. simpl.
    eapply semax_conseq with (P':=a)(R':={|
    RA_normal:=Q; RA_break:=FALSE; RA_continue:=FALSE;RA_return:=(fun v=>FALSE)
  |});
    unfold RA_normal, RA_break, RA_continue, RA_return;
    intros;try solve_andp.
    { eapply derives_trans;[|apply H]. solve_andp. }
    auto.
  + simpl. simpl in H0. intros.
    specialize (H0 x). apply H1 in H0. auto.
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
  eapply semax_conseq with (P':=P1)(R':={|
    RA_normal:=Q1; RA_break:=FALSE; RA_continue:=FALSE;RA_return:=(fun v=>FALSE)
  |});
  unfold RA_normal, RA_break, RA_continue, RA_return;
  intros;try solve_andp.
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
  eapply semax_conseq with (P':=P1)(R':={|
    RA_normal:=FALSE; RA_break:=FALSE; RA_continue:=FALSE;RA_return:=Q1
  |});
  unfold RA_normal, RA_break, RA_continue, RA_return;
  intros;try solve_andp.
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
  - apply aux_semax_extract_exists.
    intros Q.
    apply aux_semax_extract_prop.
    intros. auto.
  - intros x. specialize (H x).
    eapply add_pre_to_semax_derives_aux. 2:{ apply H. }
    Intros Q. Exists Q.
    apply andp_right.
    + apply prop_right. apply H0.
    + solve_andp.
Qed.

Lemma add_post_to_semax_reverse: forall post atom R,
  add_post_to_semax R (post_conn_atom post atom) ->
  add_post_to_semax (EX Q, Q && !! ( atom_to_semax Q R atom)) post.
Proof.
  intros. destruct post as [post path].
  induction post.
  - simpl in H.
    apply path_to_statement_app_aux in H.
    apply semax_seq_inv in H.
    destruct H as [Q [? ?]].
    eapply add_post_to_semax_derives.
    2: { simpl. apply H. }
    Exists Q.
    apply andp_right.
    + solve_andp.
    + apply prop_right. auto.
  - simpl. intros. simpl in H. specialize (H x). apply H0 in H. auto.
Qed.

Lemma path_conn_to_semax_reverse_simple: forall pre a1,
  path_to_semax (post_conn_bind_pre pre [] a1) ->
    add_pre_to_semax a1 pre.
Proof.
  intros.
  destruct pre as [a2 p2]. simpl in H.
  (* induction H.
  - destruct HX. auto.
  - hnf.  *)
  induction a2.
  - inv H. auto.
   (* simpl in H. auto. *)
  - simpl in H0, H. inv H.
    apply inj_pair2 in H3. subst.
    hnf. intros. apply H0. auto.
  (* intros x. auto. *)
Qed.


(* -------------------------------------------------
   Assertion Derivation 
   for paths/partial paths/atoms 
--------------------------------------------------- *)
Lemma atom_return_to_semax_derives_pre: forall p P1 P2 Q,
P1 |-- P2 ->
atom_return_to_semax P2 Q p ->
atom_return_to_semax P1 Q p.
Proof.
 intros.
 eapply atom_return_to_semax_derives.
 { apply H. }
 { intros. solve_andp. }
 { auto. }
Qed.


Lemma atom_return_to_semax_derives_pre_group: forall P1 P2 Q atoms,
  P1 |-- P2 ->
  Forall (atom_return_to_semax P2 Q) atoms ->
  Forall (atom_return_to_semax P1 Q) atoms.
Proof. 
  intros.
  eapply Forall_forall.
  intros. eapply atom_return_to_semax_derives_pre.
  apply H. eapply Forall_forall in H0. apply H0. auto.
Qed.

Lemma add_pre_to_semax_derives_group_weak: forall P1 P2 pres,
  P1 |-- P2 ->
  Forall (add_pre_to_semax P2) pres ->
  Forall (add_pre_to_semax P1) pres.
Proof. 
  intros.
  eapply Forall_forall.
  intros. eapply add_pre_to_semax_derives_weak.
  apply H. eapply Forall_forall in H0. apply H0. auto.
Qed.


Lemma add_pre_to_semax_derives_group: forall P1 P2 pres,
  (* ENTAIL Delta, ((allp_fun_id Delta) && P1) |-- |==> |> FF || P2 -> *)
  ENTAIL Delta, ((allp_fun_id Delta) && P1) |--  P2 ->
  Forall (add_pre_to_semax P2) pres ->
  Forall (add_pre_to_semax P1) pres.
Proof. 
  intros.
  eapply Forall_forall.
  intros. eapply add_pre_to_semax_derives.
  apply H. eapply Forall_forall in H0. apply H0. auto.
Qed.

Lemma atom_to_semax_derives_pre: forall p P1 P2 Q,
  P1 |-- P2 ->
  atom_to_semax P2 Q p ->
  atom_to_semax P1 Q p.
Proof.
  intros.
  eapply atom_to_semax_derives.
  - apply H.
  - solve_andp.
  - auto.
Qed.

Lemma atom_to_semax_derives_pre_group: forall P1 P2 Q atoms,
  P1 |-- P2 ->
  Forall (atom_to_semax P2 Q) atoms ->
  Forall (atom_to_semax P1 Q) atoms.
Proof. 
  intros.
  eapply Forall_forall.
  intros. eapply atom_to_semax_derives_pre.
  apply H. eapply Forall_forall in H0. apply H0. auto.
Qed.

Lemma atom_to_semax_derives_post: forall p P Q1 Q2,
  ENTAIL Delta, Q1 |-- Q2 ->
  atom_to_semax P Q1 p ->
  atom_to_semax P Q2 p.
Proof.
  intros.
  eapply atom_to_semax_derives.
  - apply derives_refl.
  - apply H.
  - auto.
Qed.

Lemma add_post_to_semax_conj_rule: forall Q1 Q2 post,
add_post_to_semax Q1 post ->
add_post_to_semax Q2 post ->
add_post_to_semax (Q1 && Q2) post.
Proof.
  intros. destruct post as [post path].
  induction post.
  - simpl in *.
    eapply semax_conseq.
    6: { eapply semax_conj_rule with (Q1:= {|
        RA_normal := Q1;
        RA_break := FALSE;
        RA_continue := FALSE;
        RA_return := fun _ : option val => FALSE |}) (Q2:= {|
        RA_normal := Q2;
        RA_break := FALSE;
        RA_continue := FALSE;
        RA_return := fun _ : option val => FALSE |}).
        + apply H.
        + apply H0.
    }
    { solve_andp. }
    { solve_andp. }
    { solve_andp. }
    { solve_andp. }
    { intros. solve_andp. }
  - simpl in *. auto.
Qed.

Lemma atom_to_semax_conj_rule: forall P Q1 Q2 atom,
  atom_to_semax P Q1 atom ->
  atom_to_semax P Q2 atom ->
  atom_to_semax P (Q1 && Q2) atom.
Proof.
  intros.
  eapply semax_conseq.
  6: { 
    eapply semax_conj_rule with (Q1:= {|
        RA_normal := Q1;
        RA_break := FALSE;
        RA_continue := FALSE;
        RA_return := fun _ : option val => FALSE |}) (Q2:= {|
        RA_normal := Q2;
        RA_break := FALSE;
        RA_continue := FALSE;
        RA_return := fun _ : option val => FALSE |});auto.
    apply H. apply H0. }
  { solve_andp. }
  { solve_andp. }
  { solve_andp. }
  { solve_andp. }
  { intros. solve_andp. }
Qed.

End Semantics.