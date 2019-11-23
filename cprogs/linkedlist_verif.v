Require Import AClight.proofauto.
Require Import cprogs.linkedlist_prog.
Require Import cprogs.linkedlist_def.
Require Import cprogs.linkedlist_annot.

Lemma body_sumlist: semax_body Vprog Gprog f_sumlist sumlist_spec.
Proof.
  start_function f_sumlist_hint.
  verify.
    + list_entailer.
    + list_entailer. subst. auto.
    + list_entailer. 
    ++ rewrite H0. rewrite<- app_assoc. simpl. auto.
    ++ f_equal. rewrite add_repr. f_equal. rewrite sum_Z_snoc;auto.
    + list_entailer.
    ++ f_equal. subst. rewrite app_nil_r. auto.
    ++ subst. rewrite app_nil_r. auto.
Qed.

Lemma body_append: semax_body Vprog Gprog f_append append_spec.
Proof.
  start_function f_append_hint. verify.
+ list_entailer. subst;auto.
+  list_entailer.
+ list_entailer.
+ list_entailer. rewrite<-H0. rewrite<-H3. subst. auto.
+ list_entailer. rewrite<-H3. rewrite<-app_assoc. simpl. auto.
+ list_entailer. rewrite H0 in H1. rewrite app_nil_r in H1. rewrite<-H1. rewrite<-app_assoc. simpl. auto. 
Qed.

(* Lemma body_append2: semax_body Vprog Gprog f_append2 append2_spec.
Proof.
  start_function f_append2_hint. verify.
+ list_entailer.
+ list_entailer.
++ rewrite<-H. subst. auto.
++ unfold field_address. simpl.
  rewrite if_true by auto with field_compatible;auto.
+ list_entailer. admit. simpl. admit.
+ simpl. intros. list_entailer. admit.
Admitted. *) 
Lemma body_append3: semax_body Vprog Gprog f_append3 append3_spec.
Proof.
  start_function f_append3_hint. verify.
  + list_entailer.
  + list_entailer. rewrite<-H. subst;auto. 
  + list_entailer. 
  ++ simpl. unfold field_address.
  rewrite if_true by auto with field_compatible;auto.
  ++ simpl. unfold_data_at (data_at Tsh t_struct_list _ t). entailer!.
  + list_entailer.  
  ++ rewrite<-app_assoc. simpl;auto.
  ++ simpl. cancel.
  + Intros t s3 s4 s v_fake0. 
  list_entailer. rewrite<-H0;auto.
  + sep_apply tmp. Intros u. list_entailer.
  + list_entailer. 
  ++ subst. rewrite app_nil_r. auto.
  ++ simpl. cancel.
Qed.

Lemma body_reverse: semax_body Vprog Gprog f_reverse reverse_spec.
Proof.
  start_function f_reverse_hint.
  verify.
  + list_entailer.
 + list_entailer. rewrite H;subst;auto.
+ list_entailer. simpl. rewrite<-app_assoc. simpl;auto.
+ list_entailer. subst. rewrite app_nil_r. symmetry;apply rev_involutive.
Qed.
Lemma body_maxlist: semax_body Vprog Gprog f_maxlist maxlist_spec.
Proof.
  start_function f_maxlist_hint.
  verify.
  + list_entailer.
  ++ simpl. apply umax_le.
  ++ simpl. apply umax_le.
  +  list_entailer.
  ++ subst. auto.
  ++ apply H1.
  ++ apply H1.
  ++ apply H. rewrite H0. rewrite H2. apply in_or_app.
  right;left;auto.
  ++ apply H. rewrite H0. rewrite H2. apply in_or_app.
  right;left;auto.
  + list_entailer. 
  ++ rewrite H2. rewrite<-app_assoc. simpl. auto.
  ++ apply Z.le_trans with z. apply H3. rewrite max_min2. apply Z.le_max_r.
  ++ rewrite max_min2. apply Z.max_lub. apply H1. apply H3.
  ++ f_equal. f_equal.  rewrite max_min2. apply Z.max_r. omega.
  + list_entailer.
  ++ rewrite H2. rewrite<-app_assoc. simpl. auto.
  ++ apply Z.le_trans with z. apply H3. rewrite max_min2. apply Z.le_max_r.
  ++ rewrite max_min2. apply Z.max_lub. apply H1. apply H3.
  ++ f_equal. f_equal.  rewrite max_min2. apply Z.max_l. omega.
  + list_entailer. 
  ++ subst. rewrite app_nil_r. auto.
  ++ subst. rewrite app_nil_r. auto.
Qed.
Lemma body_minlist: semax_body Vprog Gprog f_minlist minlist_spec.
Proof.
  start_function f_minlist_hint.
  verify.
  + list_entailer.
  ++ simpl. apply umax_le.
  ++ simpl. apply umax_le.
  +  list_entailer.
  ++ subst. auto.
  ++ apply H1.
  ++ apply H1.
  ++ apply H. rewrite H0. rewrite H2. apply in_or_app.
  right;left;auto.
  ++ apply H. rewrite H0. rewrite H2. apply in_or_app.
  right;left;auto.
  + list_entailer. 
  ++ rewrite H2. rewrite<-app_assoc. simpl. auto.
  ++ rewrite max_min3. apply Z.le_trans with z. apply H3. apply Z.min_glb. omega. omega. 
  ++ rewrite max_min3. apply Z.le_trans with z. apply Z.le_min_r. apply H3.
  ++ f_equal. f_equal.  rewrite max_min3. apply Z.min_r. omega.
  + list_entailer.
  ++ rewrite H2. rewrite<-app_assoc. simpl. auto.
  ++ rewrite max_min3. apply Z.le_trans with (min_Z s1). apply H1. apply Z.min_glb. omega. omega. 
  ++ rewrite max_min3. apply Z.le_trans with z. apply Z.le_min_r. apply H3.
  ++ f_equal. f_equal.  rewrite max_min3. apply Z.min_l. omega. 
  + list_entailer. 
  ++ subst. rewrite app_nil_r. auto.
  ++ subst. rewrite app_nil_r. auto.
Qed.
