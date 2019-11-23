Require Import AClight.proofauto.
Require Import cprogs.dlinklist_prog.
Require Import cprogs.dlinklist_def.
Require Import cprogs.dlinklist_annot.
From Coq Require Import Psatz.

Lemma body_sumlist: semax_body Vprog Gprog f_sumlist sumlist_spec.
Proof.
  start_function f_sumlist_hint.
  verify.
  + Exists (@nil Z). Exists sigma. Exists p. Exists nullval. entailer!. 
    entailer!. unfold lseg_pre. unfold listrep. entailer!. 
  + assert_PROP (s2 <> nil).
    {
      entailer!.
      assert( t = nullval). apply H0. auto.
      subst.
      apply Pt.
    }
    destruct s2; [ destruct H0; auto |].
    unfold listrep;unfold listrep_pre;fold listrep_pre. Intros y. 
    Exists  s2. Exists z. Exists y.
    entailer!.
  + Exists ( s1 ++ [z]); Exists s2; Exists y; Exists t.
    entailer!.
    ++ rewrite<- app_assoc. simpl. split. 
    +++ apply H0.
    +++ f_equal. f_equal. apply sum_Z_snoc.
    ++ entailer!. sep_apply singleton_lseg.
    sep_apply (lseg_lseg_pre s1 [z] p t y nullval s t). entailer!.
  + assert(s2=[]). { apply H1. auto. } rewrite H.
      entailer!.
    ++ f_equal. rewrite app_nil_r. auto.
    ++ simpl. rewrite app_nil_r. entailer!. apply lseg_listrep_pre.
Qed.

Lemma body_maxlist: semax_body Vprog Gprog f_maxlist maxlist_spec.
Proof.
  start_function f_maxlist_hint.
  verify.
  + Exists (@nil Z). Exists sigma. Exists p. Exists nullval.
  entailer!.
  ++ simpl. split;[simpl;apply umax_le|simpl;apply umax_le].
  ++ unfold lseg_pre. entailer!. unfold listrep;auto.
  + assert_PROP (s2 <> nil).
    {
      entailer!.
      assert( t = nullval). apply H2. auto.
      subst.
      apply Pt.
    }
    destruct s2; [ destruct H2; auto |].
    unfold listrep_pre;fold listrep_pre. Intros y.
    Exists s2;Exists z;Exists y.
    entailer!. apply H. apply in_or_app. right;left;auto.
  + Exists (s1++[z]);Exists s2';Exists y;Exists t. entailer!.
  ++ split.
  +++ rewrite<- app_assoc. rewrite H2. reflexivity.
  +++ split.
  ++++ rewrite max_min2. lia.
  ++++ f_equal. f_equal. rewrite max_min2. apply Z.max_r. lia.
  ++ sep_apply singleton_lseg. admit.
Admitted.
Lemma body_minlist: semax_body Vprog Gprog f_minlist minlist_spec.
Proof.
  start_function f_minlist_hint.
  verify.
Admitted.

Lemma body_append: semax_body Vprog Gprog f_append append_spec.
Proof.
  start_function f_append_hint. verify.
Admitted.
Lemma body_reverse: semax_body Vprog Gprog f_reverse reverse_spec.
Proof.
  start_function f_reverse_hint.
  verify.
Admitted.
Lemma body_find: semax_body Vprog Gprog f_find find_spec.
Proof.
  start_function f_find_hint.
  verify.
Admitted.
Lemma body_findprev: semax_body Vprog Gprog f_findprev findprev_spec.
Proof.
  start_function f_findprev_hint.
  verify.
Admitted.
Lemma body_findnext: semax_body Vprog Gprog f_findnext findnext_spec.
Proof.
  start_function f_findnext_hint.
  verify.
Admitted.