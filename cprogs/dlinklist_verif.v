Require Import AClight.proofauto.
Require Import cprogs.dlinklist_prog.
Require Import cprogs.dlinklist_def.
Require Import cprogs.dlinklist_annot.
From Coq Require Import Psatz.

(* Lemma body_sumlist: semax_body Vprog Gprog f_sumlist sumlist_spec.
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
  ++ sep_apply singleton_lseg. sep_apply (lseg_lseg_pre s1 [z] p t y nullval s t).
  auto.
  + Exists (s1 ++ [z]);Exists s2';Exists y;Exists t. entailer!.
  ++ split.
  +++ rewrite<- app_assoc. rewrite H2. reflexivity.
  +++ split.
  ++++ rewrite max_min2. lia.
  ++++ f_equal. f_equal. rewrite max_min2. apply Z.max_l. lia.
  ++ sep_apply singleton_lseg.  sep_apply (lseg_lseg_pre s1 [z] p t y nullval s t).
  auto.
  + assert(s2=[]). { rewrite<-H3;auto. } subst.
  entailer!.
  ++ f_equal. f_equal. rewrite app_nil_r. auto.
  ++ rewrite app_nil_r. unfold listrep_pre. entailer!.
  sep_apply lseg_listrep_pre. unfold listrep;entailer!.
Qed.
Lemma body_minlist: semax_body Vprog Gprog f_minlist minlist_spec.
Proof.
  start_function f_minlist_hint.
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
  ++++ rewrite max_min3. lia.
  ++++ f_equal. f_equal. rewrite max_min3. apply Z.min_r. lia.
  ++ sep_apply singleton_lseg. sep_apply (lseg_lseg_pre s1 [z] p t y nullval s t).
  auto.
  + Exists (s1 ++ [z]);Exists s2';Exists y;Exists t. entailer!.
  ++ split.
  +++ rewrite<- app_assoc. rewrite H2. reflexivity.
  +++ split.
  ++++ rewrite max_min3. lia.
  ++++ f_equal. f_equal. rewrite max_min3. apply Z.min_l. lia.
  ++ sep_apply singleton_lseg.  sep_apply (lseg_lseg_pre s1 [z] p t y nullval s t).
  auto.
  + assert(s2=[]). { rewrite<-H3;auto. } subst.
  entailer!.
  ++ f_equal. f_equal. rewrite app_nil_r. auto.
  ++ rewrite app_nil_r. unfold listrep_pre. entailer!.
  sep_apply lseg_listrep_pre. unfold listrep;entailer!.
Qed.
 *)

Lemma body_append: semax_body Vprog Gprog f_append append_spec.
Proof.
  start_function f_append_hint. verify.
  + unfold listrep. entailer!.
  + Exists y. entailer!. unfold listrep. entailer!. assert(s1=[]).
  { rewrite<-H0. auto. } rewrite H1. rewrite app_nil_l. simpl. entailer!.
  + destruct s1. { unfold listrep;unfold listrep_pre;fold listrep_pre. Intros.
  destruct H. rewrite H0. auto. } unfold listrep;unfold listrep_pre;fold listrep_pre.
  Intros y0. Exists z. Exists s1. Exists y0. entailer!.
  + Exists w. Exists x. Exists (@nil Z). Exists s1'. Exists z. Exists nullval.
  entailer!.  unfold lseg_pre.  entailer!.
  + assert_PROP (s4 <> nil).
    {
      entailer!.
     destruct H2.
      rewrite H3.
      auto.
    }
  destruct s4. { destruct H3. auto. } 
    unfold listrep;unfold listrep_pre;fold listrep_pre. Intros y0.  
    Exists z0. Exists s4. Exists y0. Exists t. entailer!.
  + Exists y'. Exists p. Exists (s3++[j]). Exists s4'. Exists z0. Exists q.
  entailer!.
  ++ rewrite<-H3. rewrite<- app_assoc. simpl. auto.
  ++ sep_apply singleton_lseg.  sep_apply (lseg_lseg_pre s3 [j] x q p nullval k q).
  auto.
  + assert_PROP (s2 <> nil).
    {
      entailer!.
     destruct H3.
      rewrite H7.
      auto.
    }
  destruct s2.
  ++ destruct H4;auto.
  ++ unfold listrep_pre;fold listrep_pre. Intros y0. Exists p q. Exists s3 s4. Exists j. Exists t. Exists z0. Exists s2. Exists y0. entailer!.
  +  Exists x. entailer!. simpl. repeat sep_apply singleton_lseg.
  sep_apply (lseg_lseg_pre s0 [j0] x q0 y nullval t0 q0). 
  assert(s5=[]). { rewrite<-H6;auto. } subst. unfold listrep_pre  at 1. entailer!.
   sep_apply (lseg_lseg_pre (s0++[j0]) [r] x y i nullval q0 y).
   sep_apply lseg_listrep_app. unfold listrep. rewrite app_nil_r in H4. rewrite H4.
   simpl. rewrite<-app_assoc. simpl. auto.
  + Exists x. entailer!. sep_apply singleton_lseg.
  assert(s4=[]). { rewrite<-H4. auto. }
  assert(s2=[]). { rewrite<-H7. auto. } subst. entailer!. unfold listrep_pre. entailer!. sep_apply (lseg_lseg_pre s3 [j] x q nullval nullval t q). rewrite <-H1.
  repeat rewrite app_nil_r. unfold listrep. sep_apply lseg_listrep_pre. entailer!.
Qed.
Lemma body_reverse: semax_body Vprog Gprog f_reverse reverse_spec.
Proof.
  start_function f_reverse_hint.
  verify.
  + Exists (@nil Z) sigma nullval p.
    entailer!.
    unfold listrep. unfold listrep_pre.
    entailer!.
  +  assert_PROP (s2 <> nil).
    {
      entailer!.
      pose proof proj2 H1 eq_refl.
      subst.
      apply Pv.
    } destruct s2. { destruct H0;auto. } unfold listrep_pre;fold listrep_pre.
    Intros y.
   Exists y;Exists z;Exists s2. entailer!.
  + Exists (z::s1);Exists s2';Exists v k. entailer!.
  ++ simpl. rewrite<-app_assoc. rewrite H0. simpl. auto.
  ++ sep_apply singleton_lseg. sep_apply lseg_listrep_app. simpl;auto.
  + Exists w. entailer!. assert( s2 = []) . rewrite<- H2;auto. subst.
  unfold listrep_pre at 2. entailer!. rewrite <- app_nil_end, rev_involutive.
  unfold listrep;auto.
Qed.

Lemma body_findprev: semax_body Vprog Gprog f_findprev findprev_spec.
Proof.
  start_function f_findprev_hint.
  verify.
  + entailer!. unfold lseg_pre. Intros u. subst. entailer!.
  + entailer!. unfold lseg_pre. Exists r;entailer!.
Qed.
Lemma body_findnext: semax_body Vprog Gprog f_findnext findnext_spec.
Proof.
  start_function f_findnext_hint.
  verify.
  + entailer!. unfold lseg_pre. Intros u. subst. entailer!.
  + entailer!. unfold lseg_pre. Exists r;entailer!.
Qed.