Require Import AClight.proofauto.
Require Import cprogs.min_prog.
Require Import cprogs.min_def.
Require Import cprogs.min_annot.
Require Import AClight.advanced_forward.

Lemma body_min: semax_body Vprog Gprog f_minimum minimum_spec.
Proof.
start_function f_minimum_hint.
assert_prop (Zlength al = n). {
  entailer!. autorewrite with sublist; auto.
}
forwardD.
forwardD.
forwardD.
forwardD.
{
  Exists 0. entailer!.
}
- forwardD.
  forwardD.
  forwardD.
  forwardD.
  forwardD.
  forwardD.
  forwardD.
  assert (repable_signed (Znth i al))
    by (apply Forall_Znth; auto; omega).
  assert (repable_signed (fold_right Z.min (Znth 0 al) (sublist 0 i al)))
    by (apply Forall_fold_min;
      [apply Forall_Znth; auto; omega
      |apply Forall_sublist; auto]).
  forwardD.
  forwardD.
  forwardD.
  {
    entailer!.
    rewrite (sublist_split 0 i (i+1)) by omega.
    rewrite (sublist_one i (i+1) al) by omega.
    rewrite fold_min_another.
    rewrite Z.min_r.
    - auto.
    - omega.
  }
  forwardD.
  {
    entailer!.
    rewrite (sublist_split 0 i (i+1)) by omega.
    rewrite (sublist_one i (i+1) al) by omega.
    rewrite fold_min_another.
    rewrite Z.min_l.
    - auto.
    - omega.
  }
  forwardD.
  forwardD.
  forwardD.
  {
    Exists (i+1). entailer!.
  }
- forwardD.
  forwardD.
  {
    entailer!.
    autorewrite with sublist.
    destruct al; simpl; auto.
  }
Qed.

Lemma body_min2: semax_body Vprog Gprog f_minimum minimum_spec.
Proof.
start_function f_minimum_hint.
assert_prop (Zlength al = n). {
  entailer!. autorewrite with sublist; auto.
}
forwardD.
forwardD.
forwardD.
forwardD.
{
  Exists 0. entailer!.
}
- forwardD.
  forwardD.
  forwardD.
  forwardD.
  forwardD.
  forwardD.
  intro d; Intros; revert d.
  assert (repable_signed (Znth i al))
    by (apply Forall_Znth; auto; omega).
  assert (repable_signed (fold_right Z.min (Znth 0 al) (sublist 0 i al)))
    by (apply Forall_fold_min;
      [apply Forall_Znth; auto; omega
      |apply Forall_sublist; auto]).
  
  intro.
  forwardM_if.
  forwardM.
  forwardM.
  forwardM.
  forwardM.
  {
    Exists (i+1).
    entailer!.
    rewrite (sublist_split 0 i (i+1)) by omega.
    rewrite (sublist_one i (i+1) al) by omega.
    rewrite fold_min_another.
    rewrite Z.min_r.
    - auto.
    - omega.
  }
  {
    Exists (i+1).
    entailer!.
    rewrite (sublist_split 0 i (i+1)) by omega.
    rewrite (sublist_one i (i+1) al) by omega.
    rewrite fold_min_another.
    rewrite Z.min_l.
    - auto.
    - omega.
  }
- forwardD.
  forwardD.
  {
    entailer!.
    autorewrite with sublist.
    destruct al; simpl; auto.
  }
Qed.
