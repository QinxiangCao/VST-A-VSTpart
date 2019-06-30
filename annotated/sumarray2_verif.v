Require Import annotation_proofauto.
Require Import sumarray2_prog.
Require Import sumarray2_def.
Require Import sumarray2_annot.

Lemma body_sumarray: semax_body Vprog Gprog f_sumarray sumarray_spec.
Proof.
start_function f_sumarray_hint.
forwardD.
forwardD.
forwardD.
forwardD.
{ EExists. entailer!. }
* forwardD.
  assert_prop (Zlength contents = size). {
    entailer!. list_solve2.
  }
  forwardD.
  forwardD.
  forwardD.
  forwardD.
  forwardD.
  forwardD.
  forwardD.
  { Exists (i+1). entailer!.
    f_equal. f_equal.
    rewrite (sublist_split 0 i (i+1)) by omega.
    rewrite sum_Z_app. rewrite (sublist_one i) by omega.
    auto.
    simpl. autorewrite with sublist. normalize.
  }
* forwardD.
  forwardD.
  { entailer!. assert (i = Zlength contents) by list_solve2. subst i.
    autorewrite with sublist in *. reflexivity.
  }
Qed.

Definition four_contents := [1; 2; 3; 4].

Lemma body_main:  semax_body Vprog Gprog f_main main_spec.
Proof.
start_function f_main_hint.
set (four := gv _four).
change [Int.repr 1; Int.repr 2; Int.repr 3; Int.repr 4] with (map Int.repr four_contents).
set (contents :=  map Vint (map Int.repr four_contents)).
assert (Zlength contents = 4) by (subst contents; reflexivity).
assert_prop (field_compatible (tarray tuint 4) [] four). { entailer!. }
assert (Forall (fun x : Z => Int.min_signed <= x <= Int.max_signed) four_contents)
  by (repeat constructor; computable).
 rewrite <- (sublist_same 0 4 contents), (sublist_split 0 2 4)
    by now autorewrite with sublist.
erewrite (split2_data_at_Tarray_app 2 4); try apply JMeq_refl; auto; try omega; try reflexivity.
intro d.
forward_call (*  s = sumarray(four+2,2); *)
  (field_address0 (tarray tuint 4) [ArraySubsc 2] four, Ews,
    sublist 2 4 four_contents,2).
{ entailer!.
  rewrite field_address0_offset by auto with field_compatible.
  normalize.
}
{ entailer!. }
{ split. auto. computable. }
revert d.
forwardD.
Qed.
