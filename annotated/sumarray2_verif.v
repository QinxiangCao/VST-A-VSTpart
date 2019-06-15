Require Import annotation_proofauto.
Require Import sumarray2.
Require Import sumarray2_def.
Require Import sumarray2_annotation.

Lemma body_sumarray: semax_body Vprog Gprog f_sumarray sumarray_spec.
Proof.
start_function.
use_annotation f_sumarray_hint.
forwardD a.
forwardD sh.
forwardD contents.
forwardD size.
forwardD.
forwardD.
forwardD.
{ EExists. entailer!. }
* forwardD.
  forwardD.
  assert_prop (Zlength contents = size). {
    entailer!. list_solve2.
  }
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
  forwardD.
  forwardD.
  apply fold_right_and_rev_nil.
* simpl rev.
  forwardD.
  forwardD.
  { entailer!. assert (i = Zlength contents) by list_solve2. subst i.
    autorewrite with sublist in *. reflexivity.
  }
Qed.

(*
(* Contents of the extern global initialized array "_four" *)
Definition four_contents := [1; 2; 3; 4].

Lemma Forall_sublist: forall {A} (P: A->Prop) lo hi (al: list A),
  Forall P al -> Forall P (sublist lo hi al).
Proof.
intros.
apply Forall_forall. rewrite -> Forall_forall in H.
intros.
apply H; auto.
apply sublist_In in H0. auto.
Qed.

Lemma body_main:  semax_body Vprog Gprog f_main main_spec.
Proof.
start_function.
set (four := gv _four).
change [Int.repr 1; Int.repr 2; Int.repr 3; Int.repr 4] with (map Int.repr four_contents).
set (contents :=  map Vint (map Int.repr four_contents)).
assert (Zlength contents = 4) by (subst contents; reflexivity).
assert_PROP (field_compatible (tarray tuint 4) [] four) by entailer!.
assert (Forall (fun x : Z => Int.min_signed <= x <= Int.max_signed) four_contents)
  by (repeat constructor; computable).
 rewrite <- (sublist_same 0 4 contents), (sublist_split 0 2 4)
    by now autorewrite with sublist.
erewrite (split2_data_at_Tarray_app 2 4); try apply JMeq_refl; auto; try omega; try reflexivity.
Intros.
forward_call (*  s = sumarray(four+2,2); *)
  (field_address0 (tarray tuint 4) [ArraySubsc 2] four, Ews,
    sublist 2 4 four_contents,2).
+
 entailer!.
 rewrite field_address0_offset by auto with field_compatible.
 normalize.
+ split. auto. computable.
+
  gather_SEP 1 2.
  erewrite <- (split2_data_at_Tarray_app 2 4); try apply JMeq_refl; auto; try omega; try reflexivity.
  rewrite <- !sublist_map. fold contents. autorewrite with sublist.
  rewrite (sublist_same 0 4) by auto.
  forward. (* return *)
Qed.

Existing Instance NullExtension.Espec.

Lemma prog_correct:
  semax_prog prog Vprog Gprog.
Proof.
prove_semax_prog.
semax_func_cons body_sumarray.
semax_func_cons body_main.
Qed.
*)