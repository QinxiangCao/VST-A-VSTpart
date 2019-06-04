Require Import annotation_proofauto.
Require Import sumarray2.
Require Import sumarray2_def.
Require Import sumarray2_annotation.

Lemma body_sumarray: semax_body Vprog Gprog f_sumarray sumarray_spec.
Proof.
start_function.
unfold Sfor in *.
match goal with
| |- ?P => let d1 := eval hnf in f_sumarray_hint in
           change (let d := @abbreviate _ d1 in P)
end.
forwardD a.
forwardD sh.
forwardD contents.
forwardD size.
forwardD.
forwardD.
forwardD.
forwardD.
{ EExists. entailer!. }
forwardD.
lazymatch goal with
| |- let d := @abbreviate _ (Ssequence (Sloop (LISingle ?Inv) _ _) _) in
       (* semax _ _ (Clight.Ssequence (Clight.Sloop _ _) _) _ => *)
       _ =>
      intro d; forward_loop Inv end.
forwardD.
lazymatch goal with
| |- let d := @abbreviate _ (Ssequence (Sloop (LISingle ?Inv) _ _) _) in
       (* semax _ _ (Clight.Ssequence (Clight.Sloop _ _) _) _ => *)
       _ =>
      intro d; forward_loop Inv;
      [ ..
      | revert d; refine (decorate_C_loop_body _ _ _ _ _ _ _ _ _ _)
      | revert d; refine (decorate_C_loop_incr _ _ _ _ _ _ _ _ _ _)
      | revert d; refine (decorate_C_loop_after _ _ _ _ _ _ _ _ _ _)]
end.
forward_loop (EX i: Z,
    PROP  (0 <= i <= size)
    LOCAL (temp _a a;
          temp _i (Vint (Int.repr i));
          temp _n (Vint (Int.repr size));
          temp _s (Vint (Int.repr (sum_Z (sublist 0 i contents)))))
    SEP   (data_at sh (tarray tuint size) (map Vint (map Int.repr contents)) a)).
forwardD.
intro d.
forward.
revert d.
forwardD.
forward_loop (EX i: Z,
    PROP  (0 <= i <= size)
    LOCAL (temp _a a;
          temp _i (Vint (Int.repr i));
          temp _n (Vint (Int.repr size));
          temp _s (Vint (Int.repr (sum_Z (sublist 0 i contents)))))
    SEP   (data_at sh (tarray tuint size) (map Vint (map Int.repr contents)) a)).
forwardD.
forward_for_simple_bound size
  (EX i: Z,
   PROP  ((*0 <= i <= size*))
   LOCAL (temp _a a;
          (*temp _i (Vint (Int.repr i)); *)
          temp _n (Vint (Int.repr size));
          temp _s (Vint (Int.repr (sum_Z (sublist 0 i contents)))))
   SEP   (data_at sh (tarray tuint size) (map Vint (map Int.repr contents)) a)).

* (* Prove that current precondition implies loop invariant *)
entailer!.
* (* Prove postcondition of loop body implies loop invariant *)
(* "forward" fails and tells us to first make (0 <= i < Zlength contents)
   provable by auto, so we assert the following: *)
assert_PROP (Zlength contents = size). {
  entailer!. do 2 rewrite Zlength_map. reflexivity.
}
forward. (* x = a[i] *)
forward. (* s += x; *)
 (* Now we have reached the end of the loop body, and it's
   time to prove that the _current precondition_  (which is the
   postcondition of the loop body) entails the loop invariant. *)
entailer!.
 f_equal. f_equal.
 rewrite (sublist_split 0 i (i+1)) by omega.
 rewrite sum_Z_app. rewrite (sublist_one i) by omega.
 simpl. autorewrite with sublist. normalize.
* (* After the loop *)
forward.  (* return s; *)
 (* Here we prove that the postcondition of the function body
    entails the postcondition demanded by the function specification. *)
entailer!.
autorewrite with sublist in *.
reflexivity.
Qed.

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