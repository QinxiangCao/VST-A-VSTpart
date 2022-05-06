Require Import CSplit.AClightFunc.

(* 
int sgn (int x) {
  //@ With x:Z,
  //@ Require PROP (Int.min_signed <= x <= Int.max_signed) LOCAL (temp _x  (Vint (Int.repr x))) SEP ()
  //@ Ensure PROP () LOCAL (temp ret_temp  (Vint (Int.repr (sgn x)))) SEP ()
  int ret;
  if (x <= 0) {
    if(x == 0)
      ret = 0;
    else
      ret = -1;
  }
  else
    ret = 1;
  return ret;
} 
*)

Infix "++" := app (right associativity, at level 60).
Infix "+++" := Capp (right associativity, at level 60) : aclight_scope.



Arguments Cifthenelse _ {_ _} _ _.
Arguments Csequence {_ _ } _ _.
Arguments Cloop {_ _} _ _.
Arguments list_binded_cons {_ _ _} _ {_} _.
Arguments bind_C_partial_post_ret {_ _} _.
Arguments bind_C_partial_post {_ _} _.
Arguments bind_C_full_path {_ _} _.


Notation "'GIVEN' x .. y , c " :=
  (bind_C_partial_post (fun x => .. (bind_C_partial_post (fun y => c)) ..)) (at level 65, x binder, y binder) : logic.

Notation "'GIVEN' x .. y , c " :=
  (bind_C_full_path (fun x => .. (bind_C_full_path (fun y => c)) ..)) (at level 65, x binder, y binder) : logic.

Notation "'GIVEN' x .. y , c " :=
  (bind_C_partial_post_ret (fun x => .. (bind_C_partial_post_ret (fun y => c)) ..)) (at level 65, x binder, y binder) : logic.

Notation "'EXGIVEN' x  '[[' ass ']]'  c " :=
  (Cexgiven _ (fun x => ass) _ (fun x => c)) (at level 65) : logic.

Notation "!!"  := semax_lemmas.Cnot.

Notation "{ x ; y ; .. ; z }" := (list_binded_cons x (list_binded_cons y .. (list_binded_cons z list_binded_nil) ..)) : list_scope.

Ltac cbv_conns := cbv [
  atom_conn_return
  atom_conn_returns
  atoms_conn_returns
  atom_conn_atom
  atom_conn_atoms
  atoms_conn_atoms
  atom_conn_Spre
  atom_conn_Spres
  atoms_conn_Spres
  Spost_conn_atom
  Sposts_conn_atom
  Spost_conn_return
  Sposts_conn_return
  Sposts_conn_atoms
  Sposts_conn_returns
  Spost_conn_Spre
  Sposts_conn_Spres
  add_exp_to_Spre
  add_exp_to_Spres
  add_exp_to_atom
  add_exp_to_atoms
  add_exp_to_ret_atom
  add_exp_to_ret_atoms
  add_P_to_Spre
  add_P_to_atom
  add_P_to_atom_ret
  add_Q_to_Spost
  add_Q_to_atom
  add_Q_to_atoms

  atom_conn_Cpre
  atom_conn_Cpres
  atoms_conn_Cpres
  Cpost_conn_atom
  Cposts_conn_atom
  Cposts_conn_atoms
  Cpost_conn_return
  Cposts_conn_return
  Cposts_conn_returns
  Cpost_conn_Cpre_aux
  Cpost_conn_Cpre
  Cpost_conn_Cpres
  Cposts_conn_Cpres
  add_exp_to_Cpre
  add_exp_to_Cpres
  add_P_to_Cpre
  add_P_to_Cpres
  add_P_to_Catoms
  add_P_to_Catom_rets
  add_Q_to_Cpost
  add_Q_to_Cposts
  add_Q_to_Catoms

  Smap Sconcat Sapp Capp Cmap
].

Ltac unfold_split := cbv [
  S_split_sequence
  S_split_ifthenelse
  S_split_loop
  S_split_loop_refined
  S_split_assert
  S_split_skip
  S_split_assign
  S_split_call
  S_split_set
  S_split_break
  S_split_continue
  S_split_return

  S_split

  C_split_assert
  C_split_sequence
  C_split_skip
  C_split_assign
  C_split_call
  C_split_set
  C_split_break
  C_split_continue
  C_split_return
  C_split_ifthenelse
  C_split_loop
  C_split_loop_refined

  C_split
].

Ltac unfold_ex := cbv [
  hd_of
  tl_of
  flatten_binds
  hd_assert_of_pre
  flatten_partial_pres_binds
  flatten_partial_posts_binds
  flatten_partial_post_rets_binds
  flatten_full_paths_binds
  C_split_exgiven
  add_exP_to_Cpre

  
  
C_result_proj_C_pre
C_result_proj_C_post_normal
C_result_proj_C_post_break
C_result_proj_C_post_continue
C_result_proj_C_post_return
C_result_proj_C_path
].


Ltac compute_split s_stm c_stm :=
let res0a := eval unfold s_stm in (C_split s_stm c_stm) in
let res0b := eval unfold c_stm in res0a in
let res1 := eval cbv [
  S_split_sequence
  S_split_ifthenelse
  S_split_loop
  S_split_loop_refined
  S_split_assert
  S_split_skip
  S_split_assign
  S_split_call
  S_split_set
  S_split_break
  S_split_continue
  S_split_return

  S_split

  C_split_assert
  C_split_sequence
  C_split_skip
  C_split_assign
  C_split_call
  C_split_set
  C_split_break
  C_split_continue
  C_split_return
  C_split_ifthenelse
  C_split_loop
  C_split_loop_refined

  C_split
] in res0b in
let res2 := eval cbv [
  atom_conn_return
  atom_conn_returns
  atoms_conn_returns
  atom_conn_atom
  atom_conn_atoms
  atoms_conn_atoms
  atom_conn_Spre
  atom_conn_Spres
  atoms_conn_Spres
  Spost_conn_atom
  Sposts_conn_atom
  Spost_conn_return
  Sposts_conn_return
  Sposts_conn_atoms
  Sposts_conn_returns
  Spost_conn_Spre
  Sposts_conn_Spres
  add_exp_to_Spre
  add_exp_to_Spres
  add_exp_to_atom
  add_exp_to_atoms
  add_exp_to_ret_atom
  add_exp_to_ret_atoms
  add_P_to_Spre
  add_P_to_atom
  add_P_to_atom_ret
  add_Q_to_Spost
  add_Q_to_atom
  add_Q_to_atoms

  atom_conn_Cpre
  atom_conn_Cpres
  atoms_conn_Cpres
  Cpost_conn_atom
  Cposts_conn_atom
  Cposts_conn_atoms
  Cpost_conn_return
  Cposts_conn_return
  Cposts_conn_returns
  Cpost_conn_Cpre_aux
  Cpost_conn_Cpre
  Cpost_conn_Cpres
  Cposts_conn_Cpres
  add_exp_to_Cpre
  add_exp_to_Cpres
  add_P_to_Cpre
  add_P_to_Cpres
  add_P_to_Catoms
  add_P_to_Catom_rets
  add_Q_to_Cpost
  add_Q_to_Cposts
  add_Q_to_Catoms

  Smap Sconcat Sapp Capp Cmap
] in res1 in
let res3 := eval cbv [
  hd_of
  tl_of
  flatten_binds
  hd_assert_of_pre
  flatten_partial_pres_binds
  flatten_partial_posts_binds
  flatten_partial_post_rets_binds
  flatten_full_paths_binds
  C_split_exgiven
  add_exP_to_Cpre

C_result_proj_C_pre
C_result_proj_C_post_normal
C_result_proj_C_post_break
C_result_proj_C_post_continue
C_result_proj_C_post_return
C_result_proj_C_path
  
] in res2 in
let res4 :=  eval cbv [
  atom_conn_return
  atom_conn_returns
  atoms_conn_returns
  atom_conn_atom
  atom_conn_atoms
  atoms_conn_atoms
  atom_conn_Spre
  atom_conn_Spres
  atoms_conn_Spres
  Spost_conn_atom
  Sposts_conn_atom
  Spost_conn_return
  Sposts_conn_return
  Sposts_conn_atoms
  Sposts_conn_returns
  Spost_conn_Spre
  Sposts_conn_Spres
  add_exp_to_Spre
  add_exp_to_Spres
  add_exp_to_atom
  add_exp_to_atoms
  add_exp_to_ret_atom
  add_exp_to_ret_atoms
  add_P_to_Spre
  add_P_to_atom
  add_P_to_atom_ret
  add_Q_to_Spost
  add_Q_to_atom
  add_Q_to_atoms

  atom_conn_Cpre
  atom_conn_Cpres
  atoms_conn_Cpres
  Cpost_conn_atom
  Cposts_conn_atom
  Cposts_conn_atoms
  Cpost_conn_return
  Cposts_conn_return
  Cposts_conn_returns
  Cpost_conn_Cpre_aux
  Cpost_conn_Cpre
  Cpost_conn_Cpres
  Cposts_conn_Cpres
  add_exp_to_Cpre
  add_exp_to_Cpres
  add_P_to_Cpre
  add_P_to_Cpres
  add_P_to_Catoms
  add_P_to_Catom_rets
  add_Q_to_Cpost
  add_Q_to_Cposts
  add_Q_to_Catoms

  Smap Sconcat Sapp Capp Cmap
] in res3 in
let res5 := eval simpl in res4 in    
    exact res5.

(* -------------------------- *)
(* Example Program 1: sgn(x)  *)
(* -------------------------- *)
Module sgn_verif.
Parameter _ret : ident.
Parameter _x : ident.

Definition sgn_S :=
(Ssequence Sassert
  (Ssequence
  (Sifthenelse (Ebinop Ole (Etempvar _x tint) (Econst_int (Int.repr 0) tint)
                  tint)
      (Sifthenelse (Ebinop Oeq (Etempvar _x tint)
                      (Econst_int (Int.repr 0) tint) tint)
      (Sset _ret (Econst_int (Int.repr 0) tint))
      (Sset _ret (Eunop Oneg (Econst_int (Int.repr 1) tint) tint)))
      (Sset _ret (Econst_int (Int.repr 1) tint)))
  (Sreturn (Some (Etempvar _ret tint))))).

Definition sgn_C :=
Cexgiven Z (fun x => (PROP (Int.min_signed <= x <= Int.max_signed) LOCAL (temp _x  (Vint (Int.repr x))) SEP ())) _
(fun x =>
(Csequence
(Cifthenelse 
    (Ebinop Ole (Etempvar _x tint) (Econst_int (Int.repr 0) tint) tint)
    (Cifthenelse (Ebinop Oeq (Etempvar _x tint)
                    (Econst_int (Int.repr 0) tint) tint)
    (Cset _ret (Econst_int (Int.repr 0) tint))
    (Cset _ret (Eunop Oneg (Econst_int (Int.repr 1) tint) tint)))
    (Cset _ret (Econst_int (Int.repr 1) tint)))
(Creturn (Some (Etempvar _ret tint))))
).

Print sgn_C.



(* Debug use:
*)
Goal (C_split sgn_S sgn_C) = (C_split sgn_S sgn_C).
unfold sgn_S. unfold sgn_C.
(* repeat (unfold_split;
      cbv_conns;
      unfold_ex). *)
      unfold_split;
      cbv_conns;
      unfold_ex.
Admitted.



Definition res :=
  ltac:(compute_split sgn_S sgn_C).

Print res.

End sgn_verif.


Module dummy_verif.

Definition dummy_C :=
  EXGIVEN a [[ prop (a = 1) ]]
  (Csequence
     Cskip
     (EXGIVEN b [[ prop (a = b)]]
      Cassert (prop (a = b + 1)))
  ).

Definition dummy_S :=
   (Ssequence Sassert (Ssequence Sskip (Ssequence Sassert Sassert))).

Parameter foo : forall s_res,  (C_result s_res) ->  Prop.

Goal foo _ (C_split _ dummy_C).
  unfold dummy_C.
  unfold_split.
  cbv_conns.
  unfold_ex.
  cbv_conns.
  simpl.
Admitted.


Definition res :=
  ltac:(compute_split dummy_S dummy_C).

Print res.

End dummy_verif.




(* -------------------------- *)
(* Example Program 2: 
  struct list *reverse (struct list *p)  *)
(* -------------------------- *)
Module reverse_verif.

Parameter sh : share.
Parameter p : val.
Parameter l : list val.

Parameter _p : ident.
Parameter _w : ident.
Parameter _v : ident.
Parameter _t : ident.
Parameter _list : ident.
Parameter _tail : ident.

Definition t_struct_list := Tstruct _list noattr.

Definition listrep (sh: share)
            (contents: list val) (x: val) : mpred. 
Admitted.
 (* match contents with
 | h::hs =>
              EX y:val,
                data_at sh t_struct_list (h,y) x * listrep sh hs y
 | nil => !! (x = nullval) && emp
 end. *)

Arguments listrep sh contents x : simpl never.

(* Definition reverse_S :=
(Ssequence
  (Sset _w (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
(Ssequence
  (Sset _v (Etempvar _p (tptr (Tstruct _list noattr))))
(Ssequence
  (Sloop
    (Ssequence
      (Sifthenelse (Etempvar _v (tptr (Tstruct _list noattr)))
        Sskip
        (Ssequence Sbreak Sskip))
      (Ssequence
        (Sassert)
        ((Ssequence
            (Sset _t (Efield (Ederef (Etempvar _v (tptr (Tstruct _list noattr))) (Tstruct _list noattr)) _tail (tptr (Tstruct _list noattr)))))
          (Ssequence
            (Sassign (Efield (Ederef (Etempvar _v (tptr (Tstruct _list noattr))) (Tstruct _list noattr)) _tail (tptr (Tstruct _list noattr))) (Etempvar _w (tptr (Tstruct _list noattr))))
          (Ssequence
            (Sset _w (Etempvar _v (tptr (Tstruct _list noattr))))
          (Ssequence 
            (Sset _v (Etempvar _t (tptr (Tstruct _list noattr))))
            Sskip))))))
    Sskip)
(Ssequence
  (Sreturn (Some (Etempvar _w (tptr (Tstruct _list noattr)))))
  Sskip)))). *)

Definition reverse_S :=
(Ssequence 
(Ssequence 
  Sassert 
  (Sset _w (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))))
(Ssequence 
  (Sset _v (Etempvar _p (tptr (Tstruct _list noattr))))
(Ssequence
  (Sloop
    (Ssequence 
        Sassert
      (Ssequence 
        Sassert
      (Ssequence 
        Sassert
      (Ssequence 
        Sassert
      (Ssequence
        (Sifthenelse (Etempvar _v (tptr (Tstruct _list noattr))) Sskip
            (Ssequence Sbreak Sskip))
      (Ssequence Sassert
      (Ssequence Sassert
      (Ssequence Sassert
      (
      (Ssequence
        (Sset _t (Efield (Ederef (Etempvar _v (tptr (Tstruct _list noattr))) (Tstruct _list noattr)) _tail (tptr (Tstruct _list noattr))))
      (Ssequence
        (Sassign (Efield (Ederef (Etempvar _v (tptr (Tstruct _list noattr))) (Tstruct _list noattr)) _tail (tptr (Tstruct _list noattr))) (Etempvar _w (tptr (Tstruct _list noattr))))
      (Ssequence
        (Sset _w (Etempvar _v (tptr (Tstruct _list noattr))))
      (Ssequence
        (Sset _v (Etempvar _t (tptr (Tstruct _list noattr)))) 
        Sskip)))))))))))))
    Sskip)
  (Ssequence 
    (Sreturn (Some (Etempvar _w (tptr (Tstruct _list noattr)))))
    (Ssequence Sskip Sassert)))))
.


(* Definition foo_C :=
  EXGIVEN a [[ PROP (a = 1) LOCAL () SEP () ]]
  EXGIVEN b [[ PROP (a = 1 /\ b = 2) LOCAL () SEP () ]] Cskip.

Print foo_C. *)


Definition reverse_C :=
(Csequence
(Csequence
  (Cassert (PROP  (writable_share sh)
            LOCAL (temp _p p)
            SEP   (listrep sh l p)))
  (Cset _w (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))))
(Csequence
  (Cset _v (Etempvar _p (tptr (Tstruct _list noattr))))
(Csequence
  (Cloop
    (EXGIVEN w [[ EX v l1 l2,
                  PROP  (l = rev l1 ++ l2)
                  LOCAL (temp _w w; temp _v v)
                  SEP   (listrep sh l1 w; listrep sh l2 v) ]]
     EXGIVEN v [[ EX l1 l2,
                  PROP  (l = rev l1 ++ l2)
                  LOCAL (temp _w w; temp _v v)
                  SEP   (listrep sh l1 w; listrep sh l2 v) ]]
     EXGIVEN l1 [[ EX l2,
                  PROP  (l = rev l1 ++ l2)
                  LOCAL (temp _w w; temp _v v)
                  SEP   (listrep sh l1 w; listrep sh l2 v) ]]
     EXGIVEN l2 [[ PROP  (l = rev l1 ++ l2)
                  LOCAL (temp _w w; temp _v v)
                  SEP   (listrep sh l1 w; listrep sh l2 v) ]]
     Csequence
      (Cifthenelse (Etempvar _v (tptr (Tstruct _list noattr)))
        Cskip
        (Csequence Cbreak Cskip))
      (EXGIVEN t [[ EX x l2',
                      PROP  (l2 = x :: l2')
                      LOCAL (temp _w w; temp _v v)
                      SEP   (
                        (* data_at sh t_struct_list (x, t) v; *)
                            listrep sh l1 w; listrep sh l2' t)  ]]
      EXGIVEN x [[ EX l2',
                      PROP  (l2 = x :: l2')
                      LOCAL (temp _w w; temp _v v)
                      SEP   (
                        (* data_at sh t_struct_list (x, t) v; *)
                            listrep sh l1 w; listrep sh l2' t)  ]]
      EXGIVEN l2' [[  PROP  (l2 = x :: l2')
                      LOCAL (temp _w w; temp _v v)
                      SEP   (
                        (* data_at sh t_struct_list (x, t) v; *)
                            listrep sh l1 w; listrep sh l2' t)  ]]
      
        ((Csequence
            (Cset _t (Efield (Ederef (Etempvar _v (tptr (Tstruct _list noattr))) (Tstruct _list noattr)) _tail (tptr (Tstruct _list noattr)))))
          (Csequence
            (Cassign (Efield (Ederef (Etempvar _v (tptr (Tstruct _list noattr))) (Tstruct _list noattr)) _tail (tptr (Tstruct _list noattr))) (Etempvar _w (tptr (Tstruct _list noattr))))
          (Csequence
            (Cset _w (Etempvar _v (tptr (Tstruct _list noattr))))
          (Csequence 
            (Cset _v (Etempvar _t (tptr (Tstruct _list noattr))))
            Cskip))))))
    Cskip)
(Csequence
  (Creturn (Some (Etempvar _w (tptr (Tstruct _list noattr)))))
(Csequence
  Cskip
  (Cassert (EX q: val,
            PROP  ()
            LOCAL (temp ret_temp q)
            SEP   (listrep sh (rev l) q)))
  ))))).

Parameter foo : forall s_res,  (C_result s_res) ->  Prop.

Goal foo _ (C_split reverse_S reverse_C).
  unfold reverse_S. unfold reverse_C.

unfold_split.
cbv_conns.
unfold_ex.
cbv_conns.
Admitted.


Definition res :=
  ltac:(compute_split reverse_S reverse_C).

Print res.

End reverse_verif.

(* 
All split functions:

atom_conn_return
atom_conn_returns
atoms_conn_returns
atom_conn_atom
atom_conn_atoms
atoms_conn_atoms
atom_conn_Spre
atom_conn_Spres
atoms_conn_Spres
Spost_conn_atom
Sposts_conn_atom
Spost_conn_return
Sposts_conn_return
Sposts_conn_atoms
Sposts_conn_returns
Spost_conn_Spre
Sposts_conn_Spres
add_exp_to_Spre
add_exp_to_Spres
add_exp_to_atom
add_exp_to_atoms
add_exp_to_ret_atom
add_exp_to_ret_atoms
add_P_to_Spre
add_P_to_atom
add_P_to_atom_ret
add_Q_to_Spost
add_Q_to_atom
add_Q_to_atoms

atom_conn_Cpre
atom_conn_Cpres
atoms_conn_Cpres
Cpost_conn_atom
Cposts_conn_atom
Cposts_conn_atoms
Cpost_conn_return
Cposts_conn_return
Cposts_conn_returns
Cpost_conn_Cpre_aux
Cpost_conn_Cpre
Cpost_conn_Cpres
Cposts_conn_Cpres
add_exp_to_Cpre
add_exp_to_Cpres
add_P_to_Cpre
add_P_to_Cpres
add_P_to_Catoms
add_P_to_Catom_rets
add_Q_to_Cpost
add_Q_to_Cposts
add_Q_to_Catoms

S_split_sequence
S_split_ifthenelse
S_split_loop
S_split_loop_refined
S_split_assert
S_split_skip
S_split_assign
S_split_call
S_split_set
S_split_break
S_split_continue
S_split_return

S_split

hd_of
tl_of
flatten_binds
hd_assert_of_pre
flatten_partial_pres_binds
flatten_partial_posts_binds
flatten_partial_post_rets_binds
flatten_full_paths_binds

C_result_proj_C_pre
C_result_proj_C_post_normal
C_result_proj_C_post_break
C_result_proj_C_post_continue
C_result_proj_C_post_return
C_result_proj_C_path

C_split_assert
C_split_sequence
add_exP_to_Cpre
C_split_exgiven
C_split_skip
C_split_assign
C_split_call
C_split_set
C_split_break
C_split_continue
C_split_return
C_split_ifthenelse
C_split_loop
C_split_loop_refined



 *)
