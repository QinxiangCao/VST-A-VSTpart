From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Require Import CSplit.AClightFunc.
Require Import CSplit.semanticsFunc.
Require Import CSplit.AClightNotations.
Require Import FloydSeq.proofauto.


Local Open Scope Z_scope.
Import AClightNotations.
Require Import cprogs.reverse_prog.
Require Import cprogs.reverse_def.
Require Import CSplit.strong.

Module Info.
  Definition version := "3.6"%string.
  Definition build_number := ""%string.
  Definition build_tag := ""%string.
  Definition arch := "x86"%string.
  Definition model := "32sse2"%string.
  Definition abi := "macosx"%string.
  Definition bitsize := 32.
  Definition big_endian := false.
  Definition source_file := "testprogs/reverse.c"%string.
  Definition normalized := true.
End Info.

Definition f_reverse_spec_annotation :=
  ANNOTATION_WITH  sh p l, ((
            PROP  (writable_share sh)
	    LOCAL (temp _p p)
	    SEP   (listrep sh l p)),
  (
          EX q: val,
	    PROP  ()
	    LOCAL (temp ret_temp q)
	    SEP   (listrep sh (rev l) q))).

Definition f_reverse_spec_complex :=
  ltac:(
    uncurry_funcspec f_reverse_spec_annotation).

Definition f_reverse_funsig: funsig :=
  (((_p, (tptr (Tstruct _list noattr))) :: nil),
   (tptr (Tstruct _list noattr))).

Definition reverse_spec :=
  ltac:(make_funcspec _reverse f_reverse_funsig f_reverse_spec_complex).

Parameter (sh:share) (p:val) (l: list val).

Definition f_reverse_hint :=
(
  (Csequence
    Cskip
    (Csequence
      Cskip
      (Csequence
        (Cset _w (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
        (Csequence
          (Cset _v (Etempvar _p (tptr (Tstruct _list noattr))))
          (Csequence
            (Cloop
              (Csequence
                (Cassert (
       (EX w v l1 l2,
          PROP  (l = rev l1 ++ l2)
	  LOCAL (temp _w w; temp _v v)
	  SEP   (listrep sh l1 w; listrep sh l2 v))%assert))
                (EXGIVEN w
                  [[((EX v l1 l2,
          PROP  (l = rev l1 ++ l2)
	  LOCAL (temp _w w; temp _v v)
	  SEP   (listrep sh l1 w; listrep sh l2 v))%assert)]] 
                  (EXGIVEN v
                    [[((EX l1 l2,
          PROP  (l = rev l1 ++ l2)
	  LOCAL (temp _w w; temp _v v)
	  SEP   (listrep sh l1 w; listrep sh l2 v))%assert)]] 
                    (EXGIVEN l1
                      [[((EX l2,
          PROP  (l = rev l1 ++ l2)
	  LOCAL (temp _w w; temp _v v)
	  SEP   (listrep sh l1 w; listrep sh l2 v))%assert)]] 
                      (EXGIVEN l2
                        [[((PROP  (l = rev l1 ++ l2)
	  LOCAL (temp _w w; temp _v v)
	  SEP   (listrep sh l1 w; listrep sh l2 v))%assert)]] 
                        (Csequence
                          (Cifthenelse (Etempvar _v (tptr (Tstruct _list noattr)))
                            Cskip
                            (Csequence Cbreak Cskip))
                          (Csequence
                            (Cassert (
         (EX t x l2',
	    PROP  (l2 = x :: l2')
	    LOCAL (temp _w w; temp _v v)
	    SEP   (data_at sh t_struct_list (x, t) v;
	           listrep sh l1 w; listrep sh l2' t))%assert))
                            (EXGIVEN t
                              [[((EX x l2',
	    PROP  (l2 = x :: l2')
	    LOCAL (temp _w w; temp _v v)
	    SEP   (data_at sh t_struct_list (x, t) v;
	           listrep sh l1 w; listrep sh l2' t))%assert)]] 
                              (EXGIVEN x
                                [[((EX l2',
	    PROP  (l2 = x :: l2')
	    LOCAL (temp _w w; temp _v v)
	    SEP   (data_at sh t_struct_list (x, t) v;
	           listrep sh l1 w; listrep sh l2' t))%assert)]] 
                                (EXGIVEN l2'
                                  [[((PROP  (l2 = x :: l2')
	    LOCAL (temp _w w; temp _v v)
	    SEP   (data_at sh t_struct_list (x, t) v;
	           listrep sh l1 w; listrep sh l2' t))%assert)]] 
                                  (Csequence
                                    (Cset _t
                                      (Efield
                                        (Ederef
                                          (Etempvar _v (tptr (Tstruct _list noattr)))
                                          (Tstruct _list noattr)) _tail
                                        (tptr (Tstruct _list noattr))))
                                    (Csequence
                                      (Cassign
                                        (Efield
                                          (Ederef
                                            (Etempvar _v (tptr (Tstruct _list noattr)))
                                            (Tstruct _list noattr)) _tail
                                          (tptr (Tstruct _list noattr)))
                                        (Etempvar _w (tptr (Tstruct _list noattr))))
                                      (Csequence
                                        (Cset _w
                                          (Etempvar _v (tptr (Tstruct _list noattr))))
                                        (Csequence
                                          (Cset _v
                                            (Etempvar _t (tptr (Tstruct _list noattr))))
                                          Cskip))))))))))))))
              Cskip)
            (Csequence
              (Creturn (Some (Etempvar _w (tptr (Tstruct _list noattr)))))
              Cskip))))))).

Definition Gprog : funspecs :=
  ltac:(with_library prog [reverse_spec]).

(* Definition f_reverse_hint_split :=
  ltac:(compute_split f_reverse_hint).

Print f_reverse_hint_split. *)
(* 

f_reverse_hint_split = 
{|
C_pre := {mk_C_partial_pre
	        [inr (Aset _w ((tptr tvoid) (0))%expr); inr (Aset _v (_p)%expr)]
            (ANNOTATION_WITH a : environ,
             (EX (x x0 : val) (x1 x2 : list val),
              (PROP (l = rev x1 ++ x2)
               LOCAL (temp _w x; temp _v x0)
               SEP (listrep sh x1 x; listrep sh x2 x0)) a))};
C_path := {GIVEN (a a0 : val) (a1 a2 : list val) (a3 a4 : val),
           mk_C_full_path
             (ANNOTATION_WITH a5 : environ,
              (EX x : list val,
               (PROP (a2 = a4 :: x)
                LOCAL (temp _w a; temp _v a0)
                SEP (data_at sh t_struct_list (a4, a3) a0; 
                listrep sh a1 a; listrep sh x a3)) a5)) []
             (ANNOTATION_WITH a5 : environ,
              (EX x : list val,
               (PROP (a2 = a4 :: x)
                LOCAL (temp _w a; temp _v a0)
                SEP (data_at sh t_struct_list (a4, a3) a0; 
                listrep sh a1 a; listrep sh x a3)) a5));
          GIVEN (a a0 : val) (a1 a2 : list val) (a3 : val),
          mk_C_full_path
            (ANNOTATION_WITH a4 : environ,
             (EX (x : val) (x0 : list val),
              (PROP (a2 = x :: x0)
               LOCAL (temp _w a; temp _v a0)
               SEP (data_at sh t_struct_list (x, a3) a0; 
               listrep sh a1 a; listrep sh x0 a3)) a4)) []
            (ANNOTATION_WITH a4 : environ,
             (EX (x : val) (x0 : list val),
              (PROP (a2 = x :: x0)
               LOCAL (temp _w a; temp _v a0)
               SEP (data_at sh t_struct_list (x, a3) a0; 
               listrep sh a1 a; listrep sh x0 a3)) a4));
          GIVEN (a a0 : val) (a1 a2 : list val),
          mk_C_full_path
            (ANNOTATION_WITH a3 : environ,
             (EX (x x0 : val) (x1 : list val),
              (PROP (a2 = x0 :: x1)
               LOCAL (temp _w a; temp _v a0)
               SEP (data_at sh t_struct_list (x0, x) a0; 
               listrep sh a1 a; listrep sh x1 x)) a3)) []
            (ANNOTATION_WITH a3 : environ,
             (EX (x x0 : val) (x1 : list val),
              (PROP (a2 = x0 :: x1)
               LOCAL (temp _w a; temp _v a0)
               SEP (data_at sh t_struct_list (x0, x) a0; 
               listrep sh a1 a; listrep sh x1 x)) a3));
          GIVEN (a a0 : val) (a1 a2 : list val),
          mk_C_full_path
            (PROP (l = rev a1 ++ a2)
             LOCAL (temp _w a; temp _v a0)
             SEP (listrep sh a1 a; listrep sh a2 a0)) [
            inl (true, (_v)%expr)]
            (ANNOTATION_WITH a3 : environ,
             (EX (x x0 : val) (x1 : list val),
              (PROP (a2 = x0 :: x1)
               LOCAL (temp _w a; temp _v a0)
               SEP (data_at sh t_struct_list (x0, x) a0; 
               listrep sh a1 a; listrep sh x1 x)) a3));
          GIVEN (a a0 : val) (a1 : list val),
          mk_C_full_path
            (ANNOTATION_WITH a2 : environ,
             (EX x : list val,
              (PROP (l = rev a1 ++ x)
               LOCAL (temp _w a; temp _v a0)
               SEP (listrep sh a1 a; listrep sh x a0)) a2)) []
            (ANNOTATION_WITH a2 : environ,
             (EX x : list val,
              (PROP (l = rev a1 ++ x)
               LOCAL (temp _w a; temp _v a0)
               SEP (listrep sh a1 a; listrep sh x a0)) a2));
          GIVEN a a0 : val,
          mk_C_full_path
            (ANNOTATION_WITH a1 : environ,
             (EX x x0 : list val,
              (PROP (l = rev x ++ x0)
               LOCAL (temp _w a; temp _v a0)
               SEP (listrep sh x a; listrep sh x0 a0)) a1)) []
            (ANNOTATION_WITH a1 : environ,
             (EX x x0 : list val,
              (PROP (l = rev x ++ x0)
               LOCAL (temp _w a; temp _v a0)
               SEP (listrep sh x a; listrep sh x0 a0)) a1));
          GIVEN a : val,
          mk_C_full_path
            (ANNOTATION_WITH a0 : environ,
             (EX (x : val) (x0 x1 : list val),
              (PROP (l = rev x0 ++ x1)
               LOCAL (temp _w a; temp _v x)
               SEP (listrep sh x0 a; listrep sh x1 x)) a0)) []
            (ANNOTATION_WITH a0 : environ,
             (EX (x : val) (x0 x1 : list val),
              (PROP (l = rev x0 ++ x1)
               LOCAL (temp _w a; temp _v x)
               SEP (listrep sh x0 a; listrep sh x1 x)) a0));
          mk_C_full_path
            (ANNOTATION_WITH a : environ,
             (EX (x x0 : val) (x1 x2 : list val),
              (PROP (l = rev x1 ++ x2)
               LOCAL (temp _w x; temp _v x0)
               SEP (listrep sh x1 x; listrep sh x2 x0)) a)) []
            (ANNOTATION_WITH a : environ,
             (EX (x x0 : val) (x1 x2 : list val),
              (PROP (l = rev x1 ++ x2)
               LOCAL (temp _w x; temp _v x0)
               SEP (listrep sh x1 x; listrep sh x2 x0)) a));
          GIVEN (a a0 : val) (a1 a2 : list val) (a3 a4 : val)
          (a5 : list val),
          mk_C_full_path
            (PROP (a2 = a4 :: a5)
             LOCAL (temp _w a; temp _v a0)
             SEP (data_at sh t_struct_list (a4, a3) a0; 
             listrep sh a1 a; listrep sh a5 a3))
            [inr (Aset _t (_v -> _tail)%expr);
            inr (Aassign (_v -> _tail)%expr (_w)%expr);
            inr (Aset _w (_v)%expr); inr (Aset _v (_t)%expr)]
            (ANNOTATION_WITH a6 : environ,
             (EX (x x0 : val) (x1 x2 : list val),
              (PROP (l = rev x1 ++ x2)
               LOCAL (temp _w x; temp _v x0)
               SEP (listrep sh x1 x; listrep sh x2 x0)) a6))};
C_post_normal := {};
C_post_break := {};
C_post_continue := {};
C_post_return := {GIVEN (a a0 : val) (a1 a2 : list val),
                  mk_C_partial_post_ret
                    (PROP (l = rev a1 ++ a2)
                     LOCAL (temp _w a; temp _v a0)
                     SEP (listrep sh a1 a; listrep sh a2 a0))
                    [inl (false, (_v)%expr)] (Some (_w)%expr)} |}
     : C_result_rec
         [mk_S_partial_pre
            [inr (Aset _w ((tptr tvoid) (0))%expr); inr (Aset _v (_p)%expr)]]
         [mk_S_full_path []; mk_S_full_path []; mk_S_full_path [];
         mk_S_full_path [inl (true, (_v)%expr)]; mk_S_full_path [];
         mk_S_full_path []; mk_S_full_path []; mk_S_full_path [];
         mk_S_full_path
           [inr (Aset _t (_v -> _tail)%expr);
           inr (Aassign (_v -> _tail)%expr (_w)%expr);
           inr (Aset _w (_v)%expr); inr (Aset _v (_t)%expr)]] [] [] []
         [mk_S_partial_post_ret [inl (false, (_v)%expr)] (Some (_w)%expr)] []
         [] [] []

*)

Parameter (Delta_specs: PTree.t funspec).

Definition reverse_delta :=
  (mk_tycontext
     (PTree.Node
        (PTree.Node
           (PTree.Node
              (PTree.Node PTree.Leaf None
                 (PTree.Node PTree.Leaf None
                    (PTree.Node PTree.Leaf
                       (Some
                          (Tpointer
                             (Tstruct 2%positive
                                {|
                                attr_volatile := false;
                                attr_alignas := None |})
                             {|
                             attr_volatile := false;
                             attr_alignas := None |}))
                       PTree.Leaf))) None PTree.Leaf) None
           (PTree.Node
              (PTree.Node PTree.Leaf None
                 (PTree.Node PTree.Leaf None
                    (PTree.Node PTree.Leaf
                       (Some
                          (Tpointer
                             (Tstruct 2%positive
                                {|
                                attr_volatile := false;
                                attr_alignas := None |})
                             {|
                             attr_volatile := false;
                             attr_alignas := None |}))
                       PTree.Leaf))) None PTree.Leaf)) None
        (PTree.Node
           (PTree.Node
              (PTree.Node PTree.Leaf None
                 (PTree.Node PTree.Leaf None
                    (PTree.Node PTree.Leaf
                       (Some
                          (Tpointer
                             (Tstruct 2%positive
                                {|
                                attr_volatile := false;
                                attr_alignas := None |})
                             {|
                             attr_volatile := false;
                             attr_alignas := None |}))
                       PTree.Leaf))) None PTree.Leaf) None
           (PTree.Node
              (PTree.Node PTree.Leaf None
                 (PTree.Node PTree.Leaf None
                    (PTree.Node PTree.Leaf
                       (Some
                          (Tpointer
                             (Tstruct 2%positive
                                {|
                                attr_volatile := false;
                                attr_alignas := None |})
                             {|
                             attr_volatile := false;
                             attr_alignas := None |}))
                       PTree.Leaf))) None PTree.Leaf)))
     PTree.Leaf
     (Tpointer
        (Tstruct 2%positive
           {| attr_volatile := false; attr_alignas := None |})
        {| attr_volatile := false; attr_alignas := None |})
     PTree.Leaf Delta_specs PTree.Leaf).


(* Lemma append_verif: 
  semax_body Vprog Gprog f_reverse reverse_spec.
Proof.
  start_function.
  unfold Delta. unfold abbreviate.
  Check Delta_specs0.
  Print Delta_specs0. *)


  Global Arguments Cifthenelse _ {_ _} _ _.
  Global Arguments Csequence {_ _ } _ _.
  Global Arguments Cloop {_ _} _ _.
  Global Arguments list_binded_cons {_ _ _} _ {_} _.
  Global Arguments bind_C_partial_post_ret {_ _} _.
  Global Arguments bind_C_partial_post {_ _} _.
  Global Arguments bind_C_full_path {_ _} _.



Notation "'GIVEN' x .. y , c " :=
  (bind_C_full_path (fun x => .. (bind_C_full_path (fun y => c)) ..)) (at level 65, x binder, y binder) : logic.


(* Check ((GIVEN (a a0 : val) (a1 a2 : list val) (a3 a4 : val)
(a5 : list val),
mk_C_full_path
  (PROP (a2 = a4 :: a5)
   LOCAL (temp _w a; temp _v a0)
   SEP (data_at sh t_struct_list (a4, a3) a0; 
   listrep sh a1 a; listrep sh a5 a3))
  [inr (Aset _t (Efield
  (Ederef
    (Etempvar _v (tptr (Tstruct _list noattr)))
    (Tstruct _list noattr)) _tail
  (tptr (Tstruct _list noattr)))%expr);
  inr (Aassign (Efield
  (Ederef
    (Etempvar _v (tptr (Tstruct _list noattr)))
    (Tstruct _list noattr)) _tail
  (tptr (Tstruct _list noattr)))%expr (Etempvar _w (tptr (Tstruct _list noattr)))%expr);
  inr (Aset _w (Etempvar _v (tptr (Tstruct _list noattr)))%expr); inr (Aset _v (Etempvar _t (tptr (Tstruct _list noattr)))%expr)]
  (ANNOTATION_WITH a6 : environ,
   (EX (x x0 : val) (x1 x2 : list val),
    (PROP (l = rev x1 ++ x2)
     LOCAL (temp _w x; temp _v x0)
     SEP (listrep sh x1 x; listrep sh x2 x0)) a6)))). *)

Parameter Espec : OracleKind.


Instance CS : compspecs. make_compspecs prog. Defined.

Require Import FloydSeq.client_lemmas. (* Intros tactic *)

Goal @path_to_semax CS Espec reverse_delta _
(GIVEN (a a0 : val) (a1 a2 : list val) (a3 a4 : val)
          (a5 : list val),
          mk_C_full_path
            (PROP (l = rev a1 ++ a2 ; a2 = a4 :: a5; (writable_share sh))
             LOCAL (temp _w a; temp _v a0)
             SEP (data_at sh t_struct_list (a4, a3) a0; 
             listrep sh a1 a; listrep sh a5 a3))
            [inr (Aset _t (Efield
            (Ederef
              (Etempvar _v (tptr (Tstruct _list noattr)))
              (Tstruct _list noattr)) _tail
            (tptr (Tstruct _list noattr)))%expr);
            inr (Aassign (Efield
            (Ederef
              (Etempvar _v (tptr (Tstruct _list noattr)))
              (Tstruct _list noattr)) _tail
            (tptr (Tstruct _list noattr)))%expr (Etempvar _w (tptr (Tstruct _list noattr)))%expr);
            inr (Aset _w (Etempvar _v (tptr (Tstruct _list noattr)))%expr); inr (Aset _v (Etempvar _t (tptr (Tstruct _list noattr)))%expr)]
            (
             (EX (x x0 : val) (x1 x2 : list val),
              (PROP (l = rev x1 ++ x2)
               LOCAL (temp _w x; temp _v x0)
               SEP (listrep sh x1 x; listrep sh x2 x0))))).
Proof.
  repeat (hnf;intros). Intros.
  unfold path_to_statement.
 ensure_normal_ret_assert.


 (* FORWARD 1 *)
 check_precondition;
 eapply semax_seq'.
 {
   
   let T1 := fresh "T1" in evar (T1: PTree.t val);
   let T2 := fresh "T2" in evar (T2: PTree.t (type * val));
   let G := fresh "GV" in evar (G: option globals);
   let LOCAL2PTREE := fresh "LOCAL2PTREE" in
   assert (local2ptree [temp _w a; temp _v a0] = (T1, T2, nil, G)) as LOCAL2PTREE;
   [subst T1 T2 G; prove_local2ptree |]
   
.

   first [ load_tac_with_hint LOCAL2PTREE | load_tac_no_hint LOCAL2PTREE | SEP_type_contradict LOCAL2PTREE Delta e R | hint_msg LOCAL2PTREE Delta e].
 }

 fwd_result.
Intros.
        (* abbreviate_semax. *)
        try (fwd_skip; try_clean_up_stackframe) .



 (* FORWARD 2 *)
 check_precondition;
 eapply semax_seq'.
 {

  ensure_open_normal_ret_assert.
  (* hoist_later_in_pre; *)
  (* sc_set_load_store.store_tac. *)
   
  
  
  (* Ltac store_tac :=
  match goal with
  | |- semax ?Delta (|> (PROPx ?P (LOCALx ?Q (SEPx ?R)))) (Sassign ?e1 ?e2) _ => *)
    check_expression_by_value (Efield
    (Ederef (Etempvar _v (tptr (Tstruct _list noattr)))
       (Tstruct _list noattr)) _tail (tptr (Tstruct _list noattr)));
    let T1 := fresh "T1" in evar (T1: PTree.t val);
    let T2 := fresh "T2" in evar (T2: PTree.t (type * val));
    let G := fresh "GV" in evar (G: option globals);
    let LOCAL2PTREE := fresh "LOCAL2PTREE" in
    assert (local2ptree [temp _t a3; temp _w a; temp _v a0] = (T1, T2, nil, G)) as LOCAL2PTREE;
    [subst T1 T2 G; prove_local2ptree |];
    first [ store_tac_with_hint LOCAL2PTREE | store_tac_no_hint LOCAL2PTREE | SEP_type_contradict LOCAL2PTREE Delta e1 R | hint_msg LOCAL2PTREE Delta e1];
    clear T1 T2 LOCAL2PTREE
  (* end. *)
  .
 }


 fwd_result.
Intros.
        (* abbreviate_semax. *)
        try (fwd_skip; try_clean_up_stackframe) .



 (* FORWARD 3 *)
 check_precondition;
 eapply semax_seq'.
 {


  ensure_normal_ret_assert;
  (* hoist_later_in_pre; *)
 (* match goal with
 | |- semax ?Delta (|> (PROPx ?P (LOCALx ?Q (SEPx ?R)))) (Sset _ ?e) _ => *)
        eapply semax_PTree_set;
        [ reflexivity
        | reflexivity
        | check_cast_assignment
        | solve_msubst_eval; simplify_casts; reflexivity
        | first [ quick_typecheck3
                | pre_entailer; try solve [entailer!] ] ].

 }
 fwd_result.
Intros.
        (* abbreviate_semax. *)
        try (fwd_skip; try_clean_up_stackframe) .


 (* FORWARD 4 *)
 check_precondition;
 eapply semax_seq'.
 {

  ensure_normal_ret_assert;
  (* hoist_later_in_pre; *)
 (* match goal with
 | |- semax ?Delta (|> (PROPx ?P (LOCALx ?Q (SEPx ?R)))) (Sset _ ?e) _ => *)
        eapply semax_PTree_set;
        [ reflexivity
        | reflexivity
        | check_cast_assignment
        | solve_msubst_eval; simplify_casts; reflexivity
        | first [ quick_typecheck3
                | pre_entailer; try solve [entailer!] ] ].

 }
 fwd_result.

 fwd_skip. unfold normal_split_assert. unfold RA_normal.
 entailer.

 Exists a0 a3 (a4 :: a1) a5.
 {
   apply andp_right.
   + apply prop_right. repeat split;auto. rewrite H. simpl.
   rewrite <- app_assoc. simpl. reflexivity.
   + unfold listrep at 3. fold listrep. Exists a. entailer!.
 }
Qed.
