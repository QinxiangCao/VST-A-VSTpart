From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Require Import CSplit.AClightFunc.
Require Import CSplit.semanticsFunc.
Require Import utils.AClightNotations.
Require Import FloydSeq.proofauto.
Require Import FloydSeq.client_lemmas.
Local Open Scope Z_scope.
Import AClightNotations.

Module Info.
  Definition version := "3.6"%string.
  Definition build_number := ""%string.
  Definition build_tag := ""%string.
  Definition arch := "x86"%string.
  Definition model := "32sse2"%string.
  Definition abi := "macosx"%string.
  Definition bitsize := 32.
  Definition big_endian := false.
  Definition source_file := "testprogs/reverse_noinv.c"%string.
  Definition normalized := true.
End Info.

Require Import cprogs.reverse_prog.
Require Import cprogs.reverse_def.

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
  ltac:(uncurry_funcspec f_reverse_spec_annotation).

Definition f_reverse_funsig: funsig :=
  (((_p, (tptr (Tstruct _list noattr))) :: nil),
   (tptr (Tstruct _list noattr))).

Definition reverse_spec :=
  ltac:(make_funcspec _reverse f_reverse_funsig f_reverse_spec_complex).

Definition f_reverse_hint :=
(EXGIVEN l
  [[(EX p sh, 
            PROP  (writable_share sh)
	    LOCAL (temp _p p)
	    SEP   (listrep sh l p))]] 
  (EXGIVEN p
    [[(EX sh, 
            PROP  (writable_share sh)
	    LOCAL (temp _p p)
	    SEP   (listrep sh l p))]] 
    (EXGIVEN sh
      [[(
            PROP  (writable_share sh)
	    LOCAL (temp _p p)
	    SEP   (listrep sh l p))]] 
      (Csequence
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
	    PROP  (l = rev l1 ++ l2; l2 = x :: l2'; writable_share sh)
	    LOCAL (temp _w w; temp _v v)
	    SEP   (data_at sh t_struct_list (x, t) v;
	           listrep sh l1 w; listrep sh l2' t))%assert))
                              (EXGIVEN t
                                [[((EX x l2',
	    PROP  (l = rev l1 ++ l2; l2 = x :: l2'; writable_share sh)
	    LOCAL (temp _w w; temp _v v)
	    SEP   (data_at sh t_struct_list (x, t) v;
	           listrep sh l1 w; listrep sh l2' t))%assert)]] 
                                (EXGIVEN x
                                  [[((EX l2',
	    PROP  (l = rev l1 ++ l2; l2 = x :: l2'; writable_share sh)
	    LOCAL (temp _w w; temp _v v)
	    SEP   (data_at sh t_struct_list (x, t) v;
	           listrep sh l1 w; listrep sh l2' t))%assert)]] 
                                  (EXGIVEN l2'
                                    [[((PROP  (l = rev l1 ++ l2; l2 = x :: l2'; writable_share sh)
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
                Cskip))))
        (Cassert (
          EX q: val,
	    PROP  ()
	    LOCAL (temp ret_temp q)
	    SEP   (listrep sh (rev l) q))))))).
  
Definition Gprog : funspecs :=
  ltac:(with_library prog [reverse_spec]).

Time Definition f_reverse_hint_split :=
  ltac:(compute_split f_reverse_hint).


