From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.

Require Import cprogs.append_def.
Require Import cprogs.append_prog.


Local Open Scope Z_scope.
Require Import CSplit.AClightNotations.
Import AClightNotations.
Require Import CSplit.AClight.

Module Info.
  Definition version := "3.6"%string.
  Definition build_number := ""%string.
  Definition build_tag := ""%string.
  Definition arch := "x86"%string.
  Definition model := "64"%string.
  Definition abi := "macosx"%string.
  Definition bitsize := 64.
  Definition big_endian := false.
  Definition source_file := "testprogs/append.c"%string.
  Definition normalized := true.
End Info.

Definition f_append_spec_annotation :=
  ANNOTATION_WITH  sh x y s1 s2, ((
       PROP(writable_share sh)
       LOCAL (temp _x x; temp _y y)
       SEP (listrep sh s1 x; listrep sh s2 y)),
  (
      EX r: val,
       PROP()
       LOCAL(temp ret_temp r)
       SEP (listrep sh (s1++s2) r))).

Definition f_append_spec_complex :=
  ltac:(uncurry_funcspec f_append_spec_annotation).

Definition f_append_funsig: funsig :=
  (((_x, (tptr (Tstruct _list noattr))) ::
    (_y, (tptr (Tstruct _list noattr))) :: nil),
   (tptr (Tstruct _list noattr))).

Definition append_spec :=
  ltac:(make_funcspec _append f_append_funsig f_append_spec_complex).



  Parameter sh: share.
  Parameter x y: val.
  Parameter s1 s2: list val.


Global Arguments Cifthenelse _ {_ _} _ _.
Global Arguments Csequence {_ _ } _ _.
Global Arguments Cloop {_ _} _ _.
Global Arguments list_binded_cons {_ _ _} _ {_} _.
Global Arguments bind_C_partial_post_ret {_ _} _.
Global Arguments bind_C_partial_post {_ _} _.
Global Arguments bind_C_full_path {_ _} _.

Global Arguments C_split {_} _.

Import AClightFunc.
Locate C_statement.

Definition f_append_hint :=
(
  (Csequence
    Cskip
    (Csequence
      Cskip
      (Csequence
        (Cifthenelse (Ebinop Oeq (Etempvar _x (tptr (Tstruct _list noattr)))
                       (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                       tint)
          (Csequence
            (Creturn (Some (Etempvar _y (tptr (Tstruct _list noattr)))))
            Cskip)
          (Csequence
            (Cset _t (Etempvar _x (tptr (Tstruct _list noattr))))
            (Csequence
              (Cassert ( (EX a s1b, (
        (PROP (s1 = a :: s1b)
         LOCAL (temp _t x; temp _x x; temp _y y)
         SEP (listrep sh s1 x; listrep sh s2 y))))))
              (EXGIVEN a
                [[((EX s1b, (
        (PROP (s1 = a :: s1b)
         LOCAL (temp _t x; temp _x x; temp _y y)
         SEP (listrep sh s1 x; listrep sh s2 y)))))]] 
                (EXGIVEN s1b
                  [[(((
        (PROP (s1 = a :: s1b)
         LOCAL (temp _t x; temp _x x; temp _y y)
         SEP (listrep sh s1 x; listrep sh s2 y)))))]] 
                  (Csequence
                    (Cassert ( (EX u,
        (PROP ()
         LOCAL (temp _t x; temp _x x; temp _y y)
         SEP (data_at sh t_struct_list (a ,u) x; listrep sh s1b u; listrep sh s2 y)))%assert))
                    (EXGIVEN u
                      [[(((PROP ()
         LOCAL (temp _t x; temp _x x; temp _y y)
         SEP (data_at sh t_struct_list (a ,u) x; listrep sh s1b u; listrep sh s2 y)))%assert)]] 
                      (Csequence
                        (Cset _u
                          (Efield
                            (Ederef
                              (Etempvar _t (tptr (Tstruct _list noattr)))
                              (Tstruct _list noattr)) _tail
                            (tptr (Tstruct _list noattr))))
                        (Csequence
                          (Cloop
                            (Csequence
                              (Cassert (
    (EX a s1b t u,
          PROP ()
          LOCAL (temp _x x; temp _t t; temp _u u; temp _y y)
          SEP (listrep sh (a::s1b++s2) t -* listrep sh (s1++s2) x;
                 data_at sh t_struct_list (a,u) t;
                 listrep sh s1b u;
                 listrep sh s2 y))%assert))
                              (EXGIVEN a
                                [[((EX s1b t u,
          PROP ()
          LOCAL (temp _x x; temp _t t; temp _u u; temp _y y)
          SEP (listrep sh (a::s1b++s2) t -* listrep sh (s1++s2) x;
                 data_at sh t_struct_list (a,u) t;
                 listrep sh s1b u;
                 listrep sh s2 y))%assert)]] 
                                (EXGIVEN s1b
                                  [[((EX t u,
          PROP ()
          LOCAL (temp _x x; temp _t t; temp _u u; temp _y y)
          SEP (listrep sh (a::s1b++s2) t -* listrep sh (s1++s2) x;
                 data_at sh t_struct_list (a,u) t;
                 listrep sh s1b u;
                 listrep sh s2 y))%assert)]] 
                                  (EXGIVEN t
                                    [[((EX u,
          PROP ()
          LOCAL (temp _x x; temp _t t; temp _u u; temp _y y)
          SEP (listrep sh (a::s1b++s2) t -* listrep sh (s1++s2) x;
                 data_at sh t_struct_list (a,u) t;
                 listrep sh s1b u;
                 listrep sh s2 y))%assert)]] 
                                    (EXGIVEN u
                                      [[((PROP ()
          LOCAL (temp _x x; temp _t t; temp _u u; temp _y y)
          SEP (listrep sh (a::s1b++s2) t -* listrep sh (s1++s2) x;
                 data_at sh t_struct_list (a,u) t;
                 listrep sh s1b u;
                 listrep sh s2 y))%assert)]] 
                                      (Csequence
                                        (Cifthenelse (Ebinop One
                                                       (Etempvar _u (tptr (Tstruct _list noattr)))
                                                       (Ecast
                                                         (Econst_int (Int.repr 0) tint)
                                                         (tptr tvoid)) tint)
                                          Cskip
                                          (Csequence Cbreak Cskip))
                                        (Csequence
                                          (Cassert ( (EX b s1c z,
            (PROP (s1b = b :: s1c)
             LOCAL (temp _x x; temp _t t; temp _u u; temp _y y)
             SEP (listrep sh (a :: s1b ++ s2) t -* listrep sh (s1 ++ s2) x;
                  data_at sh t_struct_list (a, u) t;
                  data_at sh t_struct_list (b, z) u;
                  listrep sh s1c z; listrep sh s2 y)))%assert))
                                          (EXGIVEN b
                                            [[((EX s1c z,
            (PROP (s1b = b :: s1c)
             LOCAL (temp _x x; temp _t t; temp _u u; temp _y y)
             SEP (listrep sh (a :: s1b ++ s2) t -* listrep sh (s1 ++ s2) x;
                  data_at sh t_struct_list (a, u) t;
                  data_at sh t_struct_list (b, z) u;
                  listrep sh s1c z; listrep sh s2 y)))%assert)]] 
                                            (EXGIVEN s1c
                                              [[((EX z,
            (PROP (s1b = b :: s1c)
             LOCAL (temp _x x; temp _t t; temp _u u; temp _y y)
             SEP (listrep sh (a :: s1b ++ s2) t -* listrep sh (s1 ++ s2) x;
                  data_at sh t_struct_list (a, u) t;
                  data_at sh t_struct_list (b, z) u;
                  listrep sh s1c z; listrep sh s2 y)))%assert)]] 
                                              (EXGIVEN z
                                                [[(((PROP (s1b = b :: s1c)
             LOCAL (temp _x x; temp _t t; temp _u u; temp _y y)
             SEP (listrep sh (a :: s1b ++ s2) t -* listrep sh (s1 ++ s2) x;
                  data_at sh t_struct_list (a, u) t;
                  data_at sh t_struct_list (b, z) u;
                  listrep sh s1c z; listrep sh s2 y)))%assert)]] 
                                                (Csequence
                                                  (Cset _t
                                                    (Etempvar _u (tptr (Tstruct _list noattr))))
                                                  (Csequence
                                                    (Cset _u
                                                      (Efield
                                                        (Ederef
                                                          (Etempvar _t (tptr (Tstruct _list noattr)))
                                                          (Tstruct _list noattr))
                                                        _tail
                                                        (tptr (Tstruct _list noattr))))
                                                    Cskip))))))))))))
                            Cskip)
                          (Csequence
                            (Cassign
                              (Efield
                                (Ederef
                                  (Etempvar _t (tptr (Tstruct _list noattr)))
                                  (Tstruct _list noattr)) _tail
                                (tptr (Tstruct _list noattr)))
                              (Etempvar _y (tptr (Tstruct _list noattr))))
                            (Csequence
                              (Creturn (Some (Etempvar _x (tptr (Tstruct _list noattr)))))
                              Cskip)))))))))))
        Cskip)))).

Definition Gprog : funspecs :=
  ltac:(with_library prog [append_spec]).
Locate compute_split.

Definition res :=
  ltac:(compute_split f_append_hint).

Print res.


