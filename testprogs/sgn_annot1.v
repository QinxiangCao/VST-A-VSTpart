From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Require Import CSplit.AClightFunc.
Require Import FloydSeq.AClight.
Require Import cprogs.sgn_def.
Require Import cprogs.sgn_prog.
Local Open Scope Z_scope.
Import AClightNotations.


Module Info.
  Definition version := "3.6"%string.
  Definition build_number := ""%string.
  Definition build_tag := ""%string.
  Definition arch := "x86"%string.
  Definition model := "64"%string.
  Definition abi := "macosx"%string.
  Definition bitsize := 64.
  Definition big_endian := false.
  Definition source_file := "testprogs/sgn.c"%string.
  Definition normalized := true.
End Info.

Definition f_sgn_spec_annotation :=
  ANNOTATION_WITH  x:Z, (( PROP (Int.min_signed <= x <= Int.max_signed) LOCAL (temp _x  (Vint (Int.repr x))) SEP ()),
  ( PROP () LOCAL (temp ret_temp  (Vint (Int.repr (sgn x)))) SEP ())).

Definition f_sgn_spec_complex :=
  ltac:(uncurry_funcspec f_sgn_spec_annotation).

Definition f_sgn_funsig: funsig :=
  (((_x, tint) :: nil), tint).

Definition sgn_spec :=
  ltac:(make_funcspec _sgn f_sgn_funsig f_sgn_spec_complex).

Parameter x:Z.

Definition f_sgn_hint :=
(
  (Csequence
    (* (Sdummyassert ( PROP (Int.min_signed <= x <= Int.max_signed) LOCAL (temp _x  (Vint (Int.repr x))) SEP ())) *)
    Cskip
    (Csequence
      (* (Sdummyassert ( PROP () LOCAL (temp ret_temp  (Vint (Int.repr (sgn x)))) SEP ())) *)
      Cskip
      (Csequence
        (Cassert (
        (EX x',
   PROP (Int.min_signed <= x' <= Int.max_signed /\ x = x')
   LOCAL (temp _x  (Vint (Int.repr x'))) 
   SEP ()
   )%assert))
        (EXGIVEN x'
          [[((PROP (Int.min_signed <= x' <= Int.max_signed /\ x = x')
   LOCAL (temp _x  (Vint (Int.repr x'))) 
   SEP ()
   )%assert)]] 
          (Csequence
            (Cifthenelse (Ebinop Ole (Etempvar _x tint)
                           (Econst_int (Int.repr 0) tint) tint)
              (Csequence
                (Cifthenelse (Ebinop Oeq (Etempvar _x tint)
                               (Econst_int (Int.repr 0) tint) tint)
                  (Csequence
                    (Cset _ret (Econst_int (Int.repr 0) tint))
                    Cskip)
                  (Csequence
                    (Cset _ret
                      (Eunop Oneg (Econst_int (Int.repr 1) tint) tint))
                    Cskip))
                Cskip)
              (Csequence (Cset _ret (Econst_int (Int.repr 1) tint)) Cskip))
            (Csequence
              (Cassert (
  ( EX r,
    PROP (r = sgn x') LOCAL (temp _x  (Vint (Int.repr x'))) SEP ())))
              (EXGIVEN r
                [[((PROP (r = sgn x') LOCAL (temp _x  (Vint (Int.repr x'))) SEP ()))]] 
                (Csequence
                  (Creturn (Some (Etempvar _ret tint)))
                  Cskip))))))))).

Definition Gprog : funspecs :=
  ltac:(with_library prog [sgn_spec]).

Definition f_sgn_hint_split :=
  ltac:(compute_split f_sgn_hint).

Print f_sgn_hint_split.


