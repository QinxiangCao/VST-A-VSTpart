From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Require Import AClight.AClight.
Local Open Scope Z_scope.
Import AClightNotations.
Require Import testprogs.sgn_def.
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

Definition f_sgn_hint :=
(GIVEN  x:Z,
  (Ssequence
    (Sdummyassert ( PROP (Int.min_signed <= x <= Int.max_signed) LOCAL (temp _x  (Vint (Int.repr x))) SEP ()))
    (Ssequence
      (Sdummyassert ( PROP () LOCAL (temp ret_temp  (Vint (Int.repr (sgn x)))) SEP ()))
      (Ssequence
        (Sifthenelse (Ebinop Ole (Etempvar _x tint)
                       (Econst_int (Int.repr 0) tint) tint)
          (Ssequence
            (Sifthenelse (Ebinop Oeq (Etempvar _x tint)
                           (Econst_int (Int.repr 0) tint) tint)
              (Ssequence (Sset _ret (Econst_int (Int.repr 0) tint)) Sskip)
              (Ssequence
                (Sset _ret (Eunop Oneg (Econst_int (Int.repr 1) tint) tint))
                Sskip))
            Sskip)
          (Ssequence (Sset _ret (Econst_int (Int.repr 1) tint)) Sskip))
        (Ssequence (Sreturn (Some (Etempvar _ret tint))) Sskip))))).

Definition Gprog : funspecs :=
  ltac:(with_library prog [sgn_spec]).


