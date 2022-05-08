(************************************)
(************************************)
(**** from [cprogs/reverse_prog.v] ***)
(************************************)
(************************************)
From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Local Open Scope Z_scope.

Module Info.
  Definition version := "3.6"%string.
  Definition build_number := ""%string.
  Definition build_tag := ""%string.
  Definition arch := "x86"%string.
  Definition model := "64"%string.
  Definition abi := "macosx"%string.
  Definition bitsize := 64.
  Definition big_endian := false.
  Definition source_file := "cprogs/reverse.c"%string.
  Definition normalized := true.
End Info.

Definition ___builtin_annot : ident := 12%positive.
Definition ___builtin_annot_intval : ident := 13%positive.
Definition ___builtin_bswap : ident := 5%positive.
Definition ___builtin_bswap16 : ident := 7%positive.
Definition ___builtin_bswap32 : ident := 6%positive.
Definition ___builtin_bswap64 : ident := 4%positive.
Definition ___builtin_clz : ident := 38%positive.
Definition ___builtin_clzl : ident := 39%positive.
Definition ___builtin_clzll : ident := 40%positive.
Definition ___builtin_ctz : ident := 41%positive.
Definition ___builtin_ctzl : ident := 42%positive.
Definition ___builtin_ctzll : ident := 43%positive.
Definition ___builtin_debug : ident := 55%positive.
Definition ___builtin_fabs : ident := 8%positive.
Definition ___builtin_fmadd : ident := 46%positive.
Definition ___builtin_fmax : ident := 44%positive.
Definition ___builtin_fmin : ident := 45%positive.
Definition ___builtin_fmsub : ident := 47%positive.
Definition ___builtin_fnmadd : ident := 48%positive.
Definition ___builtin_fnmsub : ident := 49%positive.
Definition ___builtin_fsqrt : ident := 9%positive.
Definition ___builtin_membar : ident := 14%positive.
Definition ___builtin_memcpy_aligned : ident := 10%positive.
Definition ___builtin_nop : ident := 54%positive.
Definition ___builtin_read16_reversed : ident := 50%positive.
Definition ___builtin_read32_reversed : ident := 51%positive.
Definition ___builtin_sel : ident := 11%positive.
Definition ___builtin_va_arg : ident := 16%positive.
Definition ___builtin_va_copy : ident := 17%positive.
Definition ___builtin_va_end : ident := 18%positive.
Definition ___builtin_va_start : ident := 15%positive.
Definition ___builtin_write16_reversed : ident := 52%positive.
Definition ___builtin_write32_reversed : ident := 53%positive.
Definition ___compcert_i64_dtos : ident := 23%positive.
Definition ___compcert_i64_dtou : ident := 24%positive.
Definition ___compcert_i64_sar : ident := 35%positive.
Definition ___compcert_i64_sdiv : ident := 29%positive.
Definition ___compcert_i64_shl : ident := 33%positive.
Definition ___compcert_i64_shr : ident := 34%positive.
Definition ___compcert_i64_smod : ident := 31%positive.
Definition ___compcert_i64_smulh : ident := 36%positive.
Definition ___compcert_i64_stod : ident := 25%positive.
Definition ___compcert_i64_stof : ident := 27%positive.
Definition ___compcert_i64_udiv : ident := 30%positive.
Definition ___compcert_i64_umod : ident := 32%positive.
Definition ___compcert_i64_umulh : ident := 37%positive.
Definition ___compcert_i64_utod : ident := 26%positive.
Definition ___compcert_i64_utof : ident := 28%positive.
Definition ___compcert_va_composite : ident := 22%positive.
Definition ___compcert_va_float64 : ident := 21%positive.
Definition ___compcert_va_int32 : ident := 19%positive.
Definition ___compcert_va_int64 : ident := 20%positive.
Definition _head : ident := 1%positive.
Definition _list : ident := 2%positive.
Definition _main : ident := 61%positive.
Definition _p : ident := 56%positive.
Definition _reverse : ident := 60%positive.
Definition _t : ident := 58%positive.
Definition _tail : ident := 3%positive.
Definition _v : ident := 59%positive.
Definition _w : ident := 57%positive.

Definition f_reverse := {|
  fn_return := (tptr (Tstruct _list noattr));
  fn_callconv := cc_default;
  fn_params := ((_p, (tptr (Tstruct _list noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_w, (tptr (Tstruct _list noattr))) ::
               (_t, (tptr (Tstruct _list noattr))) ::
               (_v, (tptr (Tstruct _list noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _w (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
  (Ssequence
    (Sset _v (Etempvar _p (tptr (Tstruct _list noattr))))
    (Ssequence
      (Swhile
        (Etempvar _v (tptr (Tstruct _list noattr)))
        (Ssequence
          (Sset _t
            (Efield
              (Ederef (Etempvar _v (tptr (Tstruct _list noattr)))
                (Tstruct _list noattr)) _tail (tptr (Tstruct _list noattr))))
          (Ssequence
            (Sassign
              (Efield
                (Ederef (Etempvar _v (tptr (Tstruct _list noattr)))
                  (Tstruct _list noattr)) _tail
                (tptr (Tstruct _list noattr)))
              (Etempvar _w (tptr (Tstruct _list noattr))))
            (Ssequence
              (Sset _w (Etempvar _v (tptr (Tstruct _list noattr))))
              (Sset _v (Etempvar _t (tptr (Tstruct _list noattr))))))))
      (Sreturn (Some (Etempvar _w (tptr (Tstruct _list noattr))))))))
|}.

Definition composites : list composite_definition :=
(Composite _list Struct
   ((_head, tuint) :: (_tail, (tptr (Tstruct _list noattr))) :: nil)
   noattr :: nil).

Definition global_definitions : list (ident * globdef fundef type) :=
((___builtin_bswap64,
   Gfun(External (EF_builtin "__builtin_bswap64"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tlong)
                     cc_default)) (Tcons tulong Tnil) tulong cc_default)) ::
 (___builtin_bswap,
   Gfun(External (EF_builtin "__builtin_bswap"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
 (___builtin_bswap32,
   Gfun(External (EF_builtin "__builtin_bswap32"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
 (___builtin_bswap16,
   Gfun(External (EF_builtin "__builtin_bswap16"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tushort Tnil) tushort cc_default)) ::
 (___builtin_fabs,
   Gfun(External (EF_builtin "__builtin_fabs"
                   (mksignature (AST.Tfloat :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_fsqrt,
   Gfun(External (EF_builtin "__builtin_fsqrt"
                   (mksignature (AST.Tfloat :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_memcpy_aligned,
   Gfun(External (EF_builtin "__builtin_memcpy_aligned"
                   (mksignature
                     (AST.Tlong :: AST.Tlong :: AST.Tlong :: AST.Tlong ::
                      nil) None cc_default))
     (Tcons (tptr tvoid)
       (Tcons (tptr tvoid) (Tcons tulong (Tcons tulong Tnil)))) tvoid
     cc_default)) ::
 (___builtin_sel,
   Gfun(External (EF_builtin "__builtin_sel"
                   (mksignature (AST.Tint :: nil) None
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
     (Tcons tbool Tnil) tvoid
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot,
   Gfun(External (EF_builtin "__builtin_annot"
                   (mksignature (AST.Tlong :: nil) None
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr tschar) Tnil) tvoid
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot_intval,
   Gfun(External (EF_builtin "__builtin_annot_intval"
                   (mksignature (AST.Tlong :: AST.Tint :: nil)
                     (Some AST.Tint) cc_default))
     (Tcons (tptr tschar) (Tcons tint Tnil)) tint cc_default)) ::
 (___builtin_membar,
   Gfun(External (EF_builtin "__builtin_membar"
                   (mksignature nil None cc_default)) Tnil tvoid cc_default)) ::
 (___builtin_va_start,
   Gfun(External (EF_builtin "__builtin_va_start"
                   (mksignature (AST.Tlong :: nil) None cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___builtin_va_arg,
   Gfun(External (EF_builtin "__builtin_va_arg"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) None
                     cc_default)) (Tcons (tptr tvoid) (Tcons tuint Tnil))
     tvoid cc_default)) ::
 (___builtin_va_copy,
   Gfun(External (EF_builtin "__builtin_va_copy"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) None
                     cc_default))
     (Tcons (tptr tvoid) (Tcons (tptr tvoid) Tnil)) tvoid cc_default)) ::
 (___builtin_va_end,
   Gfun(External (EF_builtin "__builtin_va_end"
                   (mksignature (AST.Tlong :: nil) None cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___compcert_va_int32,
   Gfun(External (EF_external "__compcert_va_int32"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tint)
                     cc_default)) (Tcons (tptr tvoid) Tnil) tuint
     cc_default)) ::
 (___compcert_va_int64,
   Gfun(External (EF_external "__compcert_va_int64"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tlong)
                     cc_default)) (Tcons (tptr tvoid) Tnil) tulong
     cc_default)) ::
 (___compcert_va_float64,
   Gfun(External (EF_external "__compcert_va_float64"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons (tptr tvoid) Tnil) tdouble
     cc_default)) ::
 (___compcert_va_composite,
   Gfun(External (EF_external "__compcert_va_composite"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons (tptr tvoid) (Tcons tulong Tnil)) (tptr tvoid) cc_default)) ::
 (___compcert_i64_dtos,
   Gfun(External (EF_runtime "__compcert_i64_dtos"
                   (mksignature (AST.Tfloat :: nil) (Some AST.Tlong)
                     cc_default)) (Tcons tdouble Tnil) tlong cc_default)) ::
 (___compcert_i64_dtou,
   Gfun(External (EF_runtime "__compcert_i64_dtou"
                   (mksignature (AST.Tfloat :: nil) (Some AST.Tlong)
                     cc_default)) (Tcons tdouble Tnil) tulong cc_default)) ::
 (___compcert_i64_stod,
   Gfun(External (EF_runtime "__compcert_i64_stod"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons tlong Tnil) tdouble cc_default)) ::
 (___compcert_i64_utod,
   Gfun(External (EF_runtime "__compcert_i64_utod"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons tulong Tnil) tdouble cc_default)) ::
 (___compcert_i64_stof,
   Gfun(External (EF_runtime "__compcert_i64_stof"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tsingle)
                     cc_default)) (Tcons tlong Tnil) tfloat cc_default)) ::
 (___compcert_i64_utof,
   Gfun(External (EF_runtime "__compcert_i64_utof"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tsingle)
                     cc_default)) (Tcons tulong Tnil) tfloat cc_default)) ::
 (___compcert_i64_sdiv,
   Gfun(External (EF_runtime "__compcert_i64_sdiv"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tlong (Tcons tlong Tnil)) tlong cc_default)) ::
 (___compcert_i64_udiv,
   Gfun(External (EF_runtime "__compcert_i64_udiv"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tulong (Tcons tulong Tnil)) tulong cc_default)) ::
 (___compcert_i64_smod,
   Gfun(External (EF_runtime "__compcert_i64_smod"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tlong (Tcons tlong Tnil)) tlong cc_default)) ::
 (___compcert_i64_umod,
   Gfun(External (EF_runtime "__compcert_i64_umod"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tulong (Tcons tulong Tnil)) tulong cc_default)) ::
 (___compcert_i64_shl,
   Gfun(External (EF_runtime "__compcert_i64_shl"
                   (mksignature (AST.Tlong :: AST.Tint :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tlong (Tcons tint Tnil)) tlong cc_default)) ::
 (___compcert_i64_shr,
   Gfun(External (EF_runtime "__compcert_i64_shr"
                   (mksignature (AST.Tlong :: AST.Tint :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tulong (Tcons tint Tnil)) tulong cc_default)) ::
 (___compcert_i64_sar,
   Gfun(External (EF_runtime "__compcert_i64_sar"
                   (mksignature (AST.Tlong :: AST.Tint :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tlong (Tcons tint Tnil)) tlong cc_default)) ::
 (___compcert_i64_smulh,
   Gfun(External (EF_runtime "__compcert_i64_smulh"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tlong (Tcons tlong Tnil)) tlong cc_default)) ::
 (___compcert_i64_umulh,
   Gfun(External (EF_runtime "__compcert_i64_umulh"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tulong (Tcons tulong Tnil)) tulong cc_default)) ::
 (___builtin_clz,
   Gfun(External (EF_builtin "__builtin_clz"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_clzl,
   Gfun(External (EF_builtin "__builtin_clzl"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tint)
                     cc_default)) (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_clzll,
   Gfun(External (EF_builtin "__builtin_clzll"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tint)
                     cc_default)) (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_ctz,
   Gfun(External (EF_builtin "__builtin_ctz"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_ctzl,
   Gfun(External (EF_builtin "__builtin_ctzl"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tint)
                     cc_default)) (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_ctzll,
   Gfun(External (EF_builtin "__builtin_ctzll"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tint)
                     cc_default)) (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_fmax,
   Gfun(External (EF_builtin "__builtin_fmax"
                   (mksignature (AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble Tnil)) tdouble cc_default)) ::
 (___builtin_fmin,
   Gfun(External (EF_builtin "__builtin_fmin"
                   (mksignature (AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble Tnil)) tdouble cc_default)) ::
 (___builtin_fmadd,
   Gfun(External (EF_builtin "__builtin_fmadd"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fmsub,
   Gfun(External (EF_builtin "__builtin_fmsub"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fnmadd,
   Gfun(External (EF_builtin "__builtin_fnmadd"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fnmsub,
   Gfun(External (EF_builtin "__builtin_fnmsub"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_read16_reversed,
   Gfun(External (EF_builtin "__builtin_read16_reversed"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tint)
                     cc_default)) (Tcons (tptr tushort) Tnil) tushort
     cc_default)) ::
 (___builtin_read32_reversed,
   Gfun(External (EF_builtin "__builtin_read32_reversed"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tint)
                     cc_default)) (Tcons (tptr tuint) Tnil) tuint
     cc_default)) ::
 (___builtin_write16_reversed,
   Gfun(External (EF_builtin "__builtin_write16_reversed"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) None
                     cc_default)) (Tcons (tptr tushort) (Tcons tushort Tnil))
     tvoid cc_default)) ::
 (___builtin_write32_reversed,
   Gfun(External (EF_builtin "__builtin_write32_reversed"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) None
                     cc_default)) (Tcons (tptr tuint) (Tcons tuint Tnil))
     tvoid cc_default)) ::
 (___builtin_nop,
   Gfun(External (EF_builtin "__builtin_nop"
                   (mksignature nil None cc_default)) Tnil tvoid cc_default)) ::
 (___builtin_debug,
   Gfun(External (EF_external "__builtin_debug"
                   (mksignature (AST.Tint :: nil) None
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
     (Tcons tint Tnil) tvoid
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})) ::
 (_reverse, Gfun(Internal f_reverse)) :: nil).

Definition public_idents : list ident :=
(_reverse :: ___builtin_debug :: ___builtin_nop ::
 ___builtin_write32_reversed :: ___builtin_write16_reversed ::
 ___builtin_read32_reversed :: ___builtin_read16_reversed ::
 ___builtin_fnmsub :: ___builtin_fnmadd :: ___builtin_fmsub ::
 ___builtin_fmadd :: ___builtin_fmin :: ___builtin_fmax ::
 ___builtin_ctzll :: ___builtin_ctzl :: ___builtin_ctz :: ___builtin_clzll ::
 ___builtin_clzl :: ___builtin_clz :: ___compcert_i64_umulh ::
 ___compcert_i64_smulh :: ___compcert_i64_sar :: ___compcert_i64_shr ::
 ___compcert_i64_shl :: ___compcert_i64_umod :: ___compcert_i64_smod ::
 ___compcert_i64_udiv :: ___compcert_i64_sdiv :: ___compcert_i64_utof ::
 ___compcert_i64_stof :: ___compcert_i64_utod :: ___compcert_i64_stod ::
 ___compcert_i64_dtou :: ___compcert_i64_dtos :: ___compcert_va_composite ::
 ___compcert_va_float64 :: ___compcert_va_int64 :: ___compcert_va_int32 ::
 ___builtin_va_end :: ___builtin_va_copy :: ___builtin_va_arg ::
 ___builtin_va_start :: ___builtin_membar :: ___builtin_annot_intval ::
 ___builtin_annot :: ___builtin_sel :: ___builtin_memcpy_aligned ::
 ___builtin_fsqrt :: ___builtin_fabs :: ___builtin_bswap16 ::
 ___builtin_bswap32 :: ___builtin_bswap :: ___builtin_bswap64 :: nil).

Definition prog : Clight.program := 
  mkprogram composites global_definitions public_idents _main Logic.I.


(************************************)
(************************************)
(**** from [cprogs/reverse_def.v] ****)
(************************************)
(************************************)
Require Import VST.floyd.proofauto.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.
Definition t_struct_list := Tstruct _list noattr.

Fixpoint listrep (sh: share)
            (contents: list val) (x: val) : mpred :=
 match contents with
 | h::hs =>
              EX y:val,
                data_at sh t_struct_list (h,y) x * listrep sh hs y
 | nil => !! (x = nullval) && emp
 end.

Arguments listrep sh contents x : simpl never.

Lemma listrep_local_facts:
  forall sh contents p,
     listrep sh contents p |--
     !! (is_pointer_or_null p /\ (p=nullval <-> contents=nil)).
Proof.
intros.
revert p; induction contents; unfold listrep; fold listrep; intros; normalize.
apply prop_right; split; simpl; auto. intuition.
entailer!.
split; intro. subst p. destruct H; contradiction. inv H2.
Qed.

Hint Resolve listrep_local_facts : saturate_local.

Lemma listrep_valid_pointer:
  forall sh contents p,
   sepalg.nonidentity sh ->
   listrep sh contents p |-- valid_pointer p.
Proof.
 destruct contents; unfold listrep; fold listrep; intros; normalize.
 auto with valid_pointer.
 apply sepcon_valid_pointer1.
 apply data_at_valid_ptr; auto. simpl;  computable.
Qed.

Hint Resolve listrep_valid_pointer : valid_pointer.

Lemma listrep_null: forall sh contents,
    listrep sh contents nullval = !! (contents=nil) && emp.
Proof.
destruct contents; unfold listrep; fold listrep.
normalize.
apply pred_ext.
Intros y. entailer. destruct H; contradiction.
Intros.
Qed.

Lemma is_pointer_or_null_not_null:
 forall x, is_pointer_or_null x -> x <> nullval -> isptr x.
Proof.
intros.
 destruct x; try contradiction. hnf in H; subst i. contradiction H0; reflexivity.
 apply I.
Qed.

Lemma listrep_is_null: forall sh l p,
  p = nullval ->
  listrep sh l p |-- !! (p = nullval /\ l = nil) && emp.
Proof.
  intros.
  saturate_local.
  assert (l = nil) by tauto.
  entailer!.
  unfold listrep.
  entailer!.
Qed.

Lemma listrep_isptr: forall sh l p,
  isptr p ->
  listrep sh l p |--
    EX x l' q, !! (l = x :: l') &&
      data_at sh t_struct_list (x, q) p *
      listrep sh l' q.
Proof.
  intros.
  saturate_local.
  destruct l.
  + pose proof proj2 H0 eq_refl. subst; tauto .
  +
  clear H0 PNp.
  Exists v l.
  unfold listrep at 1; fold listrep.
  Intros t; Exists t.
  entailer!.
Qed.

Lemma ecancel_cell: forall sh p xq,
  data_at sh t_struct_list xq p * emp |-- data_at sh t_struct_list xq p.
Proof.
  intros.
  rewrite sepcon_emp; auto.
Qed.

Lemma ecancel_list: forall sh p l,
  listrep sh l p * emp |-- listrep sh l p.
Proof.
  intros.
  rewrite sepcon_emp; auto.
Qed.

Lemma ecancel_nil_list: forall sh p,
  p = nullval ->
  emp |-- listrep sh nil p.
Proof.
  intros.
  subst; unfold listrep.
  entailer!.
Qed.

Lemma ecancel_head: forall sh (p q x: val) l,
  data_at sh t_struct_list (x, q) p * listrep sh l q |-- listrep sh (x :: l) p.
Proof.
  intros.
  unfold listrep at 2; fold listrep.
  Exists q.
  entailer!.
Qed.

Lemma listrep_unify: forall sh p l1 l2,
  l1 = l2 ->
  listrep sh l1 p*emp  |-- listrep sh l2 p.
Proof.
  intros. rewrite sepcon_emp.
  subst.
  auto.
Qed.

Lemma ecancel_cell': forall sh p xq xq',
  xq = xq' ->
  data_at sh t_struct_list xq p * emp |-- data_at sh t_struct_list xq' p.
Proof.
  intros.
  subst.
  rewrite sepcon_emp; auto.
Qed.

Lemma ecancel_nil_list': forall sh p l,
  l=nil/\p = nullval ->
  emp |-- listrep sh l p.
Proof.
  intros. destruct H.
  subst; unfold listrep.
  entailer!.
Qed.

Lemma same_data_at_l_r: forall sh (p:val) (q:val) (x:val) (x':val) (q':val),x=x'->q=q'->
   data_at sh t_struct_list (x, q) p * emp |--
       data_at sh t_struct_list (x', q') p .
Proof.
  intros. rewrite sepcon_emp. entailer!.
Qed.

Ltac solve_data_at:=
idtac;
match goal with
| |- ?x = ?x => apply eq_refl
| |- ?x = ?u =>first [is_evar x;apply eq_refl|
first [is_evar u;apply eq_refl|auto]] end.
Ltac local_listrep_cancel :=
  idtac;
  match goal with
  | |- data_at ?sh t_struct_list (?x, ?q) ?p * _ |--
       data_at ?sh t_struct_list (?u, ?v) ?p =>
       refine (same_data_at_l_r sh p q x u v _ _) ;[solve_data_at|solve_data_at]
  | |- emp |-- listrep ?sh ?l ?p =>
         first [is_evar l;refine (ecancel_nil_list sh p _); solve [auto]
         |refine (ecancel_nil_list' sh p l _ ); split;solve [auto]]
  | |- listrep ?sh ?l ?p * _ |--
       listrep ?sh ?l ?p =>
         exact (ecancel_list sh p l)
  | |- listrep ?sh ?l ?p * _ |--
       listrep ?sh ?u ?p =>
         first [is_evar u;exact (ecancel_list sh p l)|sep_apply
         (listrep_unify sh p l u );auto]
  | |- data_at ?sh t_struct_list (?x, ?q) ?p * _ |--
       listrep ?sh _ ?p =>
         refine (ecancel_head sh p q x _)
  | |- data_at ?sh t_struct_list (?x, ?q) ?p * _ |--
       listrep ?sh (?x :: ?l) _ =>
         exact (ecancel_head sh p q x l)
  end.

Ltac global_listrep_cancel :=
  idtac;
  match goal with
  | |- listrep ?sh ?l1 ?p |--
       listrep ?sh ?l2 _ =>
         refine (listrep_unify sh p l1 l2 _)
  end.

(* Ltac listrep_cancel:=
  eapply symbolic_cancel_setup;
  [ construct_fold_right_sepcon
  | construct_fold_right_sepcon
  | fold_abnormal_mpred
  | cbv iota beta delta [before_symbol_cancel];
     conservative_syntactic_cancel
      local_listrep_cancel;match goal with
       | |- _ |-- _ =>
      first [ simple apply syntactic_cancel_solve3
          | match goal with
            | |- fold_right_sepcon ?A |-- fold_right_sepcon ?B => rewrite <- (fold_left_sepconx_eq A), <- (fold_left_sepconx_eq B)
            end;
            unfold fold_left_sepconx; cbv iota beta;
            first
            [ simple apply derives_refl
            | global_listrep_cancel ] ]
        | _ =>idtac end    ].  *)
Ltac unify_for_already_lower :=
  idtac;
  match goal with
  | |- _ |--  andp (prop ?A) _ =>
        repeat
         match A with
         | context [ (?x = ?y) /\ _ ] => has_evar y; progress unify x y
         | (?x = ?y) => has_evar y; progress unify x y
         end
  | _ => idtac
  end.

Ltac pre_process :=
  let RHS := fresh "RHS" in 
  match goal with
  | |- _ |-- ?P => set (RHS := P)
  end;
  repeat
  match goal with
  | H: isptr ?p |- context [listrep ?sh ?l ?p] =>
         sep_apply (listrep_isptr sh l p);
         let x := fresh "x" in
         let ll := fresh "l" in
         let pp := fresh "p" in
         Intros x ll pp
  | H: ?p = nullval |- context [listrep ?sh ?l ?p] =>
         sep_apply (listrep_is_null sh l p);
         Intros
  | |- context [listrep ?sh ?l nullval] =>
         sep_apply (listrep_is_null sh l nullval);
         Intros
  end;
  subst RHS.

(* Ltac listrep_entailer :=
  Intros;
  pre_process;
  match goal with
  | |- ENTAIL _, PROPx _ (LOCALx _ (SEPx _)) |-- _ =>
         repeat EExists; go_lower
  | |- @derives mpred _ _ _ =>
         repeat EExists; unify_for_already_lower
  end;
  saturate_local;
  first [ apply andp_right; [apply prop_right | try listrep_cancel];
          [repeat split; auto | ..]
        | try listrep_cancel].                *)
(* Goal forall sh (p q x r: val) l, 
  r = nullval ->
  exists z w: val,
  data_at sh t_struct_list (x, q) p * listrep sh l q |--
  listrep sh (x :: l) w * listrep sh nil r * listrep sh nil z.
intros.
eexists.
eexists.
listrep_cancel.
Qed. 

Goal forall sh (p q x r: val) l,
  r = nullval ->
  data_at sh t_struct_list (x, q) p * listrep sh l q |--
  EX z w: val,
  listrep sh (x :: l) w * listrep sh nil r * listrep sh nil z.
intros.
listrep_entailer.

Qed.

Goal forall sh (x q x' q' p:val) ,x=x'->q=q'->
data_at sh t_struct_list (x, q) p*emp |--
       data_at sh t_struct_list (x', q') p.
intros.
local_listrep_cancel.
Qed. *)



  
(************************************)
(************************************)
(*** from [cprogs/reverse_annot.v] ***)
(************************************)
(************************************)
Require Import AClight.AClight.
Local Open Scope Z_scope.
Import AClightNotations.

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
(GIVEN  sh p l,
  (Ssequence
    (Sdummyassert (
            PROP  (writable_share sh)
	    LOCAL (temp _p p)
	    SEP   (listrep sh l p)))
    (Ssequence
      (Sdummyassert (
          EX q: val,
	    PROP  ()
	    LOCAL (temp ret_temp q)
	    SEP   (listrep sh (rev l) q)))
      (Ssequence
        (Sset _w (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
        (Ssequence
          (Sset _v (Etempvar _p (tptr (Tstruct _list noattr))))
          (Ssequence
            (Sloop
              (LISingle (
       (EX w v l1 l2,
          PROP  (l = rev l1 ++ l2)
	  LOCAL (temp _w w; temp _v v)
	  SEP   (listrep sh l1 w; listrep sh l2 v))%assert))
              (GIVEN w v l1 l2,
                (Ssequence
                  (Sdummyassert ((PROP  (l = rev l1 ++ l2)
	  LOCAL (temp _w w; temp _v v)
	  SEP   (listrep sh l1 w; listrep sh l2 v))%assert))
                  (Ssequence
                    (Sifthenelse (Etempvar _v (tptr (Tstruct _list noattr)))
                      Sskip
                      (Ssequence Sbreak Sskip))
                    (Ssequence
                      (Sassert (
         (EX t x l2',
	    PROP  (l2 = x :: l2')
	    LOCAL (temp _w w; temp _v v)
	    SEP   (data_at sh t_struct_list (x, t) v;
	           listrep sh l1 w; listrep sh l2' t))%assert))
                      (GIVEN t x l2',
                        (Ssequence
                          (Sdummyassert ((PROP  (l2 = x :: l2')
	    LOCAL (temp _w w; temp _v v)
	    SEP   (data_at sh t_struct_list (x, t) v;
	           listrep sh l1 w; listrep sh l2' t))%assert))
                          (Ssequence
                            (Sset _t
                              (Efield
                                (Ederef
                                  (Etempvar _v (tptr (Tstruct _list noattr)))
                                  (Tstruct _list noattr)) _tail
                                (tptr (Tstruct _list noattr))))
                            (Ssequence
                              (Sassign
                                (Efield
                                  (Ederef
                                    (Etempvar _v (tptr (Tstruct _list noattr)))
                                    (Tstruct _list noattr)) _tail
                                  (tptr (Tstruct _list noattr)))
                                (Etempvar _w (tptr (Tstruct _list noattr))))
                              (Ssequence
                                (Sset _w
                                  (Etempvar _v (tptr (Tstruct _list noattr))))
                                (Ssequence
                                  (Sset _v
                                    (Etempvar _t (tptr (Tstruct _list noattr))))
                                  Sskip))))))))))
              Sskip)
            (Ssequence
              (Sreturn (Some (Etempvar _w (tptr (Tstruct _list noattr)))))
              Sskip))))))).

Definition Gprog : funspecs :=
  ltac:(with_library prog [reverse_spec]).


(************************************)
(************************************)
(***** modified [f_append_hint] *****)
(************************************)
(************************************)

Require Import Split.defs.
Require Import Split.function.
Require Import VST.msl.shares.

Import Split.

Notation "a ++ b" := (app a b)
    (at level 60, right associativity).

Definition f_append_hint_new : Split.statement :=
(Stopgiven share Tsh (fun sh => 
(Stopgiven val Vundef (fun p => 
(Stopgiven (list val) nil (fun l => 
(Ssequence
    (Sset _w (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
(Ssequence
    (Sset _v (Etempvar _p (tptr (Tstruct _list noattr))))
(Ssequence
    (Sloop
        (LISingle (
            (EX w v l1 l2,
            PROP  (l = rev l1 ++ l2)
            LOCAL (temp _w w; temp _v v)
            SEP   (listrep sh l1 w; listrep sh l2 v))%assert))
    (* (GIVEN w v l1 l2, *)
    (* BEGIN OF EX w v l1 l2,  *)
    (Sgiven val Vundef (fun w => (
        (* dummy *)
        (EX v l1 l2,
            PROP  (l = rev l1 ++ l2)
            LOCAL (temp _w w; temp _v v)
            SEP   (listrep sh l1 w; listrep sh l2 v))%assert))
    (fun w =>
    (Sgiven val Vundef (fun v => (
        (* dummy *)
        (EX l1 l2,
            PROP  (l = rev l1 ++ l2)
            LOCAL (temp _w w; temp _v v)
            SEP   (listrep sh l1 w; listrep sh l2 v))%assert))
    (fun v =>
    (Sgiven (list val) nil (fun l1 => (
        (* dummy *)
        (EX l2,
            PROP  (l = rev l1 ++ l2)
            LOCAL (temp _w w; temp _v v)
            SEP   (listrep sh l1 w; listrep sh l2 v))%assert))
    (fun l1 =>
    (Sgiven (list val) nil (fun l2 => (
        (* dummy *)
        (   PROP  (l = rev l1 ++ l2)
            LOCAL (temp _w w; temp _v v)
            SEP   (listrep sh l1 w; listrep sh l2 v))%assert))
    (fun l2 =>

        (Ssequence
            (Sifthenelse (Etempvar _v (tptr (Tstruct _list noattr)))
                            Sskip
                            (Ssequence Sbreak Sskip))
        (
            (* BEGIN OF EX t x l2',  *)
                (Sgiven val Vundef (fun t => (
                    (* dummy *)
                    ((EX x l2',
                        PROP  (l2 = x :: l2')
                        LOCAL (temp _w w; temp _v v)
                        SEP   (data_at sh t_struct_list (x, t) v;
                                listrep sh l1 w; listrep sh l2' t))%assert)))
                (fun t =>
                (Sgiven val Vundef (fun x => (
                (* dummy *)
                ((EX l2',
                    PROP  (l2 = x :: l2')
                    LOCAL (temp _w w; temp _v v)
                    SEP   (data_at sh t_struct_list (x, t) v;
                            listrep sh l1 w; listrep sh l2' t))%assert)))
                (fun x =>
                (Sgiven (list val) nil (fun l2' => (
                (* dummy *)
                ((  PROP  (l2 = x :: l2')
                    LOCAL (temp _w w; temp _v v)
                    SEP   (data_at sh t_struct_list (x, t) v;
                            listrep sh l1 w; listrep sh l2' t))%assert)))
                (fun l2' =>
                    (Ssequence
                        (Sset _t
                            (Efield
                                (Ederef
                                    (Etempvar _v (tptr (Tstruct _list noattr)))
                                    (Tstruct _list noattr)) _tail
                                    (tptr (Tstruct _list noattr))))
                    (Ssequence
                        (Sassign
                            (Efield
                                (Ederef
                                    (Etempvar _v (tptr (Tstruct _list noattr)))
                                    (Tstruct _list noattr)) _tail
                                    (tptr (Tstruct _list noattr)))
                                    (Etempvar _w (tptr (Tstruct _list noattr))))
                    (Ssequence
                        (Sset _w
                            (Etempvar _v (tptr (Tstruct _list noattr))))
                    (Ssequence
                        (Sset _v
                            (Etempvar _t (tptr (Tstruct _list noattr))))
                                            Sskip))))))))))
                (* END OF EX t x l2',  *)
                ))
    ))))))))
    (* END OF EX w v l1 l2,  *)        
    Sskip) (* c_incr *)
(Ssequence
    (Sreturn (Some (Etempvar _w (tptr (Tstruct _list noattr)))))
    Sskip)))))))))).


(**)
Time Compute (split_result f_append_hint_new).