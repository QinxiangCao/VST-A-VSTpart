Require Import VST.floyd.proofauto.
Require Import sumarray2.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

(* Some definitions relating to the functional spec of this particular program.  *)
Definition sum_Z : list Z -> Z := fold_right Z.add 0.

Lemma sum_Z_app:
  forall a b, sum_Z (a++b) =  sum_Z a + sum_Z b.
Proof.
  intros. induction a; simpl; omega.
Qed.

(* Beginning of the API spec for the sumarray.c program *)
Definition sumarray_spec :=
 DECLARE _sumarray
  WITH a: val, sh : share, contents : list Z, size: Z
  PRE [ _a OF (tptr tuint), _n OF tint ]
          PROP  (readable_share sh; 0 <= size <= Int.max_signed)
          LOCAL (temp _a a; temp _n (Vint (Int.repr size)))
          SEP   (data_at sh (tarray tuint size) (map Vint (map Int.repr contents)) a)
  POST [ tuint ]
        PROP () LOCAL(temp ret_temp  (Vint (Int.repr (sum_Z contents))))
           SEP (data_at sh (tarray tuint size) (map Vint (map Int.repr contents)) a).

(* The precondition of "int main(void){}" always looks like this. *)
Definition main_spec :=
 DECLARE _main
  WITH gv: globals
  PRE  [] main_pre prog nil gv
  POST [ tint ]  
     PROP() 
     LOCAL (temp ret_temp (Vint (Int.repr (3+4)))) 
     SEP(TT).

(* Packaging the API spec all together. *)
Definition Gprog : funspecs :=
        ltac:(with_library prog [sumarray_spec; main_spec]).