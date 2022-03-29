Require Import CSplit.soundness.

Print Assumptions soundness.

(* 

Axioms:
Rdefinitions.up : Rdefinitions.R -> BinNums.Z
Raxioms.total_order_T : forall r1 r2 : Rdefinitions.R,
	                    {Rdefinitions.Rlt r1 r2} + {r1 = r2} +
                        {Rdefinitions.Rgt r1 r2}
Axioms.prop_ext : ClassicalFacts.prop_extensionality
FunctionalExtensionality.functional_extensionality_dep : 
forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
(forall x : A, f x = g x) -> f = g
Eqdep.Eq_rect_eq.eq_rect_eq : forall (U : Type) (p : U) 
                                (Q : U -> Type) (x : Q p) 
                                (h : p = p), x = eq_rect p Q x p h
Raxioms.completeness : forall E : Rdefinitions.R -> Prop,
                       Raxioms.bound E ->
                       (exists x : Rdefinitions.R, E x) ->
                       {m : Rdefinitions.R | Raxioms.is_lub E m}
Classical_Prop.classic : forall P : Prop, P \/ ~ P
Raxioms.archimed : forall r : Rdefinitions.R,
                   Rdefinitions.Rgt (Rdefinitions.IZR (Rdefinitions.up r)) r /\
                   Rdefinitions.Rle
                     (Rdefinitions.Rminus
                        (Rdefinitions.IZR (Rdefinitions.up r)) r)
                     (Rdefinitions.IZR (BinNums.Zpos BinNums.xH))
Raxioms.Rplus_opp_r : forall r : Rdefinitions.R,
                      Rdefinitions.Rplus r (Rdefinitions.Ropp r) =
                      Rdefinitions.IZR BinNums.Z0
Raxioms.Rplus_lt_compat_l : forall r r1 r2 : Rdefinitions.R,
                            Rdefinitions.Rlt r1 r2 ->
                            Rdefinitions.Rlt (Rdefinitions.Rplus r r1)
                              (Rdefinitions.Rplus r r2)
Raxioms.Rplus_comm : forall r1 r2 : Rdefinitions.R,
                     Rdefinitions.Rplus r1 r2 = Rdefinitions.Rplus r2 r1
Raxioms.Rplus_assoc : forall r1 r2 r3 : Rdefinitions.R,
                      Rdefinitions.Rplus (Rdefinitions.Rplus r1 r2) r3 =
                      Rdefinitions.Rplus r1 (Rdefinitions.Rplus r2 r3)
Raxioms.Rplus_0_l : forall r : Rdefinitions.R,
                    Rdefinitions.Rplus (Rdefinitions.IZR BinNums.Z0) r = r
Rdefinitions.Rplus : Rdefinitions.R -> Rdefinitions.R -> Rdefinitions.R
Rdefinitions.Ropp : Rdefinitions.R -> Rdefinitions.R
Raxioms.Rmult_plus_distr_l : forall r1 r2 r3 : Rdefinitions.R,
                             Rdefinitions.Rmult r1 (Rdefinitions.Rplus r2 r3) =
                             Rdefinitions.Rplus (Rdefinitions.Rmult r1 r2)
                               (Rdefinitions.Rmult r1 r3)
Raxioms.Rmult_lt_compat_l : forall r r1 r2 : Rdefinitions.R,
                            Rdefinitions.Rlt (Rdefinitions.IZR BinNums.Z0) r ->
                            Rdefinitions.Rlt r1 r2 ->
                            Rdefinitions.Rlt (Rdefinitions.Rmult r r1)
                              (Rdefinitions.Rmult r r2)
Raxioms.Rmult_comm : forall r1 r2 : Rdefinitions.R,
                     Rdefinitions.Rmult r1 r2 = Rdefinitions.Rmult r2 r1
Raxioms.Rmult_assoc : forall r1 r2 r3 : Rdefinitions.R,
                      Rdefinitions.Rmult (Rdefinitions.Rmult r1 r2) r3 =
                      Rdefinitions.Rmult r1 (Rdefinitions.Rmult r2 r3)
Raxioms.Rmult_1_l : forall r : Rdefinitions.R,
                    Rdefinitions.Rmult
                      (Rdefinitions.IZR (BinNums.Zpos BinNums.xH)) r = r
Rdefinitions.Rmult : Rdefinitions.R -> Rdefinitions.R -> Rdefinitions.R
Raxioms.Rlt_trans : forall r1 r2 r3 : Rdefinitions.R,
                    Rdefinitions.Rlt r1 r2 ->
                    Rdefinitions.Rlt r2 r3 -> Rdefinitions.Rlt r1 r3
Raxioms.Rlt_asym : forall r1 r2 : Rdefinitions.R,
                   Rdefinitions.Rlt r1 r2 -> ~ Rdefinitions.Rlt r2 r1
Rdefinitions.Rlt : Rdefinitions.R -> Rdefinitions.R -> Prop
Raxioms.Rinv_l : forall r : Rdefinitions.R,
                 r <> Rdefinitions.IZR BinNums.Z0 ->
                 Rdefinitions.Rmult (Rdefinitions.Rinv r) r =
                 Rdefinitions.IZR (BinNums.Zpos BinNums.xH)
Rdefinitions.Rinv : Rdefinitions.R -> Rdefinitions.R
Raxioms.R1_neq_R0 : Rdefinitions.IZR (BinNums.Zpos BinNums.xH) <>
                    Rdefinitions.IZR BinNums.Z0
Rdefinitions.R1 : Rdefinitions.R
Rdefinitions.R0 : Rdefinitions.R
Rdefinitions.R : Set
JMeq.JMeq_eq : forall (A : Type) (x y : A), JMeq.JMeq x y -> x = y


*)

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

Require Import CSplit.AClight.

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

Arguments Cifthenelse _ {_ _} _ _.
Arguments Csequence {_ _ } _ _.

Check Cgiven.

Lemma Z_inhabited: inhabited Z.
Proof.
  constructor. apply 0.
Qed.


Locate precise.

Check mk_funspec.
Search allp wand.

Print predicates_sl.precise.
(* 

forall Q R, (P * (Q && R) = (P * Q) && (P * R))%pred.

our precise:

precise ([A] {P} op {Q}) :=

forall R1, R2,
EX (x1:A), P x1 * (Q x1 -* R1) /\
EX (x2:A), P x2 * (Q x2 -* R2)
--------------
EX (x :A), P x  * (Q x -* R1 /\ R2)


without EX:

    P * (Q -* R1) /\ P * (Q -* R2)
=>  P * (Q -* R1 /\ Q -* R2)          (precise of P)
=>  P * (Q -* R1 /\ R2)

              R1 /\ R2 |-- R1 /\ R2
           => Q * (Q -* R1) /\ Q * (Q -* R2) |-- R1 /\ R2
           => Q * (Q -* R1 /\ Q -* R2) |-- R1 /\ R2       (precise of Q)
           => Q -* R1 /\ Q -* R2 |-- Q -* R1 /\ R2 


if (EX x, P x) is precise and (EX x, Q x) is precise

EX x, (Q x -* R) * (EX x, Q x)
|--  -* R)


    EX (x1:A), P x1 * (Q x1 -* R1) /\  EX (x2:A), P x2 * (Q x2 -* R2)
=>  (EX (x1:A), P x1) * (EX (x1:A), Q x1 -* R1) 
 /\ (EX (x2:A), P x2) * (EX (x2:A), Q x2 -* R2)
=> (EX (x1:A), P x1) * ((EX (x1:A), Q x1 -* R1) /\ EX (x2:A), Q x2 -* R2)


      =>   (ALL x:A, Q x1) * 
            ((EX (x1:A), Q x1 -* R1) /\ ((EX (x2:A), Q x2 -* R2)
      =>   (ALL x:A, Q x1) * ((EX (x1:A), Q x1 -* R1) 
        /\ (ALL x:A, Q x1) * ((EX (x2:A), Q x2 -* R2)
      => 
      
((EX (x1:A), Q x1 -* R1) /\ EX (x2:A), Q x2 -* R2) |-- 
      => 

--------------
EX (x2:A), P x2 * (Q x2 -* R1 /\ R2)


*)



Definition sgn_C :=
Cgiven Z Z_inhabited _
(fun x =>
Csequence
(Cassert (PROP (Int.min_signed <= x <= Int.max_signed) LOCAL (temp _x  (Vint (Int.repr x))) SEP ()))
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

Compute (S_split sgn_S).
Compute (C_split sgn_S sgn_C).

