Require Split.soundness.

Print Assumptions Split.soundness.soundness.

Print FileDependGraph Split Split.soundness.

(**
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
defs.classic : forall P : Prop, P \/ ~ P
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
*)