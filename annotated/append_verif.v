(************************************************************)
(************************************************************)
(**                                                        **)
(**                                                        **)
(**      Definitions and tactics for decorated program.    **)
(**                                                        **)
(**                                                        **)
(************************************************************)
(************************************************************)


Require Import annotation_proofauto.
Require Import append.
Require Import append_def.
Require Import append_annotation.

(************************************************************)
(************************************************************)
(**                                                        **)
(**                                                        **)
(**                       THE  PROOF                       **)
(**                                                        **)
(**                                                        **)
(************************************************************)
(************************************************************)
(*
Definition DC (sh: share) (s1 s2: list val) (x: val) (y: val): statement :=
(Sifthenelse (Ebinop Oeq (Etempvar _x (tptr (Tstruct _list noattr)))
               (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
  (Sreturn (Some (Etempvar _y (tptr (Tstruct _list noattr)))))
  (Ssequence
    (Sset _t (Etempvar _x (tptr (Tstruct _list noattr))))
    
    (Ssequence
      (Sassert (EX a: val, EX s1b: list val,
        (PROP (s1 = a :: s1b)
         LOCAL (temp _t x; temp _x x; temp _y y)
         SEP (listrep sh s1 x; listrep sh s2 y))))
    (GIVEN a: val, GIVEN s1b: list val,
    (Ssequence
      (Sassert (EX u: val,
        (PROP ()
         LOCAL (temp _t x; temp _x x; temp _y y)
         SEP (data_at sh t_struct_list (a ,u) x; listrep sh s1b u; listrep sh s2 y)))%assert)
    (GIVEN u: val,
    
    (Ssequence
      (Sset _u
        (Efield
          (Ederef (Etempvar _t (tptr (Tstruct _list noattr)))
            (Tstruct _list noattr)) _tail (tptr (Tstruct _list noattr))))
      (Ssequence
        (Swhile
          
      (EX a: val, EX s1b: list val, EX t: val, EX u: val,
            PROP ()
            LOCAL (temp _x x; temp _t t; temp _u u; temp _y y)
            SEP (listrep sh (a::s1b++s2) t -* listrep sh (s1++s2) x;
                   data_at sh t_struct_list (a,u) t;
                   listrep sh s1b u;
                   listrep sh s2 y))%assert
      
          (Ebinop One (Etempvar _u (tptr (Tstruct _list noattr)))
            (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
          
        (GIVEN a: val, GIVEN s1b: list val, GIVEN t: val, GIVEN u: val,
        (Ssequence
            (Sassert (EX b: val, EX s1c: list val, EX z: val,
              (PROP (s1b = b :: s1c)
               LOCAL (temp _x x; temp _t t; temp _u u; temp _y y)
               SEP (listrep sh (a :: s1b ++ s2) t -* listrep sh (s1 ++ s2) x;
                    data_at sh t_struct_list (a, u) t;
                    data_at sh t_struct_list (b, z) u;
                    listrep sh s1c z; listrep sh s2 y)))%assert)
          (GIVEN b: val, GIVEN s1c: list val, GIVEN z: val,
        
          (Ssequence
            (Sset _t (Etempvar _u (tptr (Tstruct _list noattr))))
            (Sset _u
              (Efield
                (Ederef (Etempvar _t (tptr (Tstruct _list noattr)))
                  (Tstruct _list noattr)) _tail
                (tptr (Tstruct _list noattr))))
            )))))
        (Ssequence
          (Sassign
            (Efield
              (Ederef (Etempvar _t (tptr (Tstruct _list noattr)))
                (Tstruct _list noattr)) _tail (tptr (Tstruct _list noattr)))
            (Etempvar _y (tptr (Tstruct _list noattr))))
          (Sreturn (Some (Etempvar _x (tptr (Tstruct _list noattr)))))
          ))))))))). *)

(************************************************************)
(************************************************************)
(**                                                        **)
(**                                                        **)
(**              Check the side conditions                 **)
(**                                                        **)
(**                                                        **)
(************************************************************)
(************************************************************)

Lemma body_append: semax_body Vprog Gprog append.f_append append_spec.
Proof.
start_function.
match goal with
| |- ?P => let d1 := eval hnf in (fn_body f_append) in
           change (let d := @abbreviate _ d1 in P)
end.
forwardD sh.
forwardD s1.
forwardD s2.
forwardD x.
forwardD y.
forwardD.
* forwardD.
  rewrite listrep_null. normalize.
  Exists y.
  simpl; entailer!.
* forwardD.
  forwardD.
  {
    destruct s1 as [| a s1b]; [unfold listrep at 1; fold listrep; normalize; entailer! |].
    Exists a s1b.
    entailer!.
  }
  forwardD.
  forwardD.
  forwardD.
  {
    subst s1.
    unfold listrep at 1; fold listrep.
    Intros u; Exists u.
    entailer!.
  }
  forwardD.
  forwardD.
  forwardD.
  {
    Exists a s1b x u.
    subst s1. entailer!. cancel_wand.
  }
  {
    entailer!.
  }
  {
    clear a s1b H0 u.
    rename a0 into a, s1b0 into s1b, u0 into u.
    forwardD a.
    forwardD s1b.
    forwardD t.
    forwardD u.
    forwardD.
    {
      destruct s1b as [| b s1c]; unfold listrep at 3; fold listrep; [ Intros; contradiction |].
      Intros z.
      Exists b s1c z.
      entailer!.
    }
    forwardD.
    forwardD.
    forwardD.
    forwardD.
    forwardD.
    {
      Exists (b,s1c,u,z). unfold fst, snd.
      simpl app.
      entailer!.
      rewrite sepcon_comm.
      apply RAMIF_PLAIN.trans''.
      apply wand_sepcon_adjoint.
      simpl.
      forget (b::s1c++s2) as s3.
      unfold listrep; fold listrep; Exists u; auto.
    }
  }
  clear a s1b H0 u.
  rename a0 into a, s1b0 into s1b, u0 into u.
  forwardD.
  forwardD.
  {
    rewrite (proj1 H2 (eq_refl _)).
    Exists x.
    simpl app.
    clear.
    entailer!.
    unfold listrep at 3; fold listrep. normalize.
    pull_right (listrep sh (a :: s2) t -* listrep sh (s1 ++ s2) x).
    apply modus_ponens_wand'.
    unfold listrep at 2; fold listrep. Exists y; auto.
  }
Qed.

