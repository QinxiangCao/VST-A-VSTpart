Require Export VST.floyd.proofauto.
Require Export annotated_Clight.

(********** annotation handling lemmas ****************************************)

Lemma decorate_C_skip: forall P,
  P ->
  let d := @abbreviate _ Sskip in P.
Proof.
  intros. assumption.
Qed.

Lemma decorate_C_dummyassert: forall Q s P,
  (let d := @abbreviate _ s in P) ->
  let d := @abbreviate _ (Ssequence (Sdummyassert Q) s) in P.
Proof.
  intros. assumption.
Qed.

Lemma decorate_C_step: forall P s1 s2,
  (let d := @abbreviate _ s2 in P) ->
  (let d := @abbreviate _ (Ssequence s1 s2) in P).
Proof.
  intros. assumption.
Qed.

Lemma decorate_C_assert:
  forall {Espec: OracleKind} {cs: compspecs},
    forall P' d1 Delta P c Post,
      ENTAIL Delta, P |-- P' ->
      (let d := @abbreviate _ d1 in semax Delta P' c Post) ->
      (let d := @abbreviate _ (Ssequence (Sassert P') d1) in semax Delta P c Post).
Proof.
  intros.
  eapply semax_pre.
  + exact H.
  + exact H0.
Qed.

(* may not find correct seq *)
Lemma decorate_C_assert2:
  forall {Espec: OracleKind} {cs: compspecs},
    forall Q s1 s2 Delta P c1 c2 Post,
      (let d := @abbreviate _ (Ssequence s1 Sskip) in semax Delta P c1 (overridePost Q Post)) ->
      (let d := @abbreviate _ s2 in semax Delta Q c2 Post) ->
      (let d := @abbreviate _ (Ssequence s1 (Ssequence (Sassert Q) s2)) in semax Delta P (Clight.Ssequence c1 c2) Post).
Proof.
  intros. eapply semax_seq.
  + exact H.
  + exact H0.
Qed.

Lemma decorate_C_if_then:
  forall {Espec: OracleKind} {cs: compspecs},
    forall b d1 d2 d3 Delta P c Post,
      (let d := @abbreviate _ d1 in semax Delta P c Post) ->
      (let d := @abbreviate _ (Ssequence (Sifthenelse b d1 d2) d3) in semax Delta P c Post).
Proof.
  intros.
  exact H.
Qed.

Lemma decorate_C_if_else:
  forall {Espec: OracleKind} {cs: compspecs},
    forall b d1 d2 d3 Delta P c Post,
      (let d := @abbreviate _ d2 in semax Delta P c Post) ->
      (let d := @abbreviate _ (Ssequence (Sifthenelse b d1 d2) d3) in semax Delta P c Post).
Proof.
  intros.
  exact H.
Qed.

Lemma decorate_C_while_body:
  forall {Espec: OracleKind} {cs: compspecs},
    forall b d1 Inv d2 Delta P c Post,
      (let d := @abbreviate _ d1 in semax Delta P c Post) ->
      (let d := @abbreviate _ (Ssequence (Swhile Inv b d1) d2) in semax Delta P c Post).
Proof.
  intros.
  exact H.
Qed.

Lemma decorate_C_while_after:
  forall {Espec: OracleKind} {cs: compspecs},
    forall b d1 Inv d2 Delta P c Post,
      (let d := @abbreviate _ d2 in semax Delta P c Post) ->
      (let d := @abbreviate _ (Ssequence (Swhile Inv b d1) d2) in semax Delta P c Post).
Proof.
  intros.
  exact H.
Qed.

Lemma decorate_C_loop_body:
  forall {Espec: OracleKind} {cs: compspecs},
    forall d1 Inv d2 d3 Delta P c Post,
      (let d := @abbreviate _ d1 in semax Delta P c Post) ->
      (let d := @abbreviate _ (Ssequence (Sloop Inv d1 d2) d3) in semax Delta P c Post).
Proof.
  intros.
  exact H.
Qed.

Lemma decorate_C_loop_incr:
  forall {Espec: OracleKind} {cs: compspecs},
    forall d1 Inv d2 d3 Delta P c Post,
      (let d := @abbreviate _ d2 in semax Delta P c Post) ->
      (let d := @abbreviate _ (Ssequence (Sloop Inv d1 d2) d3) in semax Delta P c Post).
Proof.
  intros.
  exact H.
Qed.

Ltac fill_decorate_C_loop_after d :=
  match d with
  | Ssequence Sbreak ?d2 => refine d2
  | Ssequence ?d1 ?d2 =>
      first [fill_decorate_C_loop_after d1 | fill_decorate_C_loop_after d2]
  | Sgiven ?A ?d1 =>
    match d1 with
    | (fun x => _) =>
        refine (Sgiven A _); first [intro x | let x1 := fresh x in rename x into x1; intro x];
        let d2 := eval cbv beta in (d1 x) in fill_decorate_C_loop_after d2
    end
  | Sifthenelse _ ?d1 ?d2 =>
      first [fill_decorate_C_loop_after d1 | fill_decorate_C_loop_after d2]
  | _ => fail
  end.

Ltac fill_decorate_C_loop_after2 :=
  match goal with
  | d := @abbreviate _ (Ssequence (Sloop _ ?d1 ?d2) _) |- _ =>
      fill_decorate_C_loop_after d1
  end.

Lemma decorate_C_loop_after:
  forall {Espec: OracleKind} {cs: compspecs},
    forall (d1 d2: statement) Delta P c Post,
      (let d := @abbreviate _ d1 in semax Delta P c Post) ->
      (let d := @abbreviate _ d2 in semax Delta P c Post).
Proof.
  intros.
  exact H.
Qed.

Lemma decorate_C_step2:
  forall {Espec: OracleKind} {cs: compspecs},
    forall d1 d2 P,
      (* should check d1 not Sassert or Sassume *)
      (let d := @abbreviate _ d2 in P) ->
      (let d := @abbreviate _ (Ssequence d1 d2) in P).
Proof.
  intros.
  assumption.
Qed.

Lemma decorate_C_step1:
  forall {Espec: OracleKind} {cs: compspecs},
    forall (d1: statement) P,
      (* should check d1 not Sassert or Sassume *)
      P ->
      (let d := @abbreviate _ d1 in P).
Proof.
  intros.
  assumption.
Qed.

(*
Lemma decorate_C_if_then1:
  forall {Espec: OracleKind} {cs: compspecs},
    forall b d1 d2 Delta P c Post,
      (let d := @abbreviate _ d1 in semax Delta P c Post) ->
      (let d := @abbreviate _ (Sifthenelse b d1 d2) in semax Delta P c Post).
Proof.
  intros.
  exact H.
Qed.

Lemma decorate_C_if_else1:
  forall {Espec: OracleKind} {cs: compspecs},
    forall b d1 d2 Delta P c Post,
      (let d := @abbreviate _ d2 in semax Delta P c Post) ->
      (let d := @abbreviate _ (Sifthenelse b d1 d2) in semax Delta P c Post).
Proof.
  intros.
  exact H.
Qed.

Lemma decorate_C_if_then2:
  forall {Espec: OracleKind} {cs: compspecs},
    forall b d1 d2 Q d3 Delta P c Post,
      (let d := @abbreviate _ d1 in semax Delta P c Post) ->
      (let d := @abbreviate _ (Ssequence (Sifthenelse b d1 d2) (Ssequence (Sassert Q) d3)) in semax Delta P c Post).
Proof.
  intros.
  exact H.
Qed.

Lemma decorate_C_if_else2:
  forall {Espec: OracleKind} {cs: compspecs},
    forall b d1 d2 Q d3 Delta P c Post,
      (let d := @abbreviate _ d2 in semax Delta P c Post) ->
      (let d := @abbreviate _ (Ssequence (Sifthenelse b d1 d2) (Ssequence (Sassert Q) d3)) in semax Delta P c Post).
Proof.
  intros.
  exact H.
Qed.
*)

(*
Lemma decorate_C_while_body2:
  forall {Espec: OracleKind} {cs: compspecs},
    forall b d1 Inv d2 Delta P c Post,
      (let d := @abbreviate _ d1 in semax Delta P c Post) ->
      (let d := @abbreviate _ (Ssequence (Swhile Inv b d1) d2) in semax Delta P c Post).
Proof.
  intros.
  exact H.
Qed.

Lemma decorate_C_while_after2:
  forall {Espec: OracleKind} {cs: compspecs},
    forall b d1 Inv d2 Delta P c Post,
      (let d := @abbreviate _ d2 in semax Delta P c Post) ->
      (let d := @abbreviate _ (Ssequence (Swhile Inv b d1) d2) in semax Delta P c Post).
Proof.
  intros.
  exact H.
Qed.
*)

(* Lemma decorate_C_assert:
  forall {Espec: OracleKind} {cs: compspecs},
    forall P' d1 Delta P c Post,
      ENTAIL Delta, P |-- P' ->
      (let d := @abbreviate _ d1 in semax Delta P' c Post) ->
      (let d := @abbreviate _ (Ssequence (Sassert P') d1) in semax Delta P c Post).
Proof.
  intros.
  eapply semax_pre.
  + exact H.
  + exact H0.
Qed.

Lemma decorate_C_assert2:
  forall {Espec: OracleKind} {cs: compspecs},
    forall P' d1 d2 Delta P c Post,
      ENTAIL Delta, P |-- P' ->
      (let d := @abbreviate _ d1 in semax Delta P' c Post) ->
      (let d := @abbreviate _ (Ssequence d1 (Ssequence (Sassert P') d2)) in semax Delta P c Post).
Proof.
  intros.
  eapply semax_pre.
  + exact H.
  + exact H0.
Qed. *)

Definition Intros_tag {A} (x : A) := True.

Lemma decorate_C_given:
  forall {Espec: OracleKind} {cs: compspecs},
    forall {A: Type} d1 Delta P c Post,
      (forall a, Intros_tag a -> let d := @abbreviate _ (d1 a) in semax Delta (P a) c Post) ->
      (let d := @abbreviate _ (Sgiven A d1) in semax Delta (exp P) c Post).
Proof.
  intros.
  Intros a.
  apply H. apply I.
Qed.

Lemma decorate_C_given':
  forall {Espec: OracleKind} {cs: compspecs},
    forall {A: Type} a d1 Delta P c Post,
      (Intros_tag a -> let d := @abbreviate _ (d1 a) in semax Delta P c Post) ->
      (let d := @abbreviate _ (Sgiven A d1) in semax Delta P c Post).
Proof.
  intros.
  apply H. apply I.
Qed.

Lemma delta_derives_refl:
  forall Delta P,
    ENTAIL Delta, P |-- P.
Proof.
  intros. apply andp_left2. apply derives_refl.
Qed.

Tactic Notation "forwardD" :=
  lazymatch goal with
  (* entailment *)
  | |- let d := @abbreviate _ _ in ENTAIL _, _ |-- _ =>
      intro d; clear d
  (* skip *)
  | |- let d := @abbreviate _ Sskip in _ =>
      refine (decorate_C_skip _ _)
  (* dummyassert *)
  | |- let d := @abbreviate _ (Ssequence (Sdummyassert _) _) in _ =>
      refine (decorate_C_dummyassert _ _ _ _)
  (* assert as postcondition *)
  | |- let d := @abbreviate _ (Ssequence _ (Ssequence (Sassert ?P) _)) in _ => 
      refine (decorate_C_assert2 _ _ _ _ _ _ _ _ _ _);
      [ intro d; abbreviate_semax; revert d
      | intro d; abbreviate_semax; revert d
      ]
  (* if *)
  | |- let d := @abbreviate _ (Ssequence (Sifthenelse _ _ _) _) in
       (* semax _ _ (Clight.Sifthenelse _ _ _) _ => *)
       _ =>
      intro d; forward_if;
      [ ..
      | revert d; refine (decorate_C_if_then _ _ _ _ _ _ _ _ _)
      | revert d; refine (decorate_C_if_else _ _ _ _ _ _ _ _ _)]
  (* while *)
  | |- let d := @abbreviate _ (Ssequence (Swhile ?Inv _ _) _) in
       (* semax _ _ (Clight.Ssequence (Clight.Swhile _ _) _) _ => *)
       _ =>
      intro d; forward_while Inv;
      [ ..
      | revert d; refine (decorate_C_while_body _ _ _ _ _ _ _ _ _)
      | revert d; refine (decorate_C_while_after _ _ _ _ _ _ _ _ _)]
  (* loop single inv *)
  | |- let d := @abbreviate _ (Ssequence (Sloop (LISingle ?Inv) _ _) _) in
       semax _ _ (Clight.Sloop _ _) _ =>
      intro d; forward_loop Inv;
      [ ..
      | revert d; refine (decorate_C_loop_body _ _ _ _ _ _ _ _ _)]
  (* loop double inv *)
  | |- let d := @abbreviate _ (Ssequence (Sloop (LIDouble ?Inv1 ?Inv2) _ _) _) in
       semax _ _ (Clight.Sloop _ _) _ =>
      intro d; forward_loop Inv1 continue: Inv2;
      [ ..
      | revert d; refine (decorate_C_loop_body _ _ _ _ _ _ _ _ _)
      | revert d; refine (decorate_C_loop_incr _ _ _ _ _ _ _ _ _)]
  (* loop single inv without postcondition *)
  | |- let d := @abbreviate _ (Ssequence (Sloop (LISingle ?Inv) _ _) _) in
       (* semax _ _ (Clight.Ssequence (Clight.Sloop _ _) _) _ => *)
       _ =>
      let Post := fresh "Post" in
      evar (Post : assert);
      intro d;
      set (d1 := ltac: (fill_decorate_C_loop_after2));
      forward_loop Inv break: Post;
      [ ..
      | revert d; refine (decorate_C_loop_body _ _ _ _ _ _ _ _ _)
      | revert d; refine (decorate_C_loop_after d1 _ _ _ _ _ _)]
  (* loop double inv without postcondition*)
  | |- let d := @abbreviate _ (Ssequence (Sloop (LIDouble ?Inv1 ?Inv2) _ _) _) in
       (* semax _ _ (Clight.Ssequence (Clight.Sloop _ _) _) _ => *)
       _ =>
      let Post := fresh "Post" in
      evar (Post : assert);
      set (d1 := ltac: (fill_decorate_C_loop_after2));
      intro d; forward_loop Inv1 continue: Inv2 break: Post;
      [ ..
      | revert d; refine (decorate_C_loop_body _ _ _ _ _ _ _ _ _)
      | revert d; refine (decorate_C_loop_incr _ _ _ _ _ _ _ _ _)
      | revert d; refine (decorate_C_loop_after d1 _ _ _ _ _ _)]
  (* given *)
  | |- let d := @abbreviate _ (Sgiven _ (fun x => _)) in
       semax _ _ _ _ =>
      refine (decorate_C_given _ _ _ _ _ _);
      first
      [ intro x
      | let old_x := fresh x in rename x into old_x; intro x];
      intros ? d;
      repeat match goal with
      | |- semax _ (EX (_ : ?P), _) _ _ =>
        match type of P with
        | Prop => let H := fresh "H" in Intro H
        end
      end;
      Intros;
      revert d
      ;try match goal with
      | |- let d := @abbreviate _ (Ssequence (Sdummyassert _) _) in _ =>
      refine (decorate_C_dummyassert _ _ _ _)
      end
  | |- let d := @abbreviate _ (Ssequence (Sassert ?P) _) in
       semax _ _ _ _ =>
      refine (decorate_C_assert P _ _ _ _ _ _ _)
  | |- let d := @abbreviate _ (Ssequence _ _) in
       semax _ _ (Clight.Ssequence _ _) _ =>
      intro d;
      forward;
      revert d;
      refine (decorate_C_step2 _ _ _ _)
  | |- let d := @abbreviate _ _ in
       semax _ _ _ _ =>
      refine (decorate_C_step1 _ _ _);
      forward
  end.

Tactic Notation "forwardD" constr(a) :=
  match goal with
  | |- let d := @abbreviate _ (Sgiven _ (fun x => _)) in
       semax _ _ _ _ =>
      refine (decorate_C_given' a _ _ _ _ _ _); intros ? d; Intros; revert d
  end.
