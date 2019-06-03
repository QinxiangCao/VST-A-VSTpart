Require Export VST.floyd.proofauto.
Require Export annotated_Clight.

Lemma decorate_C_skip: forall P,
  P ->
  let d := @abbreviate _ Sskip in P.
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
      (let d := @abbreviate _ s1 in semax Delta P c1 (overridePost Q Post)) ->
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
    forall d1 Inv1 Inv2 d2 d3 Delta P c Post,
      (let d := @abbreviate _ d1 in semax Delta P c Post) ->
      (let d := @abbreviate _ (Ssequence (Sloop Inv1 Inv2 d1 d2) d3) in semax Delta P c Post).
Proof.
  intros.
  exact H.
Qed.

Lemma decorate_C_loop_incr:
  forall {Espec: OracleKind} {cs: compspecs},
    forall d1 Inv1 Inv2 d2 d3 Delta P c Post,
      (let d := @abbreviate _ d2 in semax Delta P c Post) ->
      (let d := @abbreviate _ (Ssequence (Sloop Inv1 Inv2 d1 d2) d3) in semax Delta P c Post).
Proof.
  intros.
  exact H.
Qed.

Lemma decorate_C_loop_after:
  forall {Espec: OracleKind} {cs: compspecs},
    forall d1 Inv1 Inv2 d2 d3 Delta P c Post,
      (let d := @abbreviate _ d3 in semax Delta P c Post) ->
      (let d := @abbreviate _ (Ssequence (Sloop Inv1 Inv2 d1 d2) d3) in semax Delta P c Post).
Proof.
  intros.
  exact H.
Qed.

Lemma decorate_C_step2:
  forall {Espec: OracleKind} {cs: compspecs},
    forall d1 d2 Delta P c Post,
      (* should check d1 not Sassert or Sassume *)
      (let d := @abbreviate _ d2 in semax Delta P c Post) ->
      (let d := @abbreviate _ (Ssequence d1 d2) in semax Delta P c Post).
Proof.
  intros.
  exact H.
Qed.

Lemma decorate_C_step1:
  forall {Espec: OracleKind} {cs: compspecs},
    forall (d1: statement) Delta P c Post,
      (* should check d1 not Sassert or Sassume *)
      semax Delta P c Post ->
      (let d := @abbreviate _ d1 in semax Delta P c Post).
Proof.
  intros.
  exact H.
Qed.



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


Lemma decorate_C_given:
  forall {Espec: OracleKind} {cs: compspecs},
    forall {A: Type} d1 Delta P c Post,
      (forall a, let d := @abbreviate _ (d1 a) in semax Delta (P a) c Post) ->
      (let d := @abbreviate _ (Sgiven A d1) in semax Delta (exp P) c Post).
Proof.
  intros.
  Intros a.
  apply H.
Qed.

Lemma decorate_C_given':
  forall {Espec: OracleKind} {cs: compspecs},
    forall {A: Type} a d1 Delta P c Post,
      (let d := @abbreviate _ (d1 a) in semax Delta P c Post) ->
      (let d := @abbreviate _ (Sgiven A d1) in semax Delta P c Post).
Proof.
  intros.
  apply H.
Qed.

Tactic Notation "forwardD" :=
  lazymatch goal with
  | |- let d := @abbreviate _ Sskip in _ =>
      refine (decorate_C_skip _ _)
  | |- let d := @abbreviate _ (Ssequence _ (Ssequence (Sassert ?P) _)) in _ => 
      refine (decorate_C_assert2 _ _ _ _ _ _ _ _ _ _);
      [ intro d; abbreviate_semax; revert d
      | intro d; abbreviate_semax; revert d
      ]
  | |- let d := @abbreviate _ (Ssequence (Sifthenelse _ _ _) _) in
       (* semax _ _ (Clight.Sifthenelse _ _ _) _ => *)
       _ =>
      intro d; forward_if;
      [ ..
      | revert d; refine (decorate_C_if_then _ _ _ _ _ _ _ _ _)
      | revert d; refine (decorate_C_if_else _ _ _ _ _ _ _ _ _)]
  | |- let d := @abbreviate _ (Ssequence (Swhile ?Inv _ _) _) in
       (* semax _ _ (Clight.Ssequence (Clight.Swhile _ _) _) _ => *)
       _ =>
      intro d; forward_while Inv;
      [ ..
      | revert d; refine (decorate_C_while_body _ _ _ _ _ _ _ _ _)
      | revert d; refine (decorate_C_while_after _ _ _ _ _ _ _ _ _)]
  | |- let d := @abbreviate _ (Ssequence (Sloop ?Inv1 ?Inv2 _ _) _) in
       (* semax _ _ (Clight.Ssequence (Clight.Sloop _ _) _) _ => *)
       _ =>
      intro d; forward_loop Inv1 continue:Inv2;
      [ ..
      | revert d; refine (decorate_C_loop_body _ _ _ _ _ _ _ _ _ _)
      | revert d; refine (decorate_C_loop_incr _ _ _ _ _ _ _ _ _ _)
      | revert d; refine (decorate_C_loop_after _ _ _ _ _ _ _ _ _ _)]
  | |- let d := @abbreviate _ (Sgiven _ (fun x => _)) in
       semax _ _ _ _ =>
      refine (decorate_C_given _ _ _ _ _ _); intros x d; Intros; revert d
  | |- let d := @abbreviate _ (Ssequence (Sassert ?P) _) in
       semax _ _ _ _ =>
      refine (decorate_C_assert P _ _ _ _ _ _ _)
  | |- let d := @abbreviate _ (Ssequence _ _) in
       semax _ _ (Clight.Ssequence _ _) _ =>
      intro d;
      forward;
      revert d;
      refine (decorate_C_step2 _ _ _ _ _ _ _)
  | |- let d := @abbreviate _ _ in
       semax _ _ _ _ =>
      refine (decorate_C_step1 _ _ _ _ _ _);
      forward
  end.

Tactic Notation "forwardD" constr(a) :=
  match goal with
  | |- let d := @abbreviate _ (Sgiven _ (fun x => _)) in
       semax _ _ _ _ =>
      refine (decorate_C_given' a _ _ _ _ _ _); intros d; Intros; revert d
  end.
