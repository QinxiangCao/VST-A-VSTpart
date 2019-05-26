Require Export VST.floyd.proofauto.
Require Export annotated_Clight.

(*
Definition Sdowhile (s: statement) (e: expr) :=
  Sloop s (Sifthenelse e Sskip Sbreak).

Definition Sfor (s1: statement) (e2: expr) (s3: statement) (s4: statement) :=
  Ssequence s1 (Sloop (Ssequence (Sifthenelse e2 Sskip Sbreak) s3) s4).
 *)

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
  match goal with
  | |- let d := @abbreviate _ (Sifthenelse _ _ _) in
       semax _ _ (Clight.Sifthenelse _ _ _) _ =>
      intro d; forward_if;
      [ ..
      | revert d; refine (decorate_C_if_then1 _ _ _ _ _ _ _ _)
      | revert d; refine (decorate_C_if_else1 _ _ _ _ _ _ _ _)]
  | |- let d := @abbreviate _ (Ssequence (Swhile ?Inv _ _) _) in
       semax _ _ (Clight.Ssequence (Clight.Swhile _ _) _) _ =>
      intro d; forward_while Inv;
      [ ..
      | revert d; refine (decorate_C_while_body2 _ _ _ _ _ _ _ _ _)
      | revert d; refine (decorate_C_while_after2 _ _ _ _ _ _ _ _ _)]
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
