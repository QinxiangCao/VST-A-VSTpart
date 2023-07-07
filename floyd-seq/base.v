From compcert Require Export Clightdefs.
Require Export VST.veric.base.
Require Export VST.veric.SeparationLogic.
Require Export VST.msl.Extensionality.
Require Export compcert.lib.Coqlib.
Require Export VST.msl.Coqlib2 VST.veric.coqlib4 VST.floyd.coqlib3.
Require Export VST.veric.juicy_extspec.
Require Import VST.veric.NullExtension.
Require Export VST.floyd.jmeq_lemmas.
Require Export VST.floyd.find_nth_tactic.
Require Export VST.floyd.val_lemmas.
Require Export VST.floyd.assert_lemmas.
Require Export VST.floyd.base.
Require Csplit.strong.

Local Open Scope logic.

(* Locate semax. *)

Definition extract_exists_pre:
  forall {CS: compspecs} {Espec: OracleKind},
  forall (A : Type) (P : A -> environ->mpred) c (Delta: tycontext) (R: ret_assert),
  (forall x, @strong.semax CS Espec Delta (P x) c R) ->
   @strong.semax CS Espec Delta (EX x:A, P x) c R
  := @strong.semax_extract_exists.

Arguments alignof_two_p {env} t.

