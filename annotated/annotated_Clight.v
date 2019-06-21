(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation, either version 2 of the License, or  *)
(*  (at your option) any later version.  This file is also distributed *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** The Clight language: a simplified version of Compcert C where all
  expressions are pure and assignments and function calls are
  statements, not expressions. *)

Require Import Coqlib.
Require Import Errors.
Require Import Maps.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import AST.
Require Import Memory.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Ctypes.
Require Import Cop.
Require Import Clight.
Require Export VST.floyd.proofauto.

Definition assert := (environ -> mpred).

Inductive loop_invariant :=
  | LISingle : assert -> loop_invariant
  | LIDouble : assert -> assert -> loop_invariant.

(** ** Statements *)

(** This is statement with annotation *)

Inductive statement : Type :=
  | Sassert : assert -> statement
  | Sdummyassert : assert -> statement
  | Sgiven: forall A: Type, (A -> statement) -> statement
  | Sskip : statement                   (**r do nothing *)
  | Sassign : expr -> expr -> statement (**r assignment [lvalue = rvalue] *)
  | Sset : ident -> expr -> statement   (**r assignment [tempvar = rvalue] *)
  | Scall: option ident -> expr -> list expr -> statement (**r function call *)
  | Sbuiltin: option ident -> external_function -> typelist -> list expr -> statement (**r builtin invocation *)
  | Ssequence : statement -> statement -> statement  (**r sequence *)
  | Sifthenelse : expr  -> statement -> statement -> statement (**r conditional *)
  | Sloop: loop_invariant -> statement -> statement -> statement (**r infinite loop *)
  | Sbreak : statement                      (**r [break] statement *)
  | Scontinue : statement                   (**r [continue] statement *)
  | Sreturn : option expr -> statement      (**r [return] statement *)
  | Sswitch : expr -> labeled_statements -> statement  (**r [switch] statement *)
  | Slabel : label -> statement -> statement
  | Sgoto : label -> statement

with labeled_statements : Type :=            (**r cases of a [switch] *)
  | LSnil: labeled_statements
  | LScons: option Z -> statement -> labeled_statements -> labeled_statements.
                      (**r [None] is [default], [Some x] is [case x] *)

Notation "'GIVEN' x .. y , c " :=
  (Sgiven _ (fun x => .. (Sgiven _ (fun y => c)) ..)) (at level 65, x binder, y binder) : logic.
(* Notation "'GIVEN' (x1 : T1) , (x2 : T2) , .. , (xn : Tn) , c " :=
  (Sgiven T1 (fun x1 => (Sgiven T2 (fun x2 => .. (Sgiven Tn (fun xn => c)) .. )))) (at level 65, x1 at level 99, x2 at level 99) : logic. *)
(* Notation "'GIVEN'  x ':' T ',' c " := (Sgiven _ (fun x : T => c)) (at level 65, x at level 99) : logic. *)

Definition Swhile (Inv: assert) (e: expr) (s: statement):=
  Sloop (LISingle Inv) (Ssequence (Sifthenelse e Sskip Sbreak) s) Sskip.

(** ** Functions *)

(** A function definition is composed of its return type ([fn_return]),
  the names and types of its parameters ([fn_params]), the names
  and types of its local variables ([fn_vars]), and the body of the
  function (a statement, [fn_body]). *)

Record function : Type := mkfunction {
  fn_return: type;
  fn_callconv: calling_convention;
  fn_params: list (ident * type);
  fn_vars: list (ident * type);
  fn_temps: list (ident * type);
  fn_body: statement
}.

Definition var_names (vars: list(ident * type)) : list ident :=
  List.map (@fst ident type) vars.

(** Functions can either be defined ([Internal]) or declared as
  external functions ([External]). *)

Definition fundef := Ctypes.fundef function.

(** The type of a function definition. *)

Definition type_of_function (f: function) : type :=
  Tfunction (type_of_params (fn_params f)) (fn_return f) (fn_callconv f).

Definition type_of_fundef (f: fundef) : type :=
  match f with
  | Internal fd => type_of_function fd
  | External id args res cc => Tfunction args res cc
  end.

(** ** Programs *)

(** As defined in module [Ctypes], a program, or compilation unit, is
  composed of:
- a list of definitions of functions and global variables;
- the names of functions and global variables that are public (not static);
- the name of the function that acts as entry point ("main" function).
- a list of definitions for structure and union names
- the corresponding composite environment
- a proof that this environment is consistent with the definitions. *)

Definition program := Ctypes.program function.

(** Generate VST funcspec from annotation funcspec *)

Ltac move_let_inside v :=
  lazymatch goal with
  | v := let (a, b) := _ in _ |- _ =>
    lazymatch goal with
    | v := let (a, b) := ?p in fun x:?T => ?content |- _ =>
      let temp := fresh "temp" in
      refine (fun x => _);
      pose (temp := (fun x:T => let (a, b) := p in content) x);
      hnf in temp;
      clear v;
      rename temp into v;
      move_let_inside v
    | v := let (a, b) := ?p in (?pre, ?post) |- _ =>
      exact (let (a, b) := p in pre, let (a, b) := p in post)
    | _ => fail 0 v "is not recognized"
    end
  | _ => fail 0 v "must have form let (a, b) := p in _"
  end.

Ltac uncurry_funcspec spec :=
  let spec_name := fresh "spec" in
  let spec := eval unfold spec in spec in
  pose (spec_name := spec);
  repeat
    lazymatch goal with
    | spec_name := fun x:?T1 => fun y:?T2 => ?spec |- _ =>
      first [ignore (T2 : _) | fail 2 "funcspec cannot have dependent type"];
      first [
        let spec_name1 := fresh "spec" in
        pose (spec_name1 := (fun p : (T1*T2) => let (x, y) := p in spec));
        clear spec_name;
        rename spec_name1 into spec_name;
        refine (let spec_name1 :=
          ltac:(
            match goal with
            | spec_name := ?spec |- _ =>
            let spec := eval unfold spec_name in spec_name in
            let p := fresh "p" in
            intro p;
            pose (spec_name1 := spec p);
            hnf in spec_name1;
            clear spec_name;
            rename spec_name1 into spec_name;
            move_let_inside spec_name;
            exact spec_name
            end
          ) in _);
        clear spec_name;
        rename spec_name1 into spec_name;
        cbv beta zeta in spec_name
      | fail 2 "Unknown error: failed to uncurry funcspec"
      ]
    end;
  exact spec_name.

Ltac make_funcspec name funsig spec :=
  let spec := eval cbv beta zeta delta [spec] in spec in
  lazymatch spec with
  | fun x:?T => (?P, ?Q) =>
    exact (name, NDmk_funspec funsig cc_default T (fun x => P) (fun x => Q))
  | _ => fail 0 spec "is not in valid form of funcspec"
  end.
