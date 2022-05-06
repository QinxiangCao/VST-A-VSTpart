Require Import Ctypes ClightC AClight.
Require Import Coqlib Errors String List.

(** Pulling local scalar variables whose address is not taken
  into temporary variables. *)

Open Scope error_monad_scope.
Open Scope string_scope.
Open Scope list_scope.

Parameter get_binder_list : assert -> list binder * assert.

Definition add_binder_list (s: statement) (c: assert) : statement :=
  match s with
  | Sskip => Sskip
  | _ =>
      let (binder_list, dummy_assert) := get_binder_list c in
      match binder_list with
      | nil => s
      | _ =>
        let s := Ssequence (Sdummyassert dummy_assert) s in
        fold_right Sgiven2 s binder_list
      end
  end.

(***************** Control flow analysis ***********************)

Fixpoint count_break (s: statement) : Z :=
  match s with
  | Sgiven2 _ s => count_break s
  | Sexgiven _ _ s => count_break s
  | Ssequence s1 s2 =>
      let cnt1 := count_break s1 in
      let cnt2 := count_break s2 in
      cnt1 + cnt2
  | Sifthenelse _ s1 s2 =>
      let cnt1 := count_break s1 in
      let cnt2 := count_break s2 in
      cnt1 + cnt2
  | Slabel _ s => count_break s
  | Sbreak => 1
  | _ => 0
  end.

Definition check_single_break (s: statement) : res unit :=
  let cnt :=  count_break s in
  if cnt <=? 1
    then OK tt
    else Error (MSG "Missing postcondition for a loop with multiple exits" :: nil).

(*
Fixpoint count_continue (s: statement) : Z :=
  match s with
  | Sgiven2 _ s => count_continue s
  | Ssequence s1 s2 =>
      let cnt1 := count_continue s1 in
      let cnt2 := count_continue s2 in
      cnt1 + cnt2
  | Sifthenelse _ s1 s2 =>
      let cnt1 := count_continue s1 in
      let cnt2 := count_continue s2 in
      cnt1 + cnt2
  | Slabel _ s => count_continue s
  | Sswitch _ ls => count_continue_labeled ls
  | Scontinue => 1
  | _ => 0
  end
with count_continue_labeled (ls: labeled_statements) : Z :=
  match ls with
  | LSnil => 0
  | LScons _ s ls =>
      let cnt1 := count_continue s in
      let cnt2 := count_continue_labeled ls in
      cnt1 + cnt2
  end.
*)

Fixpoint count_continue (s: ClightC.statement) : Z :=
  match s with
  | ClightC.Ssequence s1 s2 =>
      let cnt1 := count_continue s1 in
      let cnt2 := count_continue s2 in
      cnt1 + cnt2
  | ClightC.Sifthenelse _ s1 s2 =>
      let cnt1 := count_continue s1 in
      let cnt2 := count_continue s2 in
      cnt1 + cnt2
  | ClightC.Slabel _ s => count_continue s
  | ClightC.Sswitch _ ls => count_continue_labeled ls
  | ClightC.Scontinue => 1
  | _ => 0
  end
with count_continue_labeled (ls: ClightC.labeled_statements) : Z :=
  match ls with
  | ClightC.LSnil => 0
  | ClightC.LScons _ s ls =>
      let cnt1 := count_continue s in
      let cnt2 := count_continue_labeled ls in
      cnt1 + cnt2
  end.

(*
Definition check_no_continue (s: statement) : res unit :=
  let cnt :=  count_continue s in
  if cnt <=? 0
    then OK tt
    else Error (MSG "Double invariants needed for for loops with continue" :: nil).
*)

Fixpoint count_normal_exit (s: statement) : Z :=
  match s with
  | Sgiven2 _ s => count_normal_exit s
  | Sexgiven _ _ s => count_normal_exit s
  | Ssequence s1 s2 =>
      let cnt1 := count_normal_exit s1 in
      match s2 with
      | Sskip => cnt1
      | _ =>
        let cnt2 := count_normal_exit s2 in
        if (cnt1 <=? 0)
          then 0
          else cnt2
      end
  | Sifthenelse _ s1 s2 =>
      let cnt1 := count_normal_exit s1 in
      let cnt2 := count_normal_exit s2 in
      cnt1 + cnt2
  | Sswitch _ ls => 2 (* This is not true, but currently we only case about 0/1/>1. *)
  | Sloop2 _ s1 s2 =>
      count_break s1
  | Sloop s1 s2 =>
      count_break s1
  | Slabel _ s => count_normal_exit s
  | Scontinue | Sbreak | Sreturn _ => 0
  | _ => 1
  end.

Definition check_single_normal_exit (s: statement) : res unit :=
  let cnt := count_normal_exit s in
  if (cnt <=? 1)
    then OK tt
    else Error (MSG "Missing postcondition for if or/and loop statement" :: nil).

Fixpoint count_statement (s: statement) : nat :=
  match s with
  | Sskip => 0
  | Sassert _ => 0
  | Sdummyassert _ => 0
  | Sgiven2 _ s => count_statement s
  | Sexgiven _ _ s => count_statement s
  | Ssequence s1 s2 => count_statement s1 + count_statement s2
  | Slocal _ n _ _ => n
  | _ => 1
  end.

Fixpoint fold_cs_aux (cs_list: list (comment + statement)) (acc: statement) (stack: list (assert * statement)(*stack for localization*)) : res statement :=
  match cs_list with
  | nil =>
    match stack with
    | nil => OK acc
    | _ => Error (MSG "Unmatched Unlocal" :: nil)
    end
  | cs :: cs_list =>
    match cs with
    | inl (Inv, c) => Error (MSG "Dangling loop invariant" :: nil)
    | inl (Assert, c) =>
      (* match acc with
      | Sskip => fold_cs cs_list (Sassert c)
      | _ => *)
        fold_cs_aux cs_list (Ssequence (Sassert c) (add_binder_list acc c)) stack
      (* end *)
    | inl (Given, c) => Error (MSG "Manual Given comment is not allowed in this version" :: nil)
    | inl (Unlocal, c) => fold_cs_aux cs_list Sskip (cons (c, (add_binder_list acc c)) stack)
    | inl (Local, c) =>
      match stack with
      | nil => Error (MSG "Unmatched Local" :: nil)
      | cons (g, s1) stack =>
        fold_cs_aux cs_list (Ssequence
            (Slocal c (count_statement acc) (add_binder_list acc c) g) s1
        ) stack
      end
    | inl _ => Error (MSG "Funcsepc cannot appear in middle of a function" :: nil)
    | inr s =>
      match s, acc with
      | Sskip, _ => fold_cs_aux cs_list acc stack
      (* no longer use these special cases that annotation not ending with Sskip
         These special cases are for printing with Swhile, but we are no longer using Swhile
      | Sbreak, Sskip
      | Scontinue, Sskip
      | Sreturn _, Sskip
          => fold_cs cs_list s
      *)
      | _, Ssequence (Sassert _) _ (* If statement is followed by an assertion, use it as post condition. *)
      | _, Sskip (* or followed by skip *)
          => fold_cs_aux cs_list (Ssequence s acc) stack
      | Sloop _ _, _
      | Sloop2 _ _ _, _
      | Sifthenelse _ _ _, _ (* For other cases, statement must have at most one exit point. *)
          => (* do _ <- check_single_normal_exit s; *)
          fold_cs_aux cs_list (Ssequence s acc) stack
      | Sswitch _ _, _ =>
          Error (MSG "Missing postcondition for switch statement" :: nil)
      | _, _ => fold_cs_aux cs_list (Ssequence s acc) stack
      end
    (* | _ => Error (MSG "Unimplemented" :: nil) *)
    end
  end.

Fixpoint fold_cs (cs_list: list (comment + statement)) : res statement :=
  fold_cs_aux cs_list Sskip nil.

Fixpoint find_inv (cs_list: list (comment + statement)) : res (loop_invariant * list (comment + statement)) :=
  match cs_list with
  | inl (Inv, inv2) :: inl (Inv, inv1) :: cs_list =>
    OK ((LIDouble inv1 inv2), cs_list)
  | inl (Inv, inv) :: cs_list =>
    OK ((LISingle inv), cs_list)
  | cs :: cs_list =>
    do (inv, cs_list) <- find_inv cs_list;
    OK (inv, cs :: cs_list)
  | _ => Error (MSG "Missing loop invariant" :: nil)
  end.

Fixpoint annotate_stmt (s: ClightC.statement) : res statement :=
  let fix annotate_stmt_list (cs_list: list (comment + statement)) (s: ClightC.statement) : res (list (comment + statement)) :=
    let annotate_loop (inv: loop_invariant) (s1 s2: ClightC.statement) : res statement :=
      match inv with
      | LISingle inv =>
        let append_flag :=
          match s2 with
          | ClightC.Sskip => true
          | _ =>
            count_continue s1 <=? 0
          end
        in
        if append_flag then
          do cs_list1 <- annotate_stmt_list nil s1;
          do cs_list2 <- annotate_stmt_list cs_list1 s2;
          do s' <- fold_cs cs_list2;
          let s'' := add_binder_list s' inv in
          OK (Sloop2 (LISingle inv) s'' Sskip)
        else
          do cs_list1 <- annotate_stmt_list nil s1;
          do cs_list2 <- annotate_stmt_list nil s2;
          do s1' <- fold_cs cs_list1;
          let s1'' := add_binder_list s1' inv in
          do s2' <- fold_cs cs_list2;
          OK (Sloop2 (LISingle inv) s1'' s2')
      | LIDouble inv1 inv2 =>
        do s1' <- annotate_stmt s1;
        do s2' <- annotate_stmt s2;
        let s1'' := add_binder_list s1' inv1 in
        let s2'' := add_binder_list s2' inv2 in
        OK (Sloop2 (LIDouble inv1 inv2) s1'' s2'')
      end
    in
    match s with
    | ClightC.Slcomment c s =>
        annotate_stmt_list (inl c :: cs_list) s
    | ClightC.Srcomment s c =>
        do cs_list1 <- annotate_stmt_list cs_list s;
        OK (inl c :: cs_list1)
    | ClightC.Ssequence s1 s2 =>
        do cs_list1 <- annotate_stmt_list cs_list s1;
        do cs_list2 <- annotate_stmt_list cs_list1 s2;
        OK cs_list2
    | ClightC.Sloop s1 s2 =>
      do (inv, cs_list) <- find_inv cs_list;
      do s <- annotate_loop inv s1 s2;
      OK (inr s :: cs_list)
    | _ =>
      do s' <-
        match s with
        | ClightC.Sifthenelse a s1 s2 =>
            do s1' <- annotate_stmt s1;
            do s2' <- annotate_stmt s2;
            OK (Sifthenelse a s1' s2')
        | ClightC.Sswitch a ls =>
            do ls' <- annotate_lblstmt ls;
            OK (Sswitch a ls')
        | ClightC.Slabel lbl s =>
            do s' <- annotate_stmt s;
            OK (Slabel lbl s')
        | ClightC.Sskip => OK Sskip
        | ClightC.Sassign a1 a2 => OK (Sassign a1 a2)
        | ClightC.Sset id a => OK (Sset id a)
        | ClightC.Scall optid a al => OK (Scall optid a al)
        | ClightC.Sbuiltin optid ef tyargs al => OK (Sbuiltin optid ef tyargs al)
        | ClightC.Sbreak => OK Sbreak
        | ClightC.Scontinue => OK Scontinue
        | ClightC.Sreturn opta => OK (Sreturn opta)
        | ClightC.Sgoto lbl => OK (Sgoto lbl)
        | _ => Error (MSG "Internal error: invalid argument s in annotate_simple_stmt" :: nil)
        end;
      OK (inr s' :: cs_list)
    end
  in
  do cs_list <- annotate_stmt_list nil s;
  do s' <- fold_cs cs_list;
  OK s'

with annotate_lblstmt (ls: ClightC.labeled_statements) : res labeled_statements :=
  match ls with
  | ClightC.LSnil => OK LSnil
  | ClightC.LScons c s ls1 =>
      do s' <- annotate_stmt s;
      do ls1' <- annotate_lblstmt ls1;
      OK (LScons c s' ls1')
  end.

Definition add_funcspec (funcspec : binder * assert * assert) (s: statement)
      : option (binder * assert * assert) * statement :=
  match funcspec with (binder, pre, post) =>
    (Some funcspec,
      Sgiven2 binder (
        Ssequence (Sdummyassert pre) (
          Ssequence (Sdummyassert post)
            s)))
  end.

Definition annotate_body (s: ClightC.statement) : res (option (binder * assert * assert) * statement) :=
  match s with
  | ClightC.Slcomment (With, binder) (
      ClightC.Slcomment (Require, pre) (
        ClightC.Slcomment (Ensure, post) s)) =>
    do s' <- annotate_stmt s;
    OK (add_funcspec (binder, pre, post) s')
  | ClightC.Ssequence (
      ClightC.Slcomment (With, binder) (
        ClightC.Slcomment (Require, pre) (
          ClightC.Slcomment (Ensure, post) s1)))
      s2 =>
    do s' <- annotate_stmt (ClightC.Ssequence s1 s2);
    OK (add_funcspec (binder, pre, post) s')
  | _ =>
    (* do s' <- annotate_stmt s; *)
    (* Treat functions without funcspecs as not included in verification *)
    OK (None, Sskip)
  end.

Definition annotate_function (f: ClightC.function) : res function :=
  do (spec, body') <- annotate_body f.(ClightC.fn_body);
  OK {| fn_return := f.(ClightC.fn_return);
        fn_callconv := f.(ClightC.fn_callconv);
        fn_params := f.(ClightC.fn_params);
        fn_vars := f.(ClightC.fn_vars);
        fn_temps := f.(ClightC.fn_temps);
        fn_body := body';
        fn_spec := spec |}.

(** Whole-program transformation *)

Definition annotate_fundef (fd: ClightC.fundef) : res fundef :=
  match fd with
  | Internal f => do tf <- annotate_function f; OK (Internal tf)
  | External ef targs tres cconv => OK (External ef targs tres cconv)
  end.

Definition annotate_program (p: ClightC.program) : res program :=
  do p1 <- AST.transform_partial_program annotate_fundef p;
  OK {| prog_defs := AST.prog_defs p1;
        prog_public := AST.prog_public p1;
        prog_main := AST.prog_main p1;
        prog_types := prog_types p;
        prog_comp_env := prog_comp_env p;
        prog_comp_env_eq := prog_comp_env_eq p |}.
