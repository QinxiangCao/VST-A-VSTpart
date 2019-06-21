Require Import VST.floyd.proofauto.
Require Import append.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.
Definition t_struct_list := Tstruct _list noattr.

Fixpoint listrep (sh: share)
            (contents: list val) (x: val) : mpred :=
 match contents with
 | h::hs =>
              EX y:val,
                data_at sh t_struct_list (h,y) x * listrep sh hs y
 | nil => !! (x = nullval) && emp
 end.

Arguments listrep sh contents x : simpl never.

Lemma listrep_local_facts:
  forall sh contents p,
     listrep sh contents p |--
     !! (is_pointer_or_null p /\ (p=nullval <-> contents=nil)).
Proof.
intros.
revert p; induction contents; unfold listrep; fold listrep; intros; normalize.
apply prop_right; split; simpl; auto. intuition.
entailer!.
split; intro. subst p. destruct H; contradiction. inv H2.
Qed.

Hint Resolve listrep_local_facts : saturate_local.

Lemma listrep_valid_pointer:
  forall sh contents p,
   sepalg.nonidentity sh ->
   listrep sh contents p |-- valid_pointer p.
Proof.
 destruct contents; unfold listrep; fold listrep; intros; normalize.
 auto with valid_pointer.
 apply sepcon_valid_pointer1.
 apply data_at_valid_ptr; auto. simpl;  computable.
Qed.

Hint Resolve listrep_valid_pointer : valid_pointer.

Lemma listrep_null: forall sh contents,
    listrep sh contents nullval = !! (contents=nil) && emp.
Proof.
destruct contents; unfold listrep; fold listrep.
normalize.
apply pred_ext.
Intros y. entailer. destruct H; contradiction.
Intros.
Qed.

Lemma is_pointer_or_null_not_null:
 forall x, is_pointer_or_null x -> x <> nullval -> isptr x.
Proof.
intros.
 destruct x; try contradiction. hnf in H; subst i. contradiction H0; reflexivity.
 apply I.
Qed.

Definition spec111 :=
  (fun sh x y s1 s2 =>
    (PROP(writable_share sh)
     LOCAL (temp _x x; temp _y y)
     SEP (listrep sh s1 x; listrep sh s2 y),
     EX r: val,
       PROP()
       LOCAL(temp ret_temp r)
       SEP (listrep sh (s1++s2) r)
    )
  ).

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

Import Coq.Program.Tactics.

Ltac foo spec :=
  let spec_name := fresh "spec" in
  pose (spec_name := spec);
  unfold spec in spec_name;
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
  exact spec_name(*;
  lazymatch goal with
  | spec_name := fun x => (?pre, ?post) |- _ =>
    let pre_name := fresh "pre" in
    let post_name := fresh "post" in
    pose (pre_name := pre);
    pose (post_name := post);
    clear spec_name
  | _ => fail 0 "bbb"
  end*).

Definition spec222 :=
  ltac:(foo spec111).

Definition spec333 :=
  ltac:(let spec := eval cbv beta zeta delta [spec222] in spec222 in exact spec).


Definition append_spec :=
  ltac: (convert
 DECLARE _append
  WITH sh : share, x: val, y: val, s1: list val, s2: list val
  PRE [ _x OF (tptr t_struct_list) , _y OF (tptr t_struct_list)]
     PROP(writable_share sh)
     LOCAL (temp _x x; temp _y y)
     SEP (listrep sh s1 x; listrep sh s2 y)
  POST [ tptr t_struct_list ]
    EX r: val,
     PROP()
     LOCAL(temp ret_temp r)
     SEP (listrep sh (s1++s2) r).

Definition Gprog : funspecs :=   ltac:(with_library prog [ append_spec ]).
