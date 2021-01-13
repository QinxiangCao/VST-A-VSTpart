Require Import AClight.AClight.
Require Import VST.floyd.SeparationLogicAsLogic.
Import AuxDefs.

Notation "x ;; y" := (Ssequence x y)  (at level 65) : logic.
Definition path:= list (expr + statement) .
Definition path_statement := (assert * path * assert)%type.
Definition path_statements := list path_statement .
Definition partial_path_statement := (path * assert)%type.
Definition partial_path_statements := list partial_path_statement.
Definition atom_seq := (list path)%type.


Record basic_split_result:Type := Pack{
  pre   : partial_path_statements;
  paths : path_statements;
  normal_post  : partial_path_statements;
  continue_post: partial_path_statements;
  break_post   : partial_path_statements;
  return_post  : partial_path_statements;
  normal_atom  : list path;
  continue_atom: list path;
  break_atom   : list path;
  return_atom  : list path;
}.

(**
-----------------------------------------------------------------------------
  Combine two single unit as a new one , four situations 
-----------------------------------------------------------------------------
**)
Definition partial_conn_pp (x y :partial_path_statement) : path_statement :=
match x,y with
|(path1,pre) , (path2,post) => (pre,path1++path2,post)
end.

Definition partial_conn_ll (x y :path): path := 
match x,y with
| hd1::tl1, hd2::tl2 =>  x++y
| _,_ => nil
end.

Definition partial_conn_lp (x: path)(y :partial_path_statement) : partial_path_statement :=
match y with
|(path_y,post) => (x++path_y , post)
end.

Definition partial_conn_pl (x :partial_path_statement)(y: path) : partial_path_statement :=
match x with
|(path_x,pre) => (path_x++y , pre)
end.


(**
-----------------------------------------------------------------------------
  Combine two lists consisting of basic units above as a new one , four situations 
-----------------------------------------------------------------------------
**)
Definition partial_conv_pp (x y : partial_path_statements) : path_statements :=
concat (map (fun x1 => (map (fun y1 => partial_conn_pp x1 y1) y)) x ).

Definition partial_conv_ll (x y : atom_seq) : atom_seq :=
concat (map (fun x1 => (map (fun y1 => partial_conn_ll x1 y1) y)) x ).

Definition partial_conv_pl (x:partial_path_statements)(y:atom_seq) : partial_path_statements :=
concat (map (fun x1 => (map (fun y1 => partial_conn_pl x1 y1) y)) x ).

Definition partial_conv_lp (x:atom_seq)(y:partial_path_statements): partial_path_statements :=
concat (map (fun x1 => (map (fun y1 => partial_conn_lp x1 y1) y)) x ).


(**
-----------------------------------------------------------------------------
  Add the expr as a singleton 'path' to paths. Used in if branch.
    updated : also used in do-while loop.
  Two main situations : adding to a (path * assert) , or to a (path) 
    
-----------------------------------------------------------------------------
**)
Fixpoint partial_addpre_p (pres: partial_path_statements)(e:expr):partial_path_statements:=
match pres with
|(path,assert)::tl => ((inl e)::path , assert):: (partial_addpre_p tl e)
|_ => nil
end.

Fixpoint partial_addpre_l (l:atom_seq)(e:expr):atom_seq:=
match l with
|hd::tl => ((inl e)::hd)::(partial_addpre_l tl e)
|_ => nil
end.

Fixpoint partial_addpre_m (l:atom_seq)(e:expr):atom_seq:=
match l with
|hd::tl => (hd++[(inl e)])::(partial_addpre_l tl e)
|_ => nil
end.


(**
-----------------------------------------------------------------------------
  add an assertion to partial path statements , to make path statements,
  or add an assertion to atomic sequence to create a partial path statements
-----------------------------------------------------------------------------
**)
Fixpoint partial_addpre_a (pres: partial_path_statements)(a:assert):path_statements := 
match pres with 
|(path,assert)::tl => (a,path,assert)::(partial_addpre_a tl a)
|_ => nil
end.

Fixpoint partial_addpre_b (l:atom_seq)(a:assert):partial_path_statements:=
match l with
|hd::tl => (hd,a)::(partial_addpre_b tl a)
|_ => nil
end.

Fixpoint partial_addpre_c (pres: partial_path_statements)(a:assert):path_statements := 
match pres with 
|(path,assert)::tl => (assert,path,a)::(partial_addpre_a tl a)
|_ => nil
end.


Inductive split_result : Type :=
| Basic_Result:  basic_split_result -> split_result
| Forall_Result: forall A:Type, (A -> split_result) -> split_result
.

Definition FALSE := (PROP (False) LOCAL () SEP ()).

Inductive post_path_empty: split_result -> Prop :=
| Forall_empty_path:
    forall (A:Type) (stm: A -> split_result), 
    (forall a, post_path_empty (stm a))
    -> post_path_empty (Forall_Result A stm)
| Basic_empty_path res:
   let test_empty path := (fst path = nil) in 
    Forall test_empty (normal_post res)
    -> Forall test_empty (continue_post res)
    -> Forall test_empty (break_post res)
    -> Forall test_empty (return_post res)
    -> post_path_empty (Basic_Result res)
.


Inductive remove_post_paths_ex (A:Type) : partial_path_statements ->
  (A -> partial_path_statements) -> Prop :=
  | remove_post_paths_ex_nil:
      remove_post_paths_ex A nil (fun _ => nil)
  | remove_post_paths_ex_cons: forall post post_removed p asrt,
      remove_post_paths_ex A post post_removed ->
      remove_post_paths_ex A ((p, fun _ => (exp asrt))::post)
                             (fun a:A => (p, (fun _:environ => asrt a))::(post_removed a)).

Inductive remove_basic_post_ex (A:Type): basic_split_result 
    -> (A -> basic_split_result) -> Prop :=
  | remove_basic_post_ex_intro:
      forall res n_removed r_removed c_removed b_removed,
        remove_post_paths_ex A (normal_post res) n_removed ->
        remove_post_paths_ex A (return_post res) r_removed ->
        remove_post_paths_ex A (continue_post res) c_removed ->
        remove_post_paths_ex A (break_post res) b_removed ->
        remove_basic_post_ex A res ( fun a:A =>
          {|
            pre := pre res; 
            paths := paths res; 
            normal_post := n_removed a;
            continue_post := c_removed a;
            break_post := b_removed a;
            return_post := r_removed a;
            normal_atom := normal_atom res;
            break_atom := break_atom res;
            continue_atom := continue_atom res;
            return_atom := return_atom res;          
          |}
        ).

Inductive remove_post_ex (A:Type) : split_result -> (A -> split_result) -> Prop :=
  | remove_post_ex_cons: forall binded_res,
      (forall (a:A), remove_post_ex A (binded_res a) binded_res) ->
      remove_post_ex A (Forall_Result A binded_res) binded_res
  | remove_post_ex_basic: forall basic_res res_removed,
      remove_basic_post_ex A basic_res res_removed ->
      remove_post_ex A (Basic_Result basic_res) (fun a => Basic_Result (res_removed a)).

Inductive merge_seq : split_result -> split_result -> split_result -> Prop :=
| ex_given_merge: forall (A:Type) res1 res1_removed res2 inner_sum,
    post_path_empty res1 -> (*premise: assert must follow given *)
    remove_post_ex A res1 res1_removed ->  (* extract all the EX a, .. from res1 post *)
    (forall a:A, merge_seq (res1_removed a) (res2 a) (inner_sum a)) -> 
    (* next_level: unify the (a:A) in res1's post and res2's bind *)
    merge_seq res1 (Forall_Result A res2) (Forall_Result A inner_sum)
| merge_forall_right: forall (A:Type) res1 res2 res_sum,
    (forall a, merge_seq (Basic_Result res1) (res2 a) (res_sum a)) -> (* curry res2 until res2 becomes basic_result *)
    merge_seq (Basic_Result res1) (Forall_Result A res2) (Forall_Result A res_sum)
| merge_forall_left: forall (A:Type) res1 res2 res_sum,
    (forall a, merge_seq (res1 a) res2 (res_sum a)) ->
    merge_seq (Forall_Result A res1) res2 (Forall_Result A res_sum)
| merge_basic: forall s1 s2,
    merge_seq (Basic_Result s1) (Basic_Result s2)
      (Basic_Result {|
        pre := pre s1 ++ partial_conv_lp (normal_atom s1) (pre s2);
        paths := paths s1 ++ paths s2 ++ partial_conv_pp (normal_post s1) (pre s2);
        normal_post := normal_post s2 ++ partial_conv_pl (normal_post s1) (normal_atom s2);
        continue_post := continue_post s1 ++ continue_post s2
                          ++ partial_conv_pl (normal_post s1) (continue_atom s2);
        break_post := break_post s1 ++ break_post s2
                          ++ partial_conv_pl (normal_post s1) (break_atom s2);
        return_post := return_post s1 ++ return_post s2
                          ++ partial_conv_pl (normal_post s1) (return_atom s2);
        normal_atom := normal_atom s1 ++ normal_atom s2;
        return_atom := return_atom s1 ++ partial_conv_ll (normal_atom s1) (return_atom s2);
        break_atom := break_atom s1 ++ partial_conv_ll (normal_atom s1) (break_atom s2);
        continue_atom := continue_atom s1 ++ partial_conv_ll (normal_atom s1) (continue_atom s2);
      |}).


Inductive remove_assert_ex (A:Type) : assert ->
(* get exists out of assert *)
  (A -> assert) -> Prop :=
  | remove_assert_ex_O: forall asrt,
      remove_assert_ex A (fun _ => (exp asrt))
                              (fun a:A => (fun _:environ => asrt a)).

Inductive merge_loop_two : assert->split_result-> assert->split_result ->split_result-> Prop :=
(*
//INV1 
s1;
//INV2
s2;
*)

(*idea : because INV2 is an assert , NO ASSERT IS ALLOWED BEWTEEN EX and its GIVEN ,
          thus we only need to consider given in s1 following EX in INV1 and similar ones in 2's .
*)
| merge_l2_inv1 :forall (A:Type) res1 res2 inv1 inv2 inv1_removed res,
  remove_assert_ex A inv1 inv1_removed ->
  forall a:A, merge_loop_two (inv1_removed a) (res1 a) inv2 res2 (res a)->
  merge_loop_two inv1 (Forall_Result A res1) inv2 res2 (Forall_Result A res)
  
| merge_l2_inv2 :forall (A:Type) res1 res2 inv1 inv2 inv2_removed res,
  remove_assert_ex A inv2 inv2_removed ->
  forall a:A, merge_loop_two (inv1) (res1) (inv2_removed a) (res2 a) (res a)->
  merge_loop_two inv1 res1 inv2 (Forall_Result A res2) (Forall_Result A res)

| merge_forall_r2: forall (A:Type) inv1 inv2 res1 res2 res_sum,
    (forall a, merge_loop_two inv1 (Basic_Result res1) inv2 (res2 a) (res_sum a)) -> 
    merge_loop_two inv1 (Basic_Result res1) inv2 (Forall_Result A res2) (Forall_Result A res_sum)
| merge_forall_l2: forall (A:Type) inv1 inv2 res1 res2 res_sum,
    (forall a, merge_loop_two inv1 (res1 a) inv2  res2 (res_sum a)) ->
    merge_loop_two inv1 (Forall_Result A res1) inv2 res2 (Forall_Result A res_sum)

| merge_l2_basic :forall s1 s2 inv1 inv2,
  merge_loop_two inv1 (Basic_Result s1) inv2 (Basic_Result s2) 
  (Basic_Result {|
    pre :=[(nil,inv1)];
    paths := (
      (partial_addpre_a (pre s1) inv1) ++ (partial_addpre_a (partial_addpre_b (partial_conv_ll (normal_atom s1) (normal_atom s2)) inv2)inv1) ++ (partial_addpre_a (partial_addpre_b (partial_conv_ll (normal_atom s1) (continue_atom s2)) inv2)inv1) ++
        (partial_addpre_a (partial_addpre_b (partial_conv_ll (continue_atom s1) (normal_atom s2)) inv2)inv1) ++(partial_addpre_a (partial_addpre_b (partial_conv_ll (continue_atom s1) (continue_atom s2)) inv2)inv1) ++
      paths s1 ++ (partial_addpre_c (normal_post s1) inv2) ++ (partial_addpre_c (continue_post s1) inv2) ++ 
      (partial_addpre_a (pre s2) inv2) ++ (partial_addpre_a (partial_addpre_b (normal_atom s1) inv1)inv2) ++ (partial_addpre_a (partial_addpre_b (continue_atom s1) inv1)inv2) ++
        (partial_addpre_a (partial_addpre_b (normal_atom s1) inv1)inv2) ++(partial_addpre_a (partial_addpre_b (continue_atom s1) inv1)inv2) ++
      paths s2 ++ (partial_addpre_c (normal_post s2) inv2) ++(partial_addpre_c (continue_post s2) inv2)  );
    normal_post :=((break_post s1) ++ (break_post s2) ++ (partial_addpre_b (break_atom s1) inv1) ++ (partial_addpre_b (break_atom s2) inv2)) ;
    continue_post := nil ;
    return_post := ((return_post s1) ++ (return_post s2) ++ (partial_addpre_b (return_atom s1) inv1) ++ (partial_addpre_b (return_atom s2) inv2) );
    break_post := nil;
    normal_atom := ( break_atom s1 );
    continue_atom:= nil; 
    return_atom := ( return_atom s1 );
    break_atom := nil;
    |})
.    


Inductive merge_loop_one : assert -> split_result -> split_result -> split_result-> Prop :=
(*idea : s1 and s2 is a seq ,we also need to think about the (EX,GIVEN) pair in (INV1,s1). *)
| ex_given_merge_1: forall (A:Type) inv1 res1 res1_removed res2 inner_sum,
    post_path_empty res1 -> (*premise: assert must follow given *)
    remove_post_ex A res1 res1_removed ->  (* extract all the EX a, .. from res1 post *)
    forall a:A, merge_loop_one inv1 (res1_removed a) (res2 a) (inner_sum a) -> 
    (* next_level: unify the (a:A) in res1's post and res2's bind *)
    merge_loop_one inv1 res1 (Forall_Result A res2) (Forall_Result A inner_sum)

| merge_l1_inv1 :forall (A:Type) res1 res2 inv1 inv1_removed res,
  remove_assert_ex A inv1 inv1_removed ->
  forall a:A, merge_loop_one (inv1_removed a) (res1 a) res2 (res a)->
  merge_loop_one inv1 (Forall_Result A res1) res2 (Forall_Result A res)
  

| merge_forall_r1: forall (A:Type) inv1 res1 res2 res_sum,
    (forall a, merge_loop_one inv1 (Basic_Result res1) (res2 a) (res_sum a)) -> 
    merge_loop_one inv1 (Basic_Result res1) (Forall_Result A res2) (Forall_Result A res_sum)
| merge_forall_l1: forall (A:Type) inv1 inv2 res1 res2 res_sum,
    (forall a, merge_loop_one inv1 (res1 a) inv2 (res_sum a)) ->
    merge_loop_one inv1 (Forall_Result A res1) res2 (Forall_Result A res_sum)
| merge_l1_basic : forall s1 s2 inv,
    merge_loop_one inv (Basic_Result s1) (Basic_Result s2) 
    (Basic_Result {|
      pre:= [(nil,inv)] ;
      paths :=  ((partial_addpre_a (pre s1) inv) ++ 
      (partial_addpre_a (partial_conv_lp (normal_atom s1) (pre s2)) inv) ++ (partial_addpre_a (partial_conv_lp (continue_atom s1) (pre s2)) inv) ++
      (partial_addpre_a (partial_addpre_b (partial_conv_ll (normal_atom s1) (normal_atom s2)) inv)inv) ++ (partial_addpre_a (partial_addpre_b (partial_conv_ll (normal_atom s1) (continue_atom s2)) inv)inv) 
        ++(partial_addpre_a (partial_addpre_b (partial_conv_ll (continue_atom s1) (normal_atom s2)) inv)inv) ++(partial_addpre_a (partial_addpre_b (partial_conv_ll (continue_atom s1) (continue_atom s2)) inv)inv) ++
      (paths s1) ++
      (partial_conv_pp (normal_post s1) (pre s2)) ++ (partial_conv_pp (continue_post s1) (pre s2)) ++
      (partial_addpre_c (partial_conv_pl (normal_post s1) (normal_atom s2)) inv) ++(partial_addpre_c (partial_conv_pl (normal_post s1) (continue_atom s2)) inv) ++
        (partial_addpre_c (partial_conv_pl (continue_post s1) (normal_atom s2)) inv) ++(partial_addpre_c (partial_conv_pl (continue_post s1) (continue_atom s2)) inv) ++
      (paths s2) ++
      (partial_addpre_c (normal_post s2) inv) ++(partial_addpre_c (continue_post s2) inv) );
      normal_post :=
    (
      (break_post s1) ++ (break_post s2) ++ (partial_addpre_b (break_atom s1) inv) ++ 
    (partial_conv_pl (normal_post s1) (break_atom s2)) ++ ( partial_conv_pl (continue_post s1) (break_atom s2)) ++
    (partial_addpre_b (partial_conv_ll (normal_atom s1) (break_atom s2))inv) ++ (partial_addpre_b (partial_conv_ll (continue_atom s1) (break_atom s2))inv) 
    );
      continue_post := nil;
      return_post :=
    (
      (return_post s1) ++ (return_post s2) ++ (partial_addpre_b (return_atom s1) inv) ++ 
    (partial_conv_pl (normal_post s1) (return_atom s2)) ++ ( partial_conv_pl (continue_post s1) (return_atom s2)) ++
    (partial_addpre_b (partial_conv_ll (normal_atom s1) (return_atom s2))inv) ++ (partial_addpre_b (partial_conv_ll (continue_atom s1) (return_atom s2))inv) 
    );
      break_post := nil;
      normal_atom := ( (break_atom s1) ++ (partial_conv_ll (normal_atom s1) (break_atom s2)) ++ (partial_conv_ll (continue_atom s1) (break_atom s2)));
      continue_atom :=nil;
      return_atom := ( (return_atom s1) ++ (partial_conv_ll (normal_atom s1) (return_atom s2) ++ (partial_conv_ll (continue_atom s1) (return_atom s2)))) ;
      break_atom := nil; |}).

Inductive merge_loop_null : split_result -> split_result -> split_result-> Prop :=
| ex_given_merge_0: forall (A:Type) res1 res1_removed res2 inner_sum,
    post_path_empty res1 -> (*premise: assert must follow given *)
    remove_post_ex A res1 res1_removed ->  (* extract all the EX a, .. from res1 post *)
    forall a:A, merge_loop_null (res1_removed a) (res2 a) (inner_sum a) -> 
    (* next_level: unify the (a:A) in res1's post and res2's bind *)
    merge_loop_null res1 (Forall_Result A res2) (Forall_Result A inner_sum)

| merge_l0_basic : forall s1 s2,
  ( (normal_atom s1 = nil) /\ (continue_atom s1 = nil )/\ (break_atom s1 = nil) /\ (return_atom s1 = nil) )\/
  ((normal_atom s2 = nil )/\ (continue_atom s2 = nil) /\ (break_atom s2 = nil )/\ (return_atom s2 = nil)) ->
    merge_loop_null (Basic_Result s1) (Basic_Result s2)
    (Basic_Result {|
    pre :=((pre s1) ++ (partial_conv_lp (continue_atom s1) (pre s2)) ++ (partial_conv_lp (normal_atom s1) (pre s2)));
    paths :=( (paths s1) ++ 
      partial_conv_pp (normal_post s1) (pre s2) ++ partial_conv_pp (continue_post s1) (pre s2) ++
      (paths s2) ++ 
      partial_conv_pp (normal_post s2) (pre s1) ++ partial_conv_pp (continue_post s2) (pre s2) ++
      partial_addpre_c (continue_post s2) FALSE ++
      (partial_addpre_c (partial_conv_pl (normal_post s1) (continue_atom s2)) FALSE) ++ (partial_addpre_c (partial_conv_pl (continue_post s1) (continue_atom s2)) FALSE)
    );
    normal_post :=(partial_conv_pl (normal_post s1) (normal_atom s2) ++ partial_conv_pl (continue_post s1) (normal_atom s2) ++ (normal_post s2) ++
      (break_post s1) ++ (break_post s2) ++ (partial_conv_pl (normal_post s1) (break_atom s2)) ++ (partial_conv_pl (continue_post s1) (break_atom s2)));
    continue_post :=nil;
    return_post :=((return_post s1) ++ (return_post s2) ++ (partial_conv_pl (normal_post s1) (return_atom s2)) ++ (partial_conv_pl (continue_post s1) (return_atom s2) ));
    break_post:=nil;
    normal_atom:=nil;
    continue_atom:=nil;
    return_atom:=nil;
    break_atom:=nil;
    
    |})
.
      


Inductive basic_split : statement -> basic_split_result->Prop :=
| (* if a then c1 else c2 endif *)
  Split_if : forall a c1 pre1 paths1 n_post1 c_post1 r_post1 b_post1 n_atom1 c_atom1 r_atom1 b_atom1 
                     c2 pre2 paths2 n_post2 c_post2 r_post2 b_post2 n_atom2 c_atom2 r_atom2 b_atom2,
    basic_split c1 (Pack pre1 paths1 n_post1 c_post1 r_post1 b_post1 n_atom1 c_atom1 r_atom1 b_atom1)->
    basic_split c2 (Pack pre2 paths2 n_post2 c_post2 r_post2 b_post2 n_atom2 c_atom2 r_atom2 b_atom2)->
    basic_split (Sifthenelse a c1 c2) 
   (Pack
      (* pre = a * pre1 ++ (~a) * pre2 *)
      ((partial_addpre_p pre1 a) ++ (partial_addpre_p pre2 (VST.veric.semax_lemmas.Cnot a)))
      (* paths = paths1 ++ paths2 *)
      (paths1 ++ paths2)
      (* n_post = n_post1 ++ n_post2 *)
      (n_post1 ++ n_post2)
      (* c_post = c_post1 ++ c_post2 *)
      (c_post1 ++ c_post2)
      (* r_post = r_post1 ++ r_post2 *)
      (r_post1 ++ r_post2)
      (* b_post = b_post1 ++ b_post2 *)
      (b_post1 ++ b_post2)
      (* n_atom = a * n_atom1 ++ (~a) * n_atom2*) 
      ((partial_addpre_l n_atom1 a) ++ (partial_addpre_l n_atom2 (VST.veric.semax_lemmas.Cnot a)))
      (* c_atom = a * c_atom1 ++ (~a) * c_atom2*) 
      ((partial_addpre_l c_atom1 a) ++ (partial_addpre_l c_atom2 (VST.veric.semax_lemmas.Cnot a)))
      (* r_atom = a * r_atom1 ++ (~a) * r_atom2*) 
      ((partial_addpre_l r_atom1 a) ++ (partial_addpre_l r_atom2 (VST.veric.semax_lemmas.Cnot a)))
      (* b_atom = a * b_atom1 ++ (~a) * b_atom2*) 
      ((partial_addpre_l b_atom1 a) ++ (partial_addpre_l b_atom2 (VST.veric.semax_lemmas.Cnot a)))
   )

| (* It is equivalent to a singleton of path : [[inr (Sset ident exp) ]] *)
  Split_set : forall ident exp,
  basic_split ((Sset ident exp)) 
    (Pack nil nil nil nil nil nil [[inr (Sset ident exp) ]] nil nil nil )
        
| (* it is just a singleton too. Therefore only the normal_atom will be not empty *) 
  Split_assign : forall exp1 exp2,
  basic_split (Sassign exp1 exp2)
    (Pack nil nil nil nil nil nil [[inr (Sassign exp1 exp2)]] nil nil nil )

| (* pre and normal_post not empty*) 
  Split_assert : forall a,
  basic_split (Sassert a) 
  (Pack [(nil,a)] nil [(nil,a)] nil nil nil nil nil nil nil)

| Split_continue : 
  basic_split Scontinue (Pack nil nil nil nil nil nil nil [nil] nil nil)

| Split_break : 
  basic_split Sbreak (Pack nil nil nil nil nil nil nil nil [nil] nil)
(*Print option.*)
(*
| Split_return_Some : forall e,
  basic_split (Sreturn (Some e)) (Pack nil nil nil nil nil nil nil nil nil [[inl e]])    (* return value should not be here*)

| Split_return_None : 
  basic_split (Sreturn (None)) (Pack nil nil nil nil nil nil nil nil nil [nil])
*)
| Split_Sskip : 
  basic_split Sskip (Pack nil nil nil nil nil nil [nil] nil nil nil)
(* The C loops are derived forms. Here are the three forms in Clight from CompCert:
i.
Definition Swhile (e: expr) (s: statement) :=
  Sloop (Ssequence (Sifthenelse e Sskip Sbreak) s) Sskip.

ii.
Definition Sdowhile (s: statement) (e: expr) :=
  Sloop s (Sifthenelse e Sskip Sbreak).

iii.
Definition Sfor (s1: statement) (e2: expr) (s3: statement) (s4: statement) :=
  Ssequence s1 (Sloop (Ssequence (Sifthenelse e2 Sskip Sbreak) s3) s4).
*)
 
(* we do not allow Continue in incremental step (sure! how can incremental step have Continue?)
   thus if there is continue in incremental step , we will have to add an 'Assert False' in that list.
*)
(*and about return , void return is different from other returns. we need to both modify normal and return *)
  
  | (*function call regarded as atomic action , the same as assign and set.*)
  Split_func : forall ident e el,
  basic_split (Scall (ident) e el)
  (Pack nil nil nil nil nil nil [[inr (Scall (ident) e el)]] nil nil nil)
  .



Inductive path_split: statement -> split_result -> Prop :=
| (* Given A, c(A) *)
  split_given: forall (A: Type) 
    (substm: A -> statement) (subres: A -> split_result),
    (forall a:A, path_split (substm a) (subres a)) ->
    path_split (Sgiven A substm) (Forall_Result A subres)
| (* c1 ;; c2 *)
  split_seq: forall stm1 stm2 res1 res2 res,
    path_split stm1 res1 ->
    path_split stm2 res2 ->
    merge_seq res1 res2 res ->
    path_split (stm1;;stm2) res
| (* two invariants *)
  split_loop_two_given :forall inv1 inv2 s1 s2 res1 res2 res,
    path_split s1 res1->
    path_split s2 res2->
    merge_loop_two inv1 res1 inv2 res2 res ->
    path_split (Sloop (LIDouble inv1 inv2) s1 s2) res
| split_loop_one_given :forall inv1 s1 s2 res1 res2 res,
    path_split s1 res1->
    path_split s2 res2->
    merge_loop_one inv1 res1 res2 res->
    path_split (Sloop (LISingle inv1) s1 s2) res
| split_loop_null_given :forall s1 s2 res1 res2 res,
    path_split s1 res1->
    path_split s2 res2->
    merge_loop_null res1 res2 res->
    path_split (Sloop (LINull) s1 s2) res
| split_basic: forall stm basic_res,
    basic_split stm basic_res ->
    path_split stm (Basic_Result basic_res)
.
  


Inductive to_Clight : statement -> Clight.statement -> Prop :=
| to_Clight_assert: forall a,
    to_Clight (Sassert a) Clight.Sskip
| to_Clight_dummyassert: forall a,
    to_Clight (Sdummyassert a) Clight.Sskip
| to_Clight_given: forall (A:Type) stm c_stm,
    (forall a, to_Clight (stm a) c_stm) ->
    to_Clight (Sgiven A stm) c_stm
| to_Clight_local: forall a1 n a2 stm c_stm,
    to_Clight stm c_stm ->
    to_Clight (Slocal a1 n stm a2) c_stm
| to_Clight_skip:
    to_Clight Sskip Clight.Sskip
| to_Clight_assign: forall e1 e2,
    to_Clight (Sassign e1 e2) (Clight.Sassign e1 e2)
| to_Clight_set: forall id e,
    to_Clight (Sset id e) (Clight.Sset id e)
| to_Clight_builtin: forall id f tlis e,
    to_Clight (Sbuiltin id f tlis e) (Clight.Sbuiltin id f tlis e)
| to_Clight_call: forall id e elis,
    to_Clight (Scall id e elis) (Clight.Scall id e elis)
| to_Clight_sequence: forall stm1 c_stm1 stm2 c_stm2,
    to_Clight stm1 c_stm1 ->
    to_Clight stm2 c_stm2 ->
    to_Clight (Ssequence stm1 stm2) (Clight.Ssequence c_stm1 c_stm2)
| to_Clight_ifthenelse: forall e stm1 c_stm1 stm2 c_stm2,
    to_Clight stm1 c_stm1 ->
    to_Clight stm2 c_stm2 ->
    to_Clight (Sifthenelse e stm1 stm2) (Clight.Sifthenelse e c_stm1 c_stm2)
| to_Clight_loop: forall inv stm1 c_stm1 stm2 c_stm2,
    to_Clight stm1 c_stm1 ->
    to_Clight stm2 c_stm2 ->
    to_Clight (Sloop inv stm1 stm2) (Clight.Sloop c_stm1 c_stm2)
| to_Clight_break:
    to_Clight Sbreak Clight.Sbreak
| to_Clight_continue:
    to_Clight Scontinue Clight.Scontinue
| to_Clight_return: forall e,
    to_Clight (Sreturn e) (Clight.Sreturn e)
| to_Clight_switch: forall e ls c_ls,
    to_Clight_seq ls c_ls ->
    to_Clight (Sswitch e ls) (Clight.Sswitch e c_ls)
| to_Clight_label: forall id stm c_stm,
    to_Clight stm c_stm ->
    to_Clight (Slabel id stm) (Clight.Slabel id c_stm)
| to_Clight_goto: forall id,
    to_Clight (Sgoto id) (Clight.Sgoto id)

with to_Clight_seq : labeled_statements -> Clight.labeled_statements -> Prop :=
| to_Clight_seq_nil: to_Clight_seq LSnil Clight.LSnil
| to_Clight_seq_cons: 
    forall z stm c_stm seq c_seq,
      to_Clight stm c_stm ->
      to_Clight_seq seq c_seq ->
      to_Clight_seq (LScons z stm seq)
        (Clight.LScons z c_stm c_seq).


Section Soundness.

Context {CS: compspecs} {Espec: OracleKind} (Delta: tycontext).

Inductive path_to_statement : path -> Clight.statement -> Prop :=
| path_to_statement_nil:
    path_to_statement nil Clight.Sskip
| path_to_statement_expr: forall tl tl_stm expr,
    path_to_statement tl tl_stm ->
    path_to_statement ((inl expr)::tl) 
      (Clight.Ssequence (Clight.Sifthenelse expr Clight.Sskip Clight.Sbreak) tl_stm)
| path_to_statement_stm: forall tl tl_stm stm c_stm,
    path_to_statement tl tl_stm -> 
    to_Clight stm c_stm ->
    path_to_statement ((inr stm)::tl)
      (Clight.Ssequence c_stm tl_stm).


Inductive path_to_semax : path_statements -> Prop :=
| path_to_semax_nil:
    path_to_semax nil
| path_to_semax_cons: forall pre path post tl c_path,
    path_to_semax tl ->
    path_to_statement path c_path ->
    @semax CS Espec Delta pre c_path
    {| RA_normal := post;
       RA_break := FALSE;
       RA_continue := FALSE;
       RA_return := fun _ => FALSE|} ->
    path_to_semax ((pre,path,post)::tl).

Inductive partial_pre_to_semax (pre:assert): partial_path_statements -> Prop :=
| partial_pre_to_semax_nil:
    partial_pre_to_semax pre nil
| partial_pre_to_semax_cons: forall path post tl c_path,
    partial_pre_to_semax pre tl ->
    path_to_statement path c_path -> 
    @semax CS Espec Delta pre c_path
    {| RA_normal := post;
      RA_break := FALSE;
      RA_continue := FALSE;
      RA_return := fun _ => FALSE|} ->
    partial_pre_to_semax pre ((path,post)::tl).

Inductive partial_post_to_semax (post:assert):partial_path_statements -> Prop :=
| partial_post_to_semax_nil:
    partial_post_to_semax post nil
| partial_post_to_semax_cons: forall path pre tl c_path,
    partial_post_to_semax post tl ->
    path_to_statement path c_path ->
    @semax CS Espec Delta pre c_path
    {| RA_normal := post;
      RA_break := FALSE;
      RA_continue := FALSE;
      RA_return := fun _ => FALSE|} ->
    partial_post_to_semax post ((path,pre)::tl).

Inductive partial_return_to_semax (post: option val -> assert):
  partial_path_statements -> Prop :=
| partial_return_to_semax_nil:
    partial_return_to_semax post nil
| partial_return_to_semax_cons: forall path pre tl c_path,
  partial_return_to_semax post tl ->
  path_to_statement path c_path ->
  @semax CS Espec Delta pre c_path
  {| RA_normal := FALSE;
    RA_break := FALSE;
    RA_continue := FALSE;
    RA_return := post|} ->
  partial_return_to_semax post ((path,pre)::tl).

Inductive atom_to_semax (pre:assert) (post:assert) : atom_seq -> Prop :=
| atom_to_semax_nil:
    atom_to_semax pre post nil
| atom_to_semax_cons: forall path tl c_path,
    atom_to_semax pre post tl ->
    path_to_statement path c_path ->
    @semax CS Espec Delta pre c_path
    {| RA_normal := post;
      RA_break := FALSE;
      RA_continue := FALSE;
      RA_return := fun _ => FALSE|} ->
    atom_to_semax pre post (path::tl).

Inductive atom_return_to_semax (pre:assert) (post: option val -> assert) : atom_seq -> Prop :=
| atom_return_to_semax_nil:
    atom_return_to_semax pre post nil
| atom_return_to_semax_cons: forall path tl c_path,
    atom_return_to_semax pre post tl ->
    path_to_statement path c_path ->
    @semax CS Espec Delta pre c_path
    {| RA_normal := FALSE;
      RA_break := FALSE;
      RA_continue := FALSE;
      RA_return := post|} ->
    atom_return_to_semax pre post (path::tl).

Inductive split_Semax (P:assert) 
(Q:ret_assert): split_result -> Prop :=
| Forall_Semax: forall A subres,
    (forall a, split_Semax P Q (subres a)) ->
    split_Semax P Q (Forall_Result A subres) 
| Basic_Semax: forall pre paths n_post c_post r_post b_post n_atom c_atom r_atom b_atom,
    partial_pre_to_semax P pre ->
    path_to_semax paths ->
    partial_post_to_semax (RA_normal Q) n_post ->
    partial_post_to_semax (RA_break Q) b_post ->
    partial_post_to_semax (RA_continue Q) c_post ->
    partial_return_to_semax (RA_return Q) r_post ->
    atom_to_semax P (RA_normal Q) n_atom ->
    atom_to_semax P (RA_break Q) b_atom ->
    atom_to_semax P (RA_continue Q) c_atom ->
    atom_return_to_semax P (RA_return Q) r_atom ->
    split_Semax P Q  (Basic_Result 
          (Pack pre paths n_post c_post r_post b_post n_atom c_atom r_atom b_atom)).



Lemma path_split_forall_inv: forall stm res,
path_split stm res ->
  match res with
  | Basic_Result _ => True
  | Forall_Result A res =>
    exists stm', forall a, path_split (stm' a) (res a)
  end.
Proof.
  intros.
  induction H.
  + exists substm. apply H.
  + clear H. clear H0. clear stm1 stm2. 
    induction H1;auto.
    - admit.
    - destruct IHpath_split2.

  
Admitted.

Theorem soundness: forall 
  (P:assert) (Q:ret_assert) (stm: statement) (c_stm: Clight.statement)
  (s: split_result),
  path_split stm s ->
  split_Semax P Q s ->
  to_Clight stm c_stm ->
  @semax CS Espec Delta P c_stm Q.
Proof. (* intros.
  generalize dependent stm. revert c_stm.
  induction H0.
  - intros.
    eapply H0.
  
  eapply H1.
    induction H.

*)

  intros. generalize dependent c_stm.
  generalize dependent P. revert Q.
  induction H;intros.
  + inversion H2.
  Print ClassicalFacts.prop_extensionality.
  Check Classical_Prop.EqdepTheory.inj_pair2. Locate inj_pair2. apply inj_pair2 in H5. subst.
    eapply H0.
    { inv H1. apply inj_pair2 in H5. subst. auto. }
    { apply H6. }
  + inv H3.
    induction H1.
    {
      admit.
    }
    {
      eapply H3.
      + apply H.
      + 
      inv H0.


     }


  intros. 
Admitted.