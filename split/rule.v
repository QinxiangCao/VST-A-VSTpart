Require Import AClight.AClight.
Require Import VST.floyd.proofauto.
Require Import Split.vst_ext.
Require Import Split.defs.
Require Import VST.veric.semax_lemmas.

Inductive binded_split_result: Type :=
| Basic_split : split_result -> binded_split_result
| Binded_split(X: Type) (x: X): (X -> split_result) -> binded_split_result
.

Definition flatten_partial (X:Type) (x:X) (stm: X -> partial_assert) : partial_assert
 := Binded_partial X (inhabits x) stm.

Definition flatten_partials (X:Type) (x:X) (stm: list (X -> partial_assert)) : list partial_assert
:= List.map (flatten_partial X x) stm.


Fixpoint flatten_partials (X:Type) (stms:partial_path_statements): 
  option (list ((X -> partial_assert) * path)) :=
  match stms with
  | nil => Some nil
  | stm :: stms' =>
      match stm with (ass, path) =>
      match ass with 
      | Binded_partial X HX ass' => 
          match flatten_partials X stms' with
          | Some res => Some ((ass', path):: res)
          | None => None
          end
      | _ => None
      end
      end
  end.

Fixpoint split_pre_of (stm: Split.statement) : option partial_path_statements :=
  match stm with
  | Split.Ssequence s1 s2 =>
      let res1 := split_pre_of s1 in
      let res2 := split_pre_of s2 in
      match res1, res2 with
      | Some res1, Some res2 =>
          (* if orb (all_basic (pre res2)) (* __ ;; basic *)
            ((* basic ;; bind*)
              (all_basic(normal_post res1)) &&
              (all_empty_path (normal_post res1)) &&
              (all_empty_atom (normal_atom res1))
            ) then *)
          Some ( res1 ) 
           (* else None *)
        | _, _ => None
      end
  | Split.Sgiven X x a_s =>
      Binded_assert 
  | _ => None
  end.



  | Split.Sifthenelse a s1 s2 => 
      let res1 := path_split s1 in
      let res2 := path_split s2 in
      match res1, res2 with
      | Some res1, Some res2 =>
          Some {|
            pre := add_exp_to_pres a (pre res1) ++ add_exp_to_pres (Cnot a) (pre res2);
            paths := paths res1 ++ paths res2;
            normal_post := normal_post res1 ++ normal_post res2;
            continue_post := continue_post res1 ++ continue_post res2;
            return_post := return_post res1 ++ return_post res2;
            break_post := break_post res1 ++ break_post res2;
            normal_atom := add_exp_to_atoms a (normal_atom res1) 
                          ++ add_exp_to_atoms (Cnot a) (normal_atom res2);
            break_atom := add_exp_to_atoms a (break_atom res1) 
                          ++ add_exp_to_atoms (Cnot a) (break_atom res2);
            return_atom := add_exp_to_return_atoms a (return_atom res1) 
                          ++ add_exp_to_return_atoms (Cnot a) (return_atom res2);
            continue_atom := add_exp_to_atoms a (continue_atom res1) 
                          ++ add_exp_to_atoms (Cnot a) (continue_atom res2);
          |}
      | _, _ => None
      end
  (* | Sloop _ s1 s2 => Clight.Sloop (Split_to_Clight s1) (Split_to_Clight s2) *)
  | Split.Sgiven A a a_s =>
    let HA := inhabits a in
    let (P, stm) := a_s a in
    let res := path_split stm in
      match res with
      | Some res => Some {|
          pre := nil;
          paths := List.map (fun path => Binded_assert A HA (fun a => 
            match (path_split snd (a_s a)) with
            | Some res => paths res
            | None => FALSE, nil) ;
          normal_post := nil;
          continue_post := nil;
          return_post := nil;
          break_post := nil;
          normal_atom := nil;
          break_atom := nil;
          return_atom := nil;
          continue_atom := nil;
      |}
      | None => None
      end
  | Split.Sassert a =>
      Some (Pack [(Basic_partial a, nil)] nil 
            [(Basic_partial a, nil)] nil nil nil nil nil nil nil)
  | Split.Sassign exp1 exp2 =>
      Some (Pack nil nil nil nil nil nil [[inr (Sassign exp1 exp2)]] nil nil nil )
  | Split.Sset ident exp => 
      Some (Pack nil nil nil nil nil nil [[inr (Sset ident exp) ]] nil nil nil )
  | Split.Scall ident e el =>
      Some (Pack nil nil nil nil nil nil [[inr (Scall (ident) e el)]] nil nil nil)
  | Split.Sbreak => Some (Pack nil nil nil nil nil nil nil nil [nil] nil)
  | Split.Scontinue => Some (Pack nil nil nil nil nil nil nil [nil] nil nil)
  | Split.Sreturn r => Some (Pack nil nil nil nil nil nil nil nil nil [(nil,r)])
  | Split.Sskip => Some (Pack nil nil nil nil nil nil [nil] nil nil nil)
  | _ => None
  end.


Inductive bind_partial_add (X:Type) (HX: Non_empty_Type X ):
partial_path_statements -> (X -> partial_path_statements) -> Prop :=
| bind_partial_nil: bind_partial_add X HX nil (fun _ => nil)
| bind_partial_cons: forall p1 tl1 tl2 a,
  bind_partial_add X HX tl1 tl2 ->
  bind_partial_add X HX ((Binded_partial X HX a, p1)::tl1)
                   (fun x:X => ((a x, p1)::(tl2 x)))
.

Inductive bind_return_add (X:Type) (HX: Non_empty_Type X ):
return_post_statements -> (X -> return_post_statements) -> Prop :=
| bind_return_nil: bind_return_add X HX nil (fun _ => nil)
| bind_return_cons: forall p1 tl1 tl2 a v,
  bind_return_add X HX tl1 tl2 ->
  bind_return_add X HX ((Binded_partial X HX a, p1, v)::tl1)
                  (fun x:X => ((a x, p1, v)::(tl2 x)))
.

Inductive bind_path_add (X:Type) (HX: Non_empty_Type X ):
path_statements -> (X -> path_statements) -> Prop :=
| bind_path_nil: bind_path_add X HX nil (fun _ => nil)
| bind_path_cons: forall p1 tl1 tl2 a,
  bind_path_add X HX tl1 tl2 ->
  bind_path_add X HX ((Binded_assert X HX a, p1)::tl1)
                  (fun x:X => ((a x, p1)::(tl2 x)))
.

(* 
Inductive bind_result_add (A:Type) (HA: Non_empty_Type A ):
  split_result -> (A -> split_result) -> Prop := 
| bind_result_add_intro: forall pre paths normal_post break_post 
    continue_post return_post normal_atom break_atom continue_atom
    return_atom pre' paths' normal_post' break_post'
    continue_post' return_post',
    bind_partial_add A HA pre pre' ->
    bind_partial_add A HA normal_post normal_post' ->
    bind_partial_add A HA break_post break_post' ->
    bind_partial_add A HA continue_post continue_post' ->
    bind_return_add A HA return_post return_post' ->
    bind_path_add A HA paths paths' ->
    bind_result_add A HA (Pack pre paths normal_post break_post continue_post
                            return_post normal_atom break_atom continue_atom
                            return_atom)
                      (fun a:A => Pack (pre' a) (paths' a) (normal_post' a) (break_post' a) (continue_post' a) (return_post' a) normal_atom break_atom continue_atom
                      return_atom)
. *)

Fixpoint path_split (stm: Split.statement) : option split_result :=
  match stm with
  | Split.Ssequence s1 s2 =>
      let res1 := path_split s1 in
      let res2 := path_split s2 in
      match res1, res2 with
      | Some res1, Some res2 =>
          if orb (all_basic (pre res2)) (* __ ;; basic *)
            ((* basic ;; bind*)
              (all_basic(normal_post res1)) &&
              (all_empty_path (normal_post res1)) &&
              (all_empty_atom (normal_atom res1))
            ) then
          Some ({|
          pre := pre res1 ++ atoms_conn_pres (normal_atom res1) (pre res2);
          paths := paths res1 ++ paths res2 ++ posts_conn_pres (normal_post res1) (pre res2);
          normal_post := normal_post res2 ++ posts_conn_atoms (normal_post res1) (normal_atom res2);
          continue_post := continue_post res1 ++ continue_post res2
                            ++ posts_conn_atoms (normal_post res1) (continue_atom res2);
          break_post := break_post res1 ++ break_post res2
                            ++ posts_conn_atoms (normal_post res1) (break_atom res2);
          return_post := return_post res1 ++ return_post res2
                            ++ posts_conn_returns (normal_post res1) (return_atom res2);
          normal_atom := atoms_conn_atoms (normal_atom res1) (normal_atom res2);
          return_atom := return_atom res1 ++ atoms_conn_returns (normal_atom res1) (return_atom res2);
          break_atom := break_atom res1 ++ atoms_conn_atoms (normal_atom res1) (break_atom res2);
          continue_atom := continue_atom res1 ++ atoms_conn_atoms (normal_atom res1) (continue_atom res2);
          |}) else None
        | _, _ => None
      end
  | Split.Sifthenelse a s1 s2 => 
      let res1 := path_split s1 in
      let res2 := path_split s2 in
      match res1, res2 with
      | Some res1, Some res2 =>
          Some {|
            pre := add_exp_to_pres a (pre res1) ++ add_exp_to_pres (Cnot a) (pre res2);
            paths := paths res1 ++ paths res2;
            normal_post := normal_post res1 ++ normal_post res2;
            continue_post := continue_post res1 ++ continue_post res2;
            return_post := return_post res1 ++ return_post res2;
            break_post := break_post res1 ++ break_post res2;
            normal_atom := add_exp_to_atoms a (normal_atom res1) 
                          ++ add_exp_to_atoms (Cnot a) (normal_atom res2);
            break_atom := add_exp_to_atoms a (break_atom res1) 
                          ++ add_exp_to_atoms (Cnot a) (break_atom res2);
            return_atom := add_exp_to_return_atoms a (return_atom res1) 
                          ++ add_exp_to_return_atoms (Cnot a) (return_atom res2);
            continue_atom := add_exp_to_atoms a (continue_atom res1) 
                          ++ add_exp_to_atoms (Cnot a) (continue_atom res2);
          |}
      | _, _ => None
      end
  (* | Sloop _ s1 s2 => Clight.Sloop (Split_to_Clight s1) (Split_to_Clight s2) *)
  | Split.Sgiven A a a_s =>
    let HA := inhabits a in
    let (P, stm) := a_s a in
    let res := path_split stm in
      match res with
      | Some res => Some {|
          pre := nil;
          paths := List.map (fun path => Binded_assert A HA (fun a => 
            match (path_split snd (a_s a)) with
            | Some res => paths res
            | None => FALSE, nil) ;
          normal_post := nil;
          continue_post := nil;
          return_post := nil;
          break_post := nil;
          normal_atom := nil;
          break_atom := nil;
          return_atom := nil;
          continue_atom := nil;
      |}
      | None => None
      end
  | Split.Sassert a =>
      Some (Pack [(Basic_partial a, nil)] nil 
            [(Basic_partial a, nil)] nil nil nil nil nil nil nil)
  | Split.Sassign exp1 exp2 =>
      Some (Pack nil nil nil nil nil nil [[inr (Sassign exp1 exp2)]] nil nil nil )
  | Split.Sset ident exp => 
      Some (Pack nil nil nil nil nil nil [[inr (Sset ident exp) ]] nil nil nil )
  | Split.Scall ident e el =>
      Some (Pack nil nil nil nil nil nil [[inr (Scall (ident) e el)]] nil nil nil)
  | Split.Sbreak => Some (Pack nil nil nil nil nil nil nil nil [nil] nil)
  | Split.Scontinue => Some (Pack nil nil nil nil nil nil nil [nil] nil nil)
  | Split.Sreturn r => Some (Pack nil nil nil nil nil nil nil nil nil [(nil,r)])
  | Split.Sskip => Some (Pack nil nil nil nil nil nil [nil] nil nil nil)
  | _ => None
  end.


Inductive path_split: Split.statement -> split_result -> Prop :=
| (* Given A, c(A) *)
  split_given: forall (X: Type)(HX:Non_empty_Type X)
    (stm': X -> statement) res' res,  
    bind_result_add X HX res res' -> 
    (forall x:X, path_split (stm' x) (res' x)) ->
    path_split (Sgiven X stm') res
| (* c1 ;; c2 *)
  split_seq: forall stm1 stm2 res1 res2,
    path_split stm1 res1 ->
    path_split stm2 res2 ->
    ((all_basic (pre res2) = true) (* __ ;; basic *)  \/
    ((* basic ;; bind*)
      (all_basic(normal_post res1) = true) /\
      (all_empty_path (normal_post res1)=true) /\
      (all_empty_atom (normal_atom res1)=true)
    )) ->
    path_split (stm1;;stm2)
      ({|
        pre := pre res1 ++ atoms_conn_pres (normal_atom res1) (pre res2);
        paths := paths res1 ++ paths res2 ++ posts_conn_pres (normal_post res1) (pre res2);
        normal_post := normal_post res2 ++ posts_conn_atoms (normal_post res1) (normal_atom res2);
        continue_post := continue_post res1 ++ continue_post res2
                          ++ posts_conn_atoms (normal_post res1) (continue_atom res2);
        break_post := break_post res1 ++ break_post res2
                          ++ posts_conn_atoms (normal_post res1) (break_atom res2);
        return_post := return_post res1 ++ return_post res2
                          ++ posts_conn_returns (normal_post res1) (return_atom res2);
        normal_atom := atoms_conn_atoms (normal_atom res1) (normal_atom res2);
        return_atom := return_atom res1 ++ atoms_conn_returns (normal_atom res1) (return_atom res2);
        break_atom := break_atom res1 ++ atoms_conn_atoms (normal_atom res1) (break_atom res2);
        continue_atom := continue_atom res1 ++ atoms_conn_atoms (normal_atom res1) (continue_atom res2);
        |})
| split_base: forall stm res,
    basic_split stm res ->
    path_split stm res
| split_if:
   forall a stm1 stm2 res1 res2,
    path_split stm1 res1 ->
    path_split stm2 res2 ->
    path_split (Sifthenelse a stm1 stm2)
    {|
      pre := add_exp_to_pres a (pre res1) ++ add_exp_to_pres (Cnot a) (pre res2);
      paths := paths res1 ++ paths res2;
      normal_post := normal_post res1 ++ normal_post res2;
      continue_post := continue_post res1 ++ continue_post res2;
      return_post := return_post res1 ++ return_post res2;
      break_post := break_post res1 ++ break_post res2;
      normal_atom := add_exp_to_atoms a (normal_atom res1) 
                    ++ add_exp_to_atoms (Cnot a) (normal_atom res2);
      break_atom := add_exp_to_atoms a (break_atom res1) 
                    ++ add_exp_to_atoms (Cnot a) (break_atom res2);
      return_atom := add_exp_to_return_atoms a (return_atom res1) 
                    ++ add_exp_to_return_atoms (Cnot a) (return_atom res2);
      continue_atom := add_exp_to_atoms a (continue_atom res1) 
                    ++ add_exp_to_atoms (Cnot a) (continue_atom res2);
    |}
| Split_loop_double: forall inv1 inv2 c1 c2 res1 res2 
  (Econt_atom: continue_atom res2 = [])
  (Econt_post: continue_post res2 = [])
  (* (Ebasic_normal1: all_basic (normal_post res1)= true)
  (Ebasic_continue1: all_basic (continue_post res1)= true)
  (Ebasic_pre2: all_basic (pre res2)= true) *) ,
    path_split c1 res1 ->
    path_split c2 res2 ->
    path_split (Sloop (LIDouble inv1 inv2) c1 c2) {|
      pre := [(Basic_partial inv1,nil)];
      paths := 
        posts_conn_pres [(Basic_partial inv1, nil)] (pre res1) ++
        posts_conn_pres [(Basic_partial inv1, nil)]
          (atoms_conn_pres (normal_atom res1) [(Basic_partial inv2, nil)]) ++
        posts_conn_pres [(Basic_partial inv1, nil)]
          (atoms_conn_pres (continue_atom res1) [(Basic_partial inv2, nil)]) ++
        posts_conn_pres (normal_post res1) [(Basic_partial inv2, nil)] ++
        posts_conn_pres (continue_post res1) [(Basic_partial inv2, nil)] ++
        posts_conn_pres [(Basic_partial inv2, nil)] (pre res2) ++
        posts_conn_pres [(Basic_partial inv2, nil)]
          (atoms_conn_pres (normal_atom res2) [(Basic_partial inv1, nil)]) ++
        posts_conn_pres (normal_post res2) [(Basic_partial inv1, nil)] ++
        posts_conn_pres (continue_post res2) [(Basic_partial inv1, nil)]++
        paths res1 ++ paths res2;
      normal_post :=
        break_post res1 ++ break_post res2 ++
        posts_conn_atoms [(Basic_partial inv1, nil)] (break_atom res1) ++
        posts_conn_atoms [(Basic_partial inv2, nil)] (break_atom res2);
      continue_post := nil;
      break_post := nil;
      return_post :=
        (return_post res1) ++ (return_post res2) ++
        posts_conn_returns [(Basic_partial inv1, nil)] (return_atom res1) ++
        posts_conn_returns [(Basic_partial inv2, nil)] (return_atom res2) ;
      normal_atom := nil;
      break_atom := nil;
      continue_atom := nil;
      return_atom := nil
          (* no continue condition in c2 *)
    |}
(* | split_loop_single_skip: forall inv c1 c1' c2 c2' res,
    AClight_to_Clight c1 c1' ->
    AClight_to_Clight c2 c2' ->
    nocontinue c2' = true ->
    nocontinue c1' = true \/ c2 = AClight.Sskip ->
    path_split (Sloop (LIDouble inv inv) (c1;;c2) AClight.Sskip) res ->
    path_split (Sloop (LISingle inv) c1 c2) res
     *)
| Split_loop_single: forall inv c1 c2 res1 res2 
  (Econt_atom: continue_atom res2 = [])
  (Econt_post: continue_post res2 = [])
  (Ebasic_pre: all_basic (pre res2) = true),
    path_split c1 res1 ->
    path_split c2 res2 ->
    path_split (Sloop (LISingle inv) c1 c2) {|
      pre := [(Basic_partial inv,nil)];
      paths := 
        posts_conn_pres [(Basic_partial inv, nil)] (pre res1) ++
        posts_conn_pres [(Basic_partial inv, nil)]
          (atoms_conn_pres (normal_atom res1) (pre res2)) ++
        posts_conn_pres [(Basic_partial inv, nil)]
          (atoms_conn_pres (normal_atom res1)
            (atoms_conn_pres (normal_atom res2)
              [(Basic_partial inv, nil)])) ++
        posts_conn_pres [(Basic_partial inv, nil)]
          (atoms_conn_pres (continue_atom res1)
              (atoms_conn_pres (normal_atom res2)
                [(Basic_partial inv, nil)])) ++
        posts_conn_pres [(Basic_partial inv, nil)]
          (atoms_conn_pres (continue_atom res1) (pre res2)) ++
        paths res1 ++ paths res2 ++
        posts_conn_pres (normal_post res1) (pre res2) ++
        posts_conn_pres (normal_post res1)
            (atoms_conn_pres (normal_atom res2) 
              [(Basic_partial inv, [])]) ++
        posts_conn_pres (continue_post res1) (pre res2) ++
        posts_conn_pres (continue_post res1)
            (atoms_conn_pres (normal_atom res2) 
              [(Basic_partial inv, [])]) ++
          posts_conn_pres (normal_post res2) [(Basic_partial inv, nil)];
      normal_post :=
        break_post res1 ++ break_post res2 ++
        posts_conn_atoms [(Basic_partial inv, nil)] (break_atom res1) ++
        posts_conn_atoms [(Basic_partial inv, nil)]
          (atoms_conn_atoms (normal_atom res1) (break_atom res2)) ++
        posts_conn_atoms [(Basic_partial inv, nil)]
          (atoms_conn_atoms (continue_atom res1) (break_atom res2)) ++
        posts_conn_atoms (normal_post res1) (break_atom res2) ++
        posts_conn_atoms (continue_post res1) (break_atom res2);
      continue_post := nil;
      break_post := nil;
      return_post :=
        (return_post res1) ++ (return_post res2) ++
        posts_conn_returns [(Basic_partial inv, nil)] (return_atom res1) ++
        posts_conn_returns [(Basic_partial inv, nil)]
          (atoms_conn_returns (normal_atom res1) (return_atom res2)) ++
        posts_conn_returns [(Basic_partial inv, nil)]
          (atoms_conn_returns (continue_atom res1) (return_atom res2)) ++
        posts_conn_returns (normal_post res1) (return_atom res2) ++
        posts_conn_returns (continue_post res1) (return_atom res2) ;
      normal_atom := nil;
      break_atom := nil;
      continue_atom := nil;
      return_atom := nil
          (* no continue condition in c2 *)
    |}

 | Split_loop_null: forall stm1 stm2 res1 res2
  (Econt_atom: continue_atom res2 = [])
  (Econt_post: continue_post res2 = [])
  (Ebasic_pre1: all_basic (pre res1) = true)
  (Ebasic_pre2: all_basic (pre res2) = true)
  (Ebasic_post1:all_basic (normal_post res1) = true)
  (Ebasic_post2:all_basic (normal_post res2) = true)
  (Ebasic_post3:all_basic (continue_post res1) = true)
  ,
  ((normal_atom res1 = []/\continue_atom res1 = []) \/ normal_atom res2 = [])->
  (pre res1 <> []) -> (pre res2 <> [])->
    path_split stm1 res1 ->
    path_split stm2 res2 ->
    path_split (Sloop (LINull) stm1 stm2)
      ({|
        pre := pre res1 ++ atoms_conn_pres (normal_atom res1) (pre res2) ++ atoms_conn_pres (continue_atom res1) (pre res2) 
        ;
        paths := (* path1 ++ path2 ++ nc_post1 * pre2 ++ nc_post1 *n_atom2 * pre1 ++ n_post2 * pre1 ++ n_post2 * nc_atom1 * pre2 *) 
                paths res1 ++ paths res2 ++ posts_conn_pres (normal_post res1) (pre res2) ++ posts_conn_pres (continue_post res1) (pre res2)
                ++ posts_conn_pres (normal_post res2) (pre res1) 
                ++ (posts_conn_pres (posts_conn_atoms (normal_post res1) (normal_atom res2)) (pre res1))
                ++ (posts_conn_pres (posts_conn_atoms (continue_post res1) (normal_atom res2)) (pre res1))
                ++ (posts_conn_pres (posts_conn_atoms (normal_post res2) (normal_atom res1)) (pre res2))
                ++ (posts_conn_pres (posts_conn_atoms (normal_post res2) (continue_atom res1)) (pre res2))
                ;
        normal_post := (break_post res1) ++ (break_post res2) 
                        ++ (posts_conn_atoms (normal_post res1) (break_atom res2)) 
                        ++ (posts_conn_atoms (normal_post res2) (break_atom res1))
                        ++ (posts_conn_atoms (continue_post res1) (break_atom res2)) 
                        ++ (posts_conn_atoms (normal_post res2) (atoms_conn_atoms (normal_atom res1) (break_atom res2)))
                        ++ (posts_conn_atoms (normal_post res2) (atoms_conn_atoms (continue_atom res1) (break_atom res2)))
                        ++ (posts_conn_atoms (normal_post res1) (atoms_conn_atoms (normal_atom res2) (break_atom res1)))
                        ++ (posts_conn_atoms (continue_post res1) (atoms_conn_atoms (normal_atom res2) (break_atom res1)))
                        ;
        continue_post := nil;
        break_post := nil;
        return_post := (return_post res1) ++ (return_post res2)
                        ++ posts_conn_returns(normal_post res1)(return_atom res2) 
                        ++ posts_conn_returns(continue_post res1)(return_atom res2)
                        ++ posts_conn_returns(normal_post res2)(return_atom res1)
                        ++ (posts_conn_returns (normal_post res2) (atoms_conn_returns (normal_atom res1) (return_atom res2)))
                        ++ (posts_conn_returns (normal_post res2) (atoms_conn_returns (continue_atom res1) (return_atom res2)))
                        ++ (posts_conn_returns (normal_post res1) (atoms_conn_returns (normal_atom res2) (return_atom res1)))
                        ++ (posts_conn_returns (continue_post res1) (atoms_conn_returns (normal_atom res2) (return_atom res1)))
                        ;
        normal_atom := break_atom res1 ++ atoms_conn_atoms (normal_atom res1) (break_atom res2) ++ atoms_conn_atoms (continue_atom res1) (break_atom res2)
                       ++ atoms_conn_atoms (normal_atom res2) (break_atom res1);
        continue_atom := nil;
        break_atom := nil;
        return_atom := return_atom res1 ++ atoms_conn_returns (normal_atom res1) (return_atom res2) ++ atoms_conn_returns (continue_atom res1) (return_atom res2)
                       ++ atoms_conn_returns (normal_atom res2) (return_atom res1) ;
        |}) 
        
.

