Require Import VST.floyd.base2.
Require Import VST.floyd.client_lemmas.
Require Import VST.floyd.go_lower.
Require Import VST.floyd.closed_lemmas.
Require Import VST.floyd.subsume_funspec.
Require Import VST.floyd.forward_lemmas VST.floyd.call_lemmas.
Require Import VST.floyd.extcall_lemmas.
Require Import VST.floyd.nested_field_lemmas.
Require Import VST.floyd.efield_lemmas.
Require Import VST.floyd.type_induction.
Require Import VST.floyd.mapsto_memory_block.
Require Import VST.floyd.data_at_rec_lemmas.
Require Import VST.floyd.field_at.
Require Import VST.floyd.loadstore_mapsto.
Require Import VST.floyd.loadstore_field_at.
Require Import VST.floyd.nested_loadstore.
Require Import VST.floyd.sc_set_load_store.
Require Import VST.floyd.stronger.
Require Import VST.floyd.local2ptree_denote.
Require Import VST.floyd.local2ptree_eval.
Require Import VST.floyd.reptype_lemmas.
Require Import VST.floyd.proj_reptype_lemmas.
Require Import VST.floyd.replace_refill_reptype_lemmas.
Require Import VST.floyd.aggregate_type.
Require Import VST.floyd.entailer.
Require Import VST.floyd.globals_lemmas.
Require Import VST.floyd.semax_tactics.
Require Import VST.floyd.for_lemmas.
Require Import VST.floyd.diagnosis.
Require Import VST.floyd.simpl_reptype.
Require Import VST.floyd.nested_pred_lemmas.
Require Import VST.floyd.freezer.
Require Import VST.floyd.forward.
Import Cop.
Import Cop2.
Import Clight_Cop2.
Import LiftNotation.

Local Open Scope logic.

Ltac start_function hint tac :=
  let HINT := fresh "HINT" in
 leaf_function;
 match goal with |- semax_body ?V ?G ?F ?spec =>
    check_normalized F;
    let s := fresh "spec" in
    pose (s:=spec); hnf in s; cbn zeta in s; (* dependent specs defined with Program Definition often have extra lets *)
   repeat lazymatch goal with
    | s := (_, NDmk_funspec _ _ _ _ _) |- _ => fail
    | s := (_, mk_funspec _ _ _ _ _ _ _) |- _ => fail
    | s := (_, ?a _ _ _ _) |- _ => unfold a in s
    | s := (_, ?a _ _ _) |- _ => unfold a in s
    | s := (_, ?a _ _) |- _ => unfold a in s
    | s := (_, ?a _) |- _ => unfold a in s
    | s := (_, ?a) |- _ => unfold a in s
    end;
    lazymatch goal with
    | s :=  (_,  WITH _: globals
               PRE  [] main_pre _ _ nil _
               POST [ tint ] _) |- _ => idtac
    | s := ?spec' |- _ => check_canonical_funspec spec'
   end;
   change (semax_body V G F s); subst s
 end;
 let DependedTypeList := fresh "DependedTypeList" in
 unfold NDmk_funspec; 
 match goal with |- semax_body _ _ _ (pair _ (mk_funspec _ _ _ ?Pre _ _ _)) =>
   split; [split3; [check_parameter_types' | check_return_type
          | try (apply compute_list_norepet_e; reflexivity);
             fail "Duplicate formal parameter names in funspec signature"  ] 
         |];
   match Pre with
   | (fun _ i => _) => intros Espec DependedTypeList i; set (HINT := hint i)
   end;
   simpl fn_body; simpl fn_params; simpl fn_return
 end;
 try match goal with |- semax _ (fun rho => ?A rho * ?B rho) _ _ =>
     change (fun rho => ?A rho * ?B rho) with (A * B)
  end;
 simpl functors.MixVariantFunctor._functor in *;
 simpl rmaps.dependent_type_functor_rec;
 clear DependedTypeList;
 repeat match goal with
 | |- @semax _ _ _ (match ?p with (a,b) => _ end * _) _ _ =>
             destruct p as [a b]
 | |- @semax _ _ _ (Clight_seplog.close_precondition _ _ match ?p with (a,b) => _ end * _) _ _ =>
             destruct p as [a b]
 | |- @semax _ _ _ ((match ?p with (a,b) => _ end) eq_refl * _) _ _ =>
             destruct p as [a b]
 | |- @semax _ _ _ (Clight_seplog.close_precondition _ _ ((match ?p with (a,b) => _ end) eq_refl) * _) _ _ =>
             destruct p as [a b]
        end;
 revert HINT;
(************ INSERTED CODE 1 BEGIN *************)
 match goal with
 | |- let _ := ?HINT_CODE in _ => intros _;
(************ INSERTED CODE 1 END ***************)
                                 
 first [apply elim_close_precondition; [solve [auto 50 with closed] | solve [auto 50 with closed] | ]
        | erewrite compute_close_precondition by reflexivity];
 simplify_func_tycontext;
 repeat match goal with
 | |- context [Sloop (Ssequence (Sifthenelse ?e Sskip Sbreak) ?s) Sskip] =>
       fold (Swhile e s)
 | |- context [Ssequence ?s1 (Sloop (Ssequence (Sifthenelse ?e Sskip Sbreak) ?s2) ?s3) ] =>
      match s3 with
      | Sset ?i _ => match s1 with Sset ?i' _ => unify i i' | Sskip => idtac end
      end;
      fold (Sfor s1 e s2 s3)
 end;
 try expand_main_pre;
 process_stackframe_of;
 repeat change_mapsto_gvar_to_data_at;  (* should really restrict this to only in main,
                                  but it needs to come after process_stackframe_of *)
 repeat rewrite <- data_at__offset_zero;
 try apply start_function_aux1;


(************ INSERTED CODE 2 BEGIN *************)
  tac HINT_CODE
 end
(************ INSERTED CODE 2 END ***************)



 (*
 abbreviate_semax;
 lazymatch goal with 
 | |- semax ?Delta (PROPx _ (LOCALx ?L _)) _ _ => check_parameter_vals Delta L
 | _ => idtac
 end;
 try match goal with DS := @abbreviate (PTree.t funspec) PTree.Leaf |- _ =>
     clearbody DS
 end;
 start_function_hint*).
