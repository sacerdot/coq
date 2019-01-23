(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *   The HELM Project         /   The EU MoWGLI Project       *)
(*         *   University of Bologna                                    *)
(************************************************************************)
(*          This file is distributed under the terms of the             *)
(*           GNU Lesser General Public License Version 2.1              *)
(*                                                                      *)
(*                 Copyright (C) 2000-2004, HELM Team.                  *)
(*                       http://helm.cs.unibo.it                        *)
(************************************************************************)

open Pp
open Util
open Names

(* Utility Functions *)

exception TwoModulesWhoseDirPathIsOneAPrefixOfTheOther;;
let get_module_path_of_full_path path =
 let dirpath = fst (Libnames.repr_path path) in
 let modules = Lib.library_dp () :: (Library.loaded_libraries ()) in
  match
   List.filter
    (function modul -> Libnames.is_dirpath_prefix_of modul dirpath) modules
  with
     [] ->
       Feedback.msg_warning (Pp.str ("Modules not supported: reference to "^
         Libnames.string_of_path path^" will be wrong"));
       dirpath
   | [modul] -> modul
   | _ ->
       raise TwoModulesWhoseDirPathIsOneAPrefixOfTheOther
;;

(*CSC: Problem: here we are using the wrong (???) hypothesis that there do *)
(*CSC: not exist two modules whose dir_paths are one a prefix of the other *)
let remove_module_dirpath_from_dirpath ~basedir dir =
  if Libnames.is_dirpath_prefix_of basedir dir then
   let ids = DirPath.repr dir in
   let rec remove_firsts n l =
    match n,l with
       (0,l) -> l
     | (n,he::tl) -> remove_firsts (n-1) tl
     | _ -> assert false
   in
    let ids' =
     List.rev
      (remove_firsts
        (List.length (DirPath.repr basedir))
        (List.rev ids))
    in
     ids'
  else DirPath.repr dir
;;

let error msg =
 prerr_endline msg ;
 assert false

let get_uri_of_var v pvars =
  let rec search_in_open_sections =
   function
      [] -> error ("Variable "^v^" not found")
    | he::tl as modules ->
       let dirpath = DirPath.make modules in
       if Id.List.mem (Id.of_string v) (Decls.last_section_hyps dirpath)
       then
         modules
       else
         search_in_open_sections tl
  in
   let path =
    if String.List.mem v pvars then
      []
    else
      search_in_open_sections (DirPath.repr (Lib.cwd ()))
   in
    "cic:" ^
     List.fold_left
      (fun i x -> "/" ^ Id.to_string x ^ i) "" path
;;

type tag =
   Constant of Names.Constant.t
 | Inductive of Names.MutInd.t
 | Variable of Names.variable (*XXX ?? Names.kernel_name*)
;;

type etag =
   TConstant
 | TInductive
 | TVariable
;;

let etag_of_tag =
 function
    Constant _ -> TConstant
  | Inductive _ -> TInductive
  | Variable _ -> TVariable

let ext_of_tag =
 function
    TConstant -> "con"
  | TInductive -> "ind"
  | TVariable -> "var"
;;

exception FunctorsXMLExportationNotImplementedYet;;

let subtract l1 l2 =
 let l1' = List.rev (DirPath.repr l1) in
 let l2' = List.rev (DirPath.repr l2) in
  let rec aux =
   function
      he::tl when tl = l2' -> [he]
    | he::tl -> he::(aux tl)
    | [] -> assert (l2' = []) ; []
  in
   DirPath.make (List.rev (aux l1'))
;;

let token_list_of_path dir id tag =
  let token_list_of_dirpath dirpath =
   List.rev_map Id.to_string (DirPath.repr dirpath) in
  token_list_of_dirpath dir @ [Id.to_string id ^ "." ^ (ext_of_tag tag)]

(*XXX
let token_list_of_kernel_name tag =
 let id,dir = match tag with
   | Variable kn ->
       Label.to_id (Names.label kn), Lib.cwd ()
   | Constant con ->
       Label.to_id (Names.con_label con),
       Lib.remove_section_part (Globnames.ConstRef con)
   | Inductive kn ->
       Label.to_id (Names.mind_label kn),
       Lib.remove_section_part (Globnames.IndRef (kn,0))
 in
 token_list_of_path dir id (etag_of_tag tag)
;;

let uri_of_kernel_name tag =
  let tokens = token_list_of_kernel_name tag in
   "cic:/" ^ String.concat "/" tokens

let uri_of_declaration id tag =
 let dir = Libnames.pop_dirpath_n (Lib.sections_depth ()) (Lib.cwd ()) in
 let tokens = token_list_of_path dir id tag in
  "cic:/" ^ String.concat "/" tokens

(* Special functions for handling of CCorn's CProp "sort" *)

type sort =
   Coq_sort of Term.sorts_family
 | CProp
;;

let prerr_endline _ = ();;

let family_of_term ty =
 match Term.kind_of_term ty with
    Term.Sort s -> Coq_sort (Term.family_of_sort s)
  | Term.Const _ -> CProp  (* I could check that the constant is CProp *)
  | _ -> Errors.anomaly (Pp.str "family_of_term")
;;

module CPropRetyping =
 struct
  module T = Constr
  module V = Vars

  let outsort env sigma t =
   family_of_term (DoubleTypeInference.whd_betadeltaiotacprop env sigma t)

  let rec subst_type env sigma typ = function
  | [] -> typ
  | h::rest ->
      match T.kind_of_term (DoubleTypeInference.whd_betadeltaiotacprop env sigma typ) with
        | T.Prod (na,c1,c2) -> subst_type env sigma (V.subst1 h c2) rest
        | _ -> Errors.anomaly (Pp.str "Non-functional construction")


  let sort_of_atomic_type env sigma ft args =
  let rec concl_of_arity env ar =
    match T.kind_of_term (DoubleTypeInference.whd_betadeltaiotacprop env sigma ar) with
      | T.Prod (na, t, b) -> concl_of_arity (Environ.push_rel (na,None,t) env) b
      | T.Sort s -> Coq_sort (T.family_of_sort s)
      | _ -> outsort env sigma (subst_type env sigma ft (Array.to_list args))
  in concl_of_arity env ft

let typeur sigma metamap =
  let rec type_of env cstr=
    match Term.kind_of_term cstr with
    | T.Proj _ -> assert false
    | T.Meta n ->
          (try T.strip_outer_cast (Int.List.assoc n metamap)
           with Not_found -> Errors.anomaly ~label:"type_of" (Pp.str "this is not a well-typed term"))
    | T.Rel n ->
        let (_,_,ty) = Environ.lookup_rel n env in
        V.lift n ty
    | T.Var id ->
        (try
          let (_,_,ty) = Environ.lookup_named id env in
          ty
        with Not_found ->
          Errors.anomaly ~label:"type_of" (str "variable " ++ Id.print id ++ str " unbound"))
    | T.Const c -> Typeops.type_of_constant_in env c
    | T.Evar ev -> Evd.existential_type sigma ev
    | T.Ind ind -> Inductiveops.type_of_inductive env ind
    | T.Construct cstr -> Inductiveops.type_of_constructor env cstr
    | T.Case (_,p,c,lf) ->
        let Inductiveops.IndType(_,realargs) =
          try Inductiveops.find_rectype env sigma (type_of env c)
          with Not_found -> Errors.anomaly ~label:"type_of" (Pp.str "Bad recursive type") in
        let t = Reductionops.whd_beta sigma (T.applist (p, realargs)) in
        (match Term.kind_of_term (DoubleTypeInference.whd_betadeltaiotacprop env sigma (type_of env t)) with
          | T.Prod _ -> Reductionops.whd_beta sigma (T.applist (t, [c]))
          | _ -> t)
    | T.Lambda (name,c1,c2) ->
          T.mkProd (name, c1, type_of (Environ.push_rel (name,None,c1) env) c2)
    | T.LetIn (name,b,c1,c2) ->
         V.subst1 b (type_of (Environ.push_rel (name,Some b,c1) env) c2)
    | T.Fix ((_,i),(_,tys,_)) -> tys.(i)
    | T.CoFix (i,(_,tys,_)) -> tys.(i)
    | T.App(f,args)->
        T.strip_outer_cast
          (subst_type env sigma (type_of env f) (Array.to_list args))
    | T.Cast (c,_, t) -> t
    | T.Sort _ | T.Prod _ ->
       match sort_of env cstr with
          Coq_sort T.InProp -> T.mkProp
        | Coq_sort T.InSet -> T.mkSet
        | Coq_sort T.InType -> T.mkType Univ.type1_univ (* ERROR HERE *)
        | CProp -> T.mkConst DoubleTypeInference.cprop

  and sort_of env t =
    match Term.kind_of_term t with
    | T.Cast (c,_, s) when T.isSort s -> family_of_term s
    | T.Sort (T.Prop c) -> Coq_sort T.InType
    | T.Sort (T.Type u) -> Coq_sort T.InType
    | T.Prod (name,t,c2) ->
       (match sort_of env t,sort_of (Environ.push_rel (name,None,t) env) c2 with
          | _, (Coq_sort T.InProp as s) -> s
          | Coq_sort T.InProp, (Coq_sort T.InSet as s)
          | Coq_sort T.InSet, (Coq_sort T.InSet as s) -> s
          | Coq_sort T.InType, (Coq_sort T.InSet as s)
          | CProp, (Coq_sort T.InSet as s) when
              fst (Environ.engagement env) = Declarations.ImpredicativeSet -> s
          | Coq_sort T.InType, Coq_sort T.InSet
          | CProp, Coq_sort T.InSet -> Coq_sort T.InType
          | _, (Coq_sort T.InType as s) -> s (*Type Univ.dummy_univ*)
          | _, (CProp as s) -> s)
    | T.App(f,args) -> sort_of_atomic_type env sigma (type_of env f) args
    | T.Lambda _ | T.Fix _ | T.Construct _ ->
        Errors.anomaly ~label:"sort_of" (Pp.str "Not a type (1)")
    | _ -> outsort env sigma (type_of env t)

  and sort_family_of env t =
    match T.kind_of_term t with
    | T.Cast (c,_, s) when T.isSort s -> family_of_term s
    | T.Sort (T.Prop c) -> Coq_sort T.InType
    | T.Sort (T.Type u) -> Coq_sort T.InType
    | T.Prod (name,t,c2) -> sort_family_of (Environ.push_rel (name,None,t) env) c2
    | T.App(f,args) ->
       sort_of_atomic_type env sigma (type_of env f) args
    | T.Lambda _ | T.Fix _ | T.Construct _ ->
        Errors.anomaly ~label:"sort_of" (Pp.str "Not a type (1)")
    | _ -> outsort env sigma (type_of env t)

  in type_of, sort_of, sort_family_of

  let get_type_of env sigma c = let f,_,_ = typeur sigma [] in f env c
  let get_sort_family_of env sigma c = let _,_,f = typeur sigma [] in f env c

 end
;;

let get_sort_family_of env evar_map ty =
 CPropRetyping.get_sort_family_of env evar_map ty
;;

let type_as_sort env evar_map ty =
(* CCorn code *)
 family_of_term (DoubleTypeInference.whd_betadeltaiotacprop env evar_map ty)
;;

let is_a_Prop =
 function
    "Prop"
  | "CProp" -> true
  | _ -> false
;;

(* Main Functions *)

type anntypes =
 {annsynthesized : Acic.aconstr ; annexpected : Acic.aconstr option}
;;

let gen_id seed =
 let res = "i" ^ string_of_int !seed in
  incr seed ;
  res
;;

let fresh_id seed ids_to_terms constr_to_ids ids_to_father_ids =
 fun father t ->
  let res = gen_id seed in
   Hashtbl.add ids_to_father_ids res father ;
   Hashtbl.add ids_to_terms res t ;
   Acic.CicHash.add constr_to_ids t res ;
   res
;;

let source_id_of_id id = "#source#" ^ id;;

let acic_of_cic_context' computeinnertypes seed ids_to_terms constr_to_ids
 ids_to_father_ids ids_to_inner_sorts ids_to_inner_types
 ?(fake_dependent_products=false) env idrefs evar_map t expectedty
=
  let fresh_id' = fresh_id seed ids_to_terms constr_to_ids ids_to_father_ids in
   (* CSC: do you have any reasonable substitute for 503? *)
   let terms_to_types = Acic.CicHash.create 503 in
    DoubleTypeInference.double_type_of env evar_map t expectedty terms_to_types ;
    let rec aux computeinnertypes father passed_lambdas_or_prods_or_letins env
     idrefs ?(subst=None,[]) tt
    =
     let fresh_id'' = fresh_id' father tt in
     let aux' = aux computeinnertypes (Some fresh_id'') [] in
      let string_of_sort_family =
       function
          Coq_sort Term.InProp -> "Prop"
        | Coq_sort Term.InSet  -> "Set"
        | Coq_sort Term.InType -> "Type"
        | CProp -> "CProp"
      in
      let string_of_sort t =
       string_of_sort_family
        (type_as_sort env evar_map t)
      in
       let ainnertypes,innertype,innersort,expected_available =
        let {DoubleTypeInference.synthesized = synthesized;
             DoubleTypeInference.expected = expected} =
         if false (*computeinnertypes*) then
try
          Acic.CicHash.find terms_to_types tt
with e when Errors.noncritical e ->
(*CSC: Warning: it really happens, for example in Ring_theory!!! *)
Pp.msg_debug (Pp.(++) (Pp.str "BUG: this subterm was not visited during the double-type-inference: ") (Printer.pr_lconstr tt)) ; assert false
         else
          (* We are already in an inner-type and Coscoy's double *)
          (* type inference algorithm has not been applied.      *)
          (* We need to refresh the universes because we are doing *)
          (* type inference on an already inferred type.           *)
          {DoubleTypeInference.synthesized =
            Reductionops.nf_beta evar_map
             (CPropRetyping.get_type_of env evar_map
              ((* Termops.refresh_universes *) tt)) ;
           DoubleTypeInference.expected = None}
        in
         let innersort =
          let synthesized_innersort =
           get_sort_family_of env evar_map synthesized
          in
           match expected with
              None -> synthesized_innersort
            | Some ty ->
              let expected_innersort =
               get_sort_family_of env evar_map ty
              in
               match expected_innersort, synthesized_innersort with
                  CProp, _
                | _, CProp -> CProp
                | _, _ -> expected_innersort
         in
(* Debugging only:
print_endline "PASSATO" ; flush stdout ;
*)
          let ainnertypes,expected_available =
           if computeinnertypes then
            let annexpected,expected_available =
               match expected with
                  None -> None,false
                | Some expectedty' ->
                   Some (aux false (Some fresh_id'') [] env idrefs expectedty'),
                    true
            in
             Some
              {annsynthesized =
                aux false (Some fresh_id'') [] env idrefs synthesized ;
               annexpected = annexpected
              }, expected_available
           else
            None,false
          in
           ainnertypes,synthesized, string_of_sort_family innersort,
            expected_available
       in
        let add_inner_type id =
         match ainnertypes with
            None -> ()
          | Some ainnertypes -> Hashtbl.add ids_to_inner_types id ainnertypes
        in

         (* explicit_substitute_and_eta_expand_if_required h t t'         *)
         (* where [t] = [] and [tt] = [h]{[t']} ("{.}" denotes explicit   *)
         (* named substitution) or [tt] = (App [h]::[t]) (and [t'] = [])  *)
         (* check if [h] is a term that requires an explicit named        *)
         (* substitution and, in that case, uses the first arguments of   *)
         (* [t] as the actual arguments of the substitution. If there     *)
         (* are not enough parameters in the list [t], then eta-expansion *)
         (* is performed.                                                 *)
         let
          explicit_substitute_and_eta_expand_if_required h t t'
           compute_result_if_eta_expansion_not_required
         =
          let subst,residual_args,uninst_vars =
           let variables,basedir =
             try
               let g = Globnames.global_of_constr h in
               let sp =
                match g with
                   Globnames.ConstructRef ((induri,_),_)
                 | Globnames.IndRef (induri,_) ->
                    Nametab.path_of_global (Globnames.IndRef (induri,0))
                 | Globnames.VarRef id ->
                    (* Invariant: variables are never cooked in Coq *)
                    raise Not_found
                 | _ -> Nametab.path_of_global g
               in
               Dischargedhypsmap.get_discharged_hyps sp,
               get_module_path_of_full_path sp
             with Not_found ->
                (* no explicit substitution *)
                [], Libnames.dirpath_of_string "dummy"
           in
           (* returns a triple whose first element is  *)
           (* an explicit named substitution of "type" *)
           (* (variable * argument) list, whose        *)
           (* second element is the list of residual   *)
           (* arguments and whose third argument is    *)
           (* the list of uninstantiated variables     *)
           let rec get_explicit_subst variables arguments =
            match variables,arguments with
               [],_ -> [],arguments,[]
             | _,[] -> [],[],variables
             | he1::tl1,he2::tl2 ->
                let subst,extra_args,uninst = get_explicit_subst tl1 tl2 in
                let (he1_sp, he1_id) = Libnames.repr_path he1 in
                let he1' = remove_module_dirpath_from_dirpath ~basedir he1_sp in
                let he1'' =
                 String.concat "/"
                  (List.rev_map Id.to_string he1') ^ "/"
                 ^ (Id.to_string he1_id) ^ ".var"
                in
                 (he1'',he2)::subst, extra_args, uninst
           in
            get_explicit_subst variables t'
          in
           let uninst_vars_length = List.length uninst_vars in
            if uninst_vars_length > 0 then
             (* Not enough arguments provided. We must eta-expand! *)
             let un_args,_ =
              Term.decompose_prod_n uninst_vars_length
               (CPropRetyping.get_type_of env evar_map tt)
             in
              let eta_expanded =
               let arguments =
                List.map (Vars.lift uninst_vars_length) t @
                 Termops.rel_list 0 uninst_vars_length
               in
                Unshare.unshare
                 (Term.lamn uninst_vars_length un_args
                  (Term.applistc h arguments))
              in
               DoubleTypeInference.double_type_of env evar_map eta_expanded
                None terms_to_types ;
               Hashtbl.remove ids_to_inner_types fresh_id'' ;
               aux' env idrefs eta_expanded
            else
             compute_result_if_eta_expansion_not_required subst residual_args
         in

          (* Now that we have all the auxiliary functions we  *)
          (* can finally proceed with the main case analysis. *)
          match Term.kind_of_term tt with
          | Term.Proj _ -> assert false
          | Term.Rel n ->
              let id =
               match List.nth (Environ.rel_context env) (n - 1) with
                  (Names.Name id,_,_)   -> id
                | (Names.Anonymous,_,_) -> Nameops.make_ident "_" None
              in
               Hashtbl.add ids_to_inner_sorts fresh_id'' innersort ;
               if is_a_Prop innersort  && expected_available then
                add_inner_type fresh_id'' ;
               Acic.ARel (fresh_id'', n, List.nth idrefs (n-1), id)
           | Term.Var id ->
	      let pvars = Termops.ids_of_named_context (Environ.named_context env) in
	      let pvars = List.map Id.to_string pvars in
              let path = get_uri_of_var (Id.to_string id) pvars in
               Hashtbl.add ids_to_inner_sorts fresh_id'' innersort ;
               if is_a_Prop innersort  && expected_available then
                add_inner_type fresh_id'' ;
               Acic.AVar
                (fresh_id'', path ^ "/" ^ (Id.to_string id) ^ ".var")
           | Term.Evar (n,l) ->
              Hashtbl.add ids_to_inner_sorts fresh_id'' innersort ;
              if is_a_Prop innersort  && expected_available then
               add_inner_type fresh_id'' ;
              Acic.AEvar
               (fresh_id'', n, Array.to_list (Array.map (aux' env idrefs) l))
           | Term.Meta _ -> Errors.anomaly (Pp.str "Meta met during exporting to XML")
           | Term.Sort s -> Acic.ASort (fresh_id'', s)
           | Term.Cast (v,_, t) ->
              Hashtbl.add ids_to_inner_sorts fresh_id'' innersort ;
              if is_a_Prop innersort then
               add_inner_type fresh_id'' ;
              Acic.ACast (fresh_id'', aux' env idrefs v, aux' env idrefs t)
           | Term.Prod (n,s,t) ->
              let n' =
               match n with
                  Names.Anonymous -> Names.Anonymous
                | _ ->
                  if not fake_dependent_products && Vars.noccurn 1 t then
                   Names.Anonymous
                  else
                   Names.Name
                    (Namegen.next_name_away n (Termops.ids_of_context env))
              in
               Hashtbl.add ids_to_inner_sorts fresh_id''
                (string_of_sort innertype) ;
               let sourcetype = CPropRetyping.get_type_of env evar_map s in
                Hashtbl.add ids_to_inner_sorts (source_id_of_id fresh_id'')
                 (string_of_sort sourcetype) ;
               let new_passed_prods =
                let father_is_prod =
                 match father with
                    None -> false
                  | Some father' ->
                     match
                      Term.kind_of_term (Hashtbl.find ids_to_terms father')
                     with
                        Term.Prod _ -> true
                      | _ -> false
                in
                 (fresh_id'', n', aux' env idrefs s)::
                  (if father_is_prod then
                    passed_lambdas_or_prods_or_letins
                   else [])
               in
                let new_env = Environ.push_rel (n', None, s) env in
                let new_idrefs = fresh_id''::idrefs in
                 (match Term.kind_of_term t with
                     Term.Prod _ ->
                      aux computeinnertypes (Some fresh_id'') new_passed_prods
                       new_env new_idrefs t
                   | _ ->
                     Acic.AProds (new_passed_prods, aux' new_env new_idrefs t))
           | Term.Lambda (n,s,t) ->
              let n' =
               match n with
                  Names.Anonymous -> Names.Anonymous
                | _ ->
                  Names.Name (Namegen.next_name_away n (Termops.ids_of_context env))
              in
               Hashtbl.add ids_to_inner_sorts fresh_id'' innersort ;
               let sourcetype = CPropRetyping.get_type_of env evar_map s in
                Hashtbl.add ids_to_inner_sorts (source_id_of_id fresh_id'')
                 (string_of_sort sourcetype) ;
               let father_is_lambda =
                match father with
                   None -> false
                 | Some father' ->
                    match
                     Term.kind_of_term (Hashtbl.find ids_to_terms father')
                    with
                       Term.Lambda _ -> true
                     | _ -> false
               in
                if is_a_Prop innersort &&
                   ((not father_is_lambda) || expected_available)
                then add_inner_type fresh_id'' ;
                let new_passed_lambdas =
                 (fresh_id'',n', aux' env idrefs s)::
                  (if father_is_lambda then
                    passed_lambdas_or_prods_or_letins
                   else []) in
                let new_env = Environ.push_rel (n', None, s) env in
                let new_idrefs = fresh_id''::idrefs in
                 (match Term.kind_of_term t with
                     Term.Lambda _ ->
                      aux computeinnertypes (Some fresh_id'') new_passed_lambdas
                       new_env new_idrefs t
                   | _ ->
                     let t' = aux' new_env new_idrefs t in
                      (* eta-expansion for explicit named substitutions *)
                      (* can create nested Lambdas. Here we perform the *)
                      (* flattening.                                    *)
                      match t' with
                         Acic.ALambdas (lambdas, t'') ->
                          Acic.ALambdas (lambdas@new_passed_lambdas, t'')
                       | _ ->
                         Acic.ALambdas (new_passed_lambdas, t')
                 )
           | Term.LetIn (n,s,t,d) ->
              let id =
               match n with
                   Names.Anonymous -> Id.of_string "_X"
                 | Names.Name id -> id
              in
              let n' =
               Names.Name (Namegen.next_ident_away id (Termops.ids_of_context env))
              in
               Hashtbl.add ids_to_inner_sorts fresh_id'' innersort ;
               let sourcesort =
                get_sort_family_of env evar_map
                 (CPropRetyping.get_type_of env evar_map s)
               in
                Hashtbl.add ids_to_inner_sorts (source_id_of_id fresh_id'')
                 (string_of_sort_family sourcesort) ;
               let father_is_letin =
                match father with
                   None -> false
                 | Some father' ->
                    match
                     Term.kind_of_term (Hashtbl.find ids_to_terms father')
                    with
                       Term.LetIn _ -> true
                     | _ -> false
               in
                if is_a_Prop innersort then
                 add_inner_type fresh_id'' ;
                let new_passed_letins =
                 (fresh_id'',n', aux' env idrefs s)::
                  (if father_is_letin then
                    passed_lambdas_or_prods_or_letins
                   else []) in
                let new_env = Environ.push_rel (n', Some s, t) env in
                let new_idrefs = fresh_id''::idrefs in
                 (match Term.kind_of_term d with
                     Term.LetIn _ ->
                      aux computeinnertypes (Some fresh_id'') new_passed_letins
                       new_env new_idrefs d
                   | _ -> Acic.ALetIns
                           (new_passed_letins, aux' new_env new_idrefs d))
           | Term.App (h,t) ->
              Hashtbl.add ids_to_inner_sorts fresh_id'' innersort ;
              if is_a_Prop innersort then
               add_inner_type fresh_id'' ;
              let
               compute_result_if_eta_expansion_not_required subst residual_args
              =
               let residual_args_not_empty = residual_args <> [] in
               let h' =
                if residual_args_not_empty then
                 aux' env idrefs ~subst:(None,subst) h
                else
                 aux' env idrefs ~subst:(Some fresh_id'',subst) h
               in
                (* maybe all the arguments were used for the explicit *)
                (* named substitution                                 *)
                if residual_args_not_empty then
                 Acic.AApp (fresh_id'', h'::residual_args)
                else
                 h'
              in
               let t' =
                Array.fold_right (fun x i -> (aux' env idrefs x)::i) t []
               in
                explicit_substitute_and_eta_expand_if_required h
                 (Array.to_list t) t'
                 compute_result_if_eta_expansion_not_required
           | Term.Const (kn,u) ->
              Hashtbl.add ids_to_inner_sorts fresh_id'' innersort ;
              if is_a_Prop innersort  && expected_available then
               add_inner_type fresh_id'' ;
              let compute_result_if_eta_expansion_not_required _ _ =
               Acic.AConst (fresh_id'', subst, (uri_of_kernel_name (Constant kn)))
              in
               let (_,subst') = subst in
                explicit_substitute_and_eta_expand_if_required tt []
                 (List.map snd subst')
                 compute_result_if_eta_expansion_not_required
           | Term.Ind ((kn,i),u) ->
              let compute_result_if_eta_expansion_not_required _ _ =
               Acic.AInd (fresh_id'', subst, (uri_of_kernel_name (Inductive kn)), i)
              in
               let (_,subst') = subst in
                explicit_substitute_and_eta_expand_if_required tt []
                 (List.map snd subst')
                 compute_result_if_eta_expansion_not_required
           | Term.Construct (((kn,i),j),u) ->
              Hashtbl.add ids_to_inner_sorts fresh_id'' innersort ;
              if is_a_Prop innersort  && expected_available then
               add_inner_type fresh_id'' ;
              let compute_result_if_eta_expansion_not_required _ _ =
               Acic.AConstruct
                (fresh_id'', subst, (uri_of_kernel_name (Inductive kn)), i, j)
              in
               let (_,subst') = subst in
                explicit_substitute_and_eta_expand_if_required tt []
                 (List.map snd subst')
                 compute_result_if_eta_expansion_not_required
           | Term.Case ({Term.ci_ind=(kn,i)},ty,term,a) ->
              Hashtbl.add ids_to_inner_sorts fresh_id'' innersort ;
              if is_a_Prop innersort then
               add_inner_type fresh_id'' ;
              let a' =
               Array.fold_right (fun x i -> (aux' env idrefs x)::i) a []
              in
               Acic.ACase
                (fresh_id'', (uri_of_kernel_name (Inductive kn)), i,
                  aux' env idrefs ty, aux' env idrefs term, a')
           | Term.Fix ((ai,i),(f,t,b)) ->
              Hashtbl.add ids_to_inner_sorts fresh_id'' innersort ;
              if is_a_Prop innersort then add_inner_type fresh_id'' ;
              let fresh_idrefs =
               Array.init (Array.length t) (function _ -> gen_id seed) in
              let new_idrefs =
               (List.rev (Array.to_list fresh_idrefs)) @ idrefs
              in
               let f' =
                let ids = ref (Termops.ids_of_context env) in
                 Array.map
                  (function
                      Names.Anonymous -> Errors.error "Anonymous fix function met"
                    | Names.Name id as n ->
                       let res = Names.Name (Namegen.next_name_away n !ids) in
                        ids := id::!ids ;
                        res
                 ) f
               in
                Acic.AFix (fresh_id'', i,
                 Array.fold_right
                  (fun (id,fi,ti,bi,ai) i ->
                    let fi' =
                     match fi with
                        Names.Name fi -> fi
                      | Names.Anonymous -> Errors.error "Anonymous fix function met"
                    in
                     (id, fi', ai,
                      aux' env idrefs ti,
                      aux' (Environ.push_rec_types (f',t,b) env) new_idrefs bi)::i)
                  (Array.mapi
                   (fun j x -> (fresh_idrefs.(j),x,t.(j),b.(j),ai.(j))) f'
                  ) []
                 )
           | Term.CoFix (i,(f,t,b)) ->
              Hashtbl.add ids_to_inner_sorts fresh_id'' innersort ;
              if is_a_Prop innersort then add_inner_type fresh_id'' ;
              let fresh_idrefs =
               Array.init (Array.length t) (function _ -> gen_id seed) in
              let new_idrefs =
               (List.rev (Array.to_list fresh_idrefs)) @ idrefs
              in
               let f' =
                let ids = ref (Termops.ids_of_context env) in
                 Array.map
                  (function
                      Names.Anonymous -> Errors.error "Anonymous fix function met"
                    | Names.Name id as n ->
                       let res = Names.Name (Namegen.next_name_away n !ids) in
                        ids := id::!ids ;
                        res
                 ) f
               in
                Acic.ACoFix (fresh_id'', i,
                 Array.fold_right
                  (fun (id,fi,ti,bi) i ->
                    let fi' =
                     match fi with
                        Names.Name fi -> fi
                      | Names.Anonymous -> Errors.error "Anonymous fix function met"
                    in
                     (id, fi',
                      aux' env idrefs ti,
                      aux' (Environ.push_rec_types (f',t,b) env) new_idrefs bi)::i)
                  (Array.mapi
                    (fun j x -> (fresh_idrefs.(j),x,t.(j),b.(j)) ) f'
                  ) []
                 )
    in
     aux computeinnertypes None [] env idrefs t
;;

(* Obsolete [HH 1/2009]
let acic_of_cic_context metasenv context t =
 let ids_to_terms = Hashtbl.create 503 in
 let constr_to_ids = Acic.CicHash.create 503 in
 let ids_to_father_ids = Hashtbl.create 503 in
 let ids_to_inner_sorts = Hashtbl.create 503 in
 let ids_to_inner_types = Hashtbl.create 503 in
 let seed = ref 0 in
   acic_of_cic_context' true seed ids_to_terms constr_to_ids ids_to_father_ids
    ids_to_inner_sorts ids_to_inner_types metasenv context t,
   ids_to_terms, ids_to_father_ids, ids_to_inner_sorts, ids_to_inner_types
;;
*)

let acic_object_of_cic_object sigma obj =
  let ids_to_terms = Hashtbl.create 503 in
  let constr_to_ids = Acic.CicHash.create 503 in
  let ids_to_father_ids = Hashtbl.create 503 in
  let ids_to_inner_sorts = Hashtbl.create 503 in
  let ids_to_inner_types = Hashtbl.create 503 in
  let ids_to_conjectures = Hashtbl.create 11 in
  let ids_to_hypotheses = Hashtbl.create 127 in
  let hypotheses_seed = ref 0 in
  let conjectures_seed = ref 0 in
  let seed = ref 0 in
  let acic_term_of_cic_term_context' =
   acic_of_cic_context' true seed ids_to_terms constr_to_ids ids_to_father_ids
    ids_to_inner_sorts ids_to_inner_types in
(*CSC: is this the right env to use? Hhmmm. There is a problem: in    *)
(*CSC: Global.env () the object we are exporting is already defined,  *)
(*CSC: either in the environment or in the named context (in the case *)
(*CSC: of variables. Is this a problem?                               *)
  let env = Global.env () in
  let acic_term_of_cic_term' ?fake_dependent_products =
   acic_term_of_cic_term_context' ?fake_dependent_products env [] sigma in
(*CSC: the fresh_id is not stored anywhere. This _MUST_ be fixed using *)
(*CSC: a modified version of the already existent fresh_id function    *)
  let fresh_id () =
   let res = "i" ^ string_of_int !seed in
    incr seed ;
    res
  in
   let aobj =
    match obj with
      Acic.Constant (id,bo,ty,params) ->
       let abo =
        match bo with
           None -> None
         | Some bo' -> Some (acic_term_of_cic_term' bo' (Some ty))
       in
       let aty = acic_term_of_cic_term' ty None in
        Acic.AConstant (fresh_id (),id,abo,aty,params)
    | Acic.Variable (id,bo,ty,params) ->
       let abo =
        match bo with
           Some bo -> Some (acic_term_of_cic_term' bo (Some ty))
         | None -> None
       in
       let aty = acic_term_of_cic_term' ty None in
        Acic.AVariable (fresh_id (),id,abo,aty,params)
    | Acic.CurrentProof (id,conjectures,bo,ty) ->
       let aconjectures =
        List.map
         (function (i,canonical_context,term) as conjecture ->
           let cid = "c" ^ string_of_int !conjectures_seed in
            Hashtbl.add ids_to_conjectures cid conjecture ;
            incr conjectures_seed ;
            let canonical_env,idrefs',acanonical_context =
             let rec aux env idrefs =
              function
                 [] -> env,idrefs,[]
               | ((n,decl_or_def) as hyp)::tl ->
                  let hid = "h" ^ string_of_int !hypotheses_seed in
                  let new_idrefs = hid::idrefs in
                   Hashtbl.add ids_to_hypotheses hid hyp ;
                   incr hypotheses_seed ;
                   match decl_or_def with
                       Acic.Decl t ->
                        let final_env,final_idrefs,atl =
                         aux (Environ.push_rel (Names.Name n,None,t) env)
                          new_idrefs tl
                        in
                         let at =
                          acic_term_of_cic_term_context' env idrefs sigma t None
                         in
                          final_env,final_idrefs,(hid,(n,Acic.Decl at))::atl
                     | Acic.Def (t,ty) ->
                        let final_env,final_idrefs,atl =
                         aux
                          (Environ.push_rel (Names.Name n,Some t,ty) env)
                           new_idrefs tl
                        in
                         let at =
                          acic_term_of_cic_term_context' env idrefs sigma t None
                         in
                         let dummy_never_used =
                          let s = "dummy_never_used" in
                           Acic.ARel (s,99,s,Id.of_string s)
                         in
                          final_env,final_idrefs,
                           (hid,(n,Acic.Def (at,dummy_never_used)))::atl
             in
              aux env [] canonical_context
            in
             let aterm =
              acic_term_of_cic_term_context' canonical_env idrefs' sigma term
               None
             in
              (cid,i,List.rev acanonical_context,aterm)
         ) conjectures in
       let abo = acic_term_of_cic_term_context' env [] sigma bo (Some ty) in
       let aty = acic_term_of_cic_term_context' env [] sigma ty None in
        Acic.ACurrentProof (fresh_id (),id,aconjectures,abo,aty)
    | Acic.InductiveDefinition (tys,params,paramsno) ->
       let env' =
        List.fold_right
         (fun (name,_,arity,_) env ->
           Environ.push_rel (Names.Name name, None, arity) env
         ) (List.rev tys) env in
       let idrefs = List.map (function _ -> gen_id seed) tys in
       let atys =
        List.map2
         (fun id (name,inductive,ty,cons) ->
           let acons =
            List.map
             (function (name,ty) ->
               (name,
                 acic_term_of_cic_term_context' ~fake_dependent_products:true
                  env' idrefs Evd.empty ty None)
             ) cons
           in
            let aty =
             acic_term_of_cic_term' ~fake_dependent_products:true ty None
            in
             (id,name,inductive,aty,acons)
         ) (List.rev idrefs) tys
       in
       Acic.AInductiveDefinition (fresh_id (),atys,params,paramsno)
   in
    aobj,ids_to_terms,constr_to_ids,ids_to_father_ids,ids_to_inner_sorts,
     ids_to_inner_types,ids_to_conjectures,ids_to_hypotheses
;;
*)
let source_id_of_id _ = assert false
let token_list_of_kernel_name _ = assert false
let acic_object_of_cic_object _ = assert false
let acic_of_cic_context' _ = assert false
type anntypes =
 {annsynthesized : Acic.aconstr ; annexpected : Acic.aconstr option}
;;
