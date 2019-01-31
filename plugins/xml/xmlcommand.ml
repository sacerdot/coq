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

(* CONFIGURATION PARAMETERS *)

let verbose = ref false;;

(* UTILITY FUNCTIONS *)

let print_if_verbose s = if !verbose then print_string s;;

let error msg =
 prerr_endline msg ;
 assert false

open Decl_kinds
open Names
open Util
open Declarations

(* filter_params pvars hyps *)
(* filters out from pvars (which is a list of lists) all the variables *)
(* that does not belong to hyps (which is a simple list)               *)
(* It returns a list of couples relative section path -- list of       *)
(* variable names.                                                     *)
let filter_params pvars hyps =
 let rec aux ids =
  function
     [] -> []
   | (id,he)::tl ->
      let ids' = id::ids in
      let ids'' =
       "cic:/" ^
        String.concat "/" (List.rev_map Id.to_string ids') in
      let he' =
       ids'', List.rev (List.filter (function x -> String.List.mem x hyps) he)
      in
      let tl' = aux ids' tl in
       match he' with
          _,[] -> tl'
        | _,_  -> he'::tl'
 in
  let cwd = Lib.cwd () in
  let cwdsp = Libnames.make_path cwd (Id.of_string "dummy") in
  let modulepath = Cic2acic.get_module_path_of_full_path cwdsp in
   aux (DirPath.repr modulepath) (List.rev pvars)
;;

(* The computation is very inefficient, but we can't do anything *)
(* better unless this function is reimplemented in the Declare   *)
(* module.                                                       *)
let search_variables () =
  let cwd = Lib.cwd () in
  let cwdsp = Libnames.make_path cwd (Id.of_string "dummy") in
  let modulepath = Cic2acic.get_module_path_of_full_path cwdsp in
   let rec aux =
    function
       [] -> []
     | he::tl as modules ->
        let one_section_variables =
         let dirpath = DirPath.make (modules @ DirPath.repr modulepath) in
          let t = List.map Id.to_string (Decls.last_section_hyps dirpath) in
           [he,t]
        in
         one_section_variables @ aux tl
   in
    aux
     (Cic2acic.remove_module_dirpath_from_dirpath
       ~basedir:modulepath cwd)
;;

(* FUNCTIONS TO PRINT A SINGLE OBJECT OF COQ *)

let rec join_dirs cwd =
 function
    []  -> cwd
  | he::tail ->
      (try
        Unix.mkdir cwd 0o775
       with e when CErrors.noncritical e -> () (* ignore the errors on mkdir *)
      ) ;
     let newcwd = cwd ^ "/" ^ he in
      join_dirs newcwd tail
;;

let filename_of_path xml_library_root tag =
  match xml_library_root with
     None -> None  (* stdout *)
   | Some xml_library_root' ->
      let tokens = Cic2acic.token_list_of_kernel_name tag in
       Some (join_dirs xml_library_root' tokens)
;;

let uri_of_dirpath dir =
  "/" ^ String.concat "/"
    (List.rev_map Id.to_string (DirPath.repr dir))
;;

let uri_of_modpath mp =
 "/" ^ String.concat "/" (Cic2acic.uripath_of_modpath mp)

let filename_of_modpath xml_library_root mp =
  match xml_library_root with
     None -> assert false
   | Some xml_library_root' -> xml_library_root' ^ uri_of_modpath mp
;;

let body_filename_of_filename =
 function
    Some f -> Some (f ^ ".body")
  | None   -> None
;;

let types_filename_of_filename =
 function
    Some f -> Some (f ^ ".types")
  | None   -> None
;;

let library_dp = ref (Lib.library_dp ());; (* dummy value, always overwritten *)

let theory_filename xml_library_root =
  match xml_library_root with
    None -> None  (* stdout *)
  | Some xml_library_root' ->
     let toks = List.map Id.to_string (DirPath.repr !library_dp) in
     (* theory from A/B/C/F.v goes into A/B/C/F.theory *)
     let alltoks = List.rev toks in
       Some (join_dirs xml_library_root' alltoks ^ ".theory")

let print_object uri obj sigma filename =
 (* function to pretty print and compress an XML file *)
(*CSC: Unix.system "gzip ..." is an horrible non-portable solution. *)
 let pp xml filename =
  Xml.pp xml filename ;
  match filename with
     None -> ()
   | Some fn ->
      let fn' =
       let rec escape s n =
        try
         let p = String.index_from s n '\'' in
          String.sub s n (p - n) ^ "\\'" ^ escape s (p+1)
        with Not_found -> String.sub s n (String.length s - n)
       in
        escape fn 0
      in
       ignore (Unix.system ("gzip " ^ fn' ^ ".xml"))
 in
  let (annobj,_,constr_to_ids,_,ids_to_inner_sorts,ids_to_inner_types,_,_) =
   Cic2acic.acic_object_of_cic_object sigma obj in
  let (xml, xml') = Acic2Xml.print_object uri ids_to_inner_sorts annobj in
  let xmltypes =
   Acic2Xml.print_inner_types uri ids_to_inner_sorts ids_to_inner_types in
  pp xml filename ;
  begin
   match xml' with
      None -> ()
    | Some xml' -> pp xml' (body_filename_of_filename filename)
  end ;
  pp xmltypes (types_filename_of_filename filename)
;;

let string_list_of_named_context_list =
 List.map (fun x -> Id.to_string (Context.Named.Declaration.get_id x))
;;

(* Function to collect the variables that occur in a term. *)
(* Used only for variables (since for constants and mutual *)
(* inductive types this information is already available.  *)
let find_hyps t =
  let rec aux l t =
   match Constr.kind t with
      Constr.Var id when not (Id.List.mem id l) ->
       let boids,ty =
        match Global.lookup_named id with
           Context.Named.Declaration.LocalAssum (_,ty) -> l,ty
         | Context.Named.Declaration.LocalDef (_,bo,ty) -> aux l bo,ty
       in
         id::(aux boids ty)
    | Constr.Var _
    | Constr.Rel _
    | Constr.Meta _
    | Constr.Evar _
    | Constr.Sort _ -> l
    | Constr.Proj _ -> ignore(CErrors.todo "Proj in find_hyps"); assert false
    | Constr.Cast (te,_, ty) -> aux (aux l te) ty
    | Constr.Prod (_,s,t) -> aux (aux l s) t
    | Constr.Lambda (_,s,t) -> aux (aux l s) t
    | Constr.LetIn (_,s,_,t) -> aux (aux l s) t
    | Constr.App (he,tl) -> Array.fold_left (fun i x -> aux i x) (aux l he) tl
    | Constr.Const (con, _) ->
       let hyps = (Global.lookup_constant con).Declarations.const_hyps in
        map_and_filter l hyps @ l
    | Constr.Ind (ind,_)
    | Constr.Construct ((ind,_),_) ->
       let hyps = (fst (Global.lookup_inductive ind)).Declarations.mind_hyps in
        map_and_filter l hyps @ l
    | Constr.Case (_,t1,t2,b) ->
       Array.fold_left (fun i x -> aux i x) (aux (aux l t1) t2) b
    | Constr.Fix (_,(_,tys,bodies))
    | Constr.CoFix (_,(_,tys,bodies)) ->
       let r = Array.fold_left (fun i x -> aux i x) l tys in
        Array.fold_left (fun i x -> aux i x) r bodies
  and map_and_filter l =
   function
      [] -> []
    | e::tl when not (Id.List.mem (Context.Named.Declaration.get_id e) l) -> Context.Named.Declaration.get_id e :: (map_and_filter l tl)
    | _::tl -> map_and_filter l tl
  in
   aux [] t
;;

(* Functions to construct an object *)

let mk_variable_obj id var =
 let hyps,unsharedbody,typ =
  match var with
     Context.Named.Declaration.LocalAssum (_,typ) -> find_hyps typ,None,typ
   | Context.Named.Declaration.LocalDef (_,bo,typ) -> find_hyps typ @ find_hyps bo, Some (Unshare.unshare bo),typ
 in
  let hyps = List.map Id.to_string hyps in
  let variables = search_variables () in
  let params = filter_params variables hyps in
   Acic.Variable
    (Id.to_string id, Option.map EConstr.of_constr unsharedbody, Unshare.unshare (EConstr.of_constr typ), params)
;;

let mk_constant_obj id bo ty variables hyps =
 let hyps = string_list_of_named_context_list hyps in
 let ty = Unshare.unshare ty in
 let params = filter_params variables hyps in
  match bo with
     None ->
      Acic.Constant (Id.to_string id,None,ty,params)
   | Some c ->
      Acic.Constant
       (Id.to_string id, Some (Unshare.unshare c), ty,params)
;;

let mk_inductive_obj sp mib packs variables nparams hyps finite =
  let hyps = string_list_of_named_context_list hyps in
  let params = filter_params variables hyps in
(*  let nparams = extract_nparams packs in *)
   let tys =
    let tyno = ref (Array.length packs) in
    Array.fold_right
     (fun p i ->
       decr tyno ;
       let {Declarations.mind_consnames=consnames ;
            Declarations.mind_typename=typename } = p
       in
       let inst = Univ.AUContext.instance (Declareops.inductive_polymorphic_context mib) in
       let arity = Inductive.type_of_inductive (Global.env()) ((mib,p),inst) in
       let lc = Inductiveops.arities_of_constructors (Global.env ()) ((sp,!tyno),inst) in
       let cons =
         (Array.fold_right (fun (name,lc) i -> (name,lc)::i)
            (Array.mapi
               (fun j x ->(x,Unshare.unshare (EConstr.of_constr lc.(j)))) consnames)
            []
         ) in
       let arity = EConstr.of_constr arity in
         (typename,finite,Unshare.unshare arity,cons)::i
     ) packs []
   in
    Acic.InductiveDefinition (tys,params,nparams)
;;

(* The current channel for .theory files *)
let theory_buffer = Buffer.create 4000;;

let theory_output_string ?(do_not_quote = false) s =
  (* prepare for coqdoc post-processing *)
  let s = if do_not_quote then s else "(** #"^s^"\n#*)\n" in
  print_if_verbose s;
   Buffer.add_string theory_buffer s
;;

let kind_of_inductive isrecord kn =
 "DEFINITION",
 if (fst (Global.lookup_inductive (kn,0))).Declarations.mind_finite <> CoFinite
 then if isrecord then "Record" else "Inductive"
 else "CoInductive"
;;

let kind_of_variable id =
  match Decls.variable_kind id with
    | IsAssumption Definitional -> "VARIABLE","Assumption"
    | IsAssumption Logical -> "VARIABLE","Hypothesis"
    | IsAssumption Conjectural -> "VARIABLE","Conjecture"
    | IsDefinition Definition -> "VARIABLE","LocalDefinition"
    | IsDefinition Let ->
        Feedback.msg_warning (Pp.str "Let not supported in dtd (used LocalDefinition instead)");
        "VARIABLE","LocalDefinition"
    | IsProof _ -> "VARIABLE","LocalFact"
    | _ -> CErrors.anomaly (Pp.str "Unsupported variable kind")
;;

let kind_of_constant kn =
try (
  match Decls.constant_kind kn with
    | IsAssumption Definitional -> "AXIOM","Declaration"
    | IsAssumption Logical -> "AXIOM","Axiom"
    | IsAssumption Conjectural ->
        Feedback.msg_warning (Pp.str "Conjecture not supported in dtd (used Declaration instead)");
        "AXIOM","Declaration"
    | IsDefinition Definition -> "DEFINITION","Definition"
    | IsDefinition Let ->
        Feedback.msg_warning (Pp.str "Let not supported in dtd (used Definition instead)");
        "DEFINITION","Definition"
    | IsDefinition Example ->
        Feedback.msg_warning (Pp.str "Example not supported in dtd (used Definition instead)");
        "DEFINITION","Definition"
    | IsDefinition Coercion ->
        Feedback.msg_warning (Pp.str "Coercion not supported in dtd (used Definition instead)");
        "DEFINITION","Definition"
    | IsDefinition SubClass ->
        Feedback.msg_warning (Pp.str "SubClass not supported in dtd (used Definition instead)");
        "DEFINITION","Definition"
    | IsDefinition CanonicalStructure ->
        Feedback.msg_warning (Pp.str "CanonicalStructure not supported in dtd (used Definition instead)");
        "DEFINITION","Definition"
    | IsDefinition Fixpoint ->
        Feedback.msg_warning (Pp.str "Fixpoint not supported in dtd (used Definition instead)");
        "DEFINITION","Definition"
    | IsDefinition CoFixpoint ->
        Feedback.msg_warning (Pp.str "CoFixpoint not supported in dtd (used Definition instead)");
        "DEFINITION","Definition"
    | IsDefinition Scheme ->
        Feedback.msg_warning (Pp.str "Scheme not supported in dtd (used Definition instead)");
        "DEFINITION","Definition"
    | IsDefinition StructureComponent ->
        Feedback.msg_warning (Pp.str "StructureComponent not supported in dtd (used Definition instead)");
        "DEFINITION","Definition"
    | IsDefinition IdentityCoercion ->
        Feedback.msg_warning (Pp.str "IdentityCoercion not supported in dtd (used Definition instead)");
        "DEFINITION","Definition"
    | IsDefinition Instance ->
        Feedback.msg_warning (Pp.str "Instance not supported in dtd (used Definition instead)");
        "DEFINITION","Definition"
    | IsDefinition Method ->
        Feedback.msg_warning (Pp.str "Method not supported in dtd (used Definition instead)");
        "DEFINITION","Definition"
    | IsProof (Theorem|Lemma|Corollary|Fact|Remark as thm) ->
        "THEOREM",Kindops.string_of_theorem_kind thm
    | IsProof _ ->
        Feedback.msg_warning (Pp.str "Unsupported theorem kind (used Theorem instead)");
        "THEOREM",Kindops.string_of_theorem_kind Theorem
) with Not_found ->
   Feedback.msg_warning (Pp.str ("CRITICAL Looking for " ^ Names.Constant.to_string kn));
   "THEOREM","UNKNOWN"
;;

let kind_of_global r =
  match r with
  | Globnames.IndRef kn | Globnames.ConstructRef (kn,_) ->
      let isrecord =
	try let _ = Recordops.lookup_projections kn in true
        with Not_found -> false in
      kind_of_inductive isrecord (fst kn)
  | Globnames.VarRef id -> kind_of_variable id
  | Globnames.ConstRef kn -> kind_of_constant kn
;;

let print_object_kind uri (xmltag,variation) =
  let s =
    Printf.sprintf "<ht:%s uri=\"%s\" as=\"%s\"/>\n" xmltag uri variation
  in
  theory_output_string s
;;

(* print id dest                                                          *)
(*  where sp   is the qualified identifier (section path) of a            *)
(*             definition/theorem, variable or inductive definition       *)
(*  and   dest is either None (for stdout) or (Some filename)             *)
(* pretty prints via Xml.pp the object whose identifier is id on dest     *)
(* Note: it is printed only (and directly) the most cooked available      *)
(*       form of the definition (all the parameters are                   *)
(*       lambda-abstracted, but the object can still refer to variables)  *)
let print glob_ref kind xml_library_root =
  (* Variables are the identifiers of the variables in scope *)
  let variables = search_variables () in
  let tag,obj =
   match glob_ref with
      Globnames.VarRef id ->
       (* this kn is fake since it is not provided by Coq *)
       let kn = Lib.make_kn id in
       let var = Global.lookup_named id in
        Cic2acic.Variable kn,mk_variable_obj id var
    | Globnames.ConstRef kn ->
       let id = Label.to_id (Names.Constant.label kn) in
       let cb = Global.lookup_constant kn in
       let val0 = cb.Declarations.const_body in
       let typ = cb.Declarations.const_type in
       let hyps = cb.Declarations.const_hyps in
       let val0 =
        match val0 with
           Undef _ -> None
         | Def x -> Some (Mod_subst.force_constr x)
         | OpaqueDef x ->
            let env = Global.env () in
            Some (Opaqueproof.force_proof (Environ.opaque_tables env) x) in
       let val0 = Option.map EConstr.of_constr val0 in
       let typ = EConstr.of_constr typ in
        Cic2acic.Constant kn,mk_constant_obj id val0 typ variables hyps
    | Globnames.IndRef (kn,_) ->
       let mib = Global.lookup_mind kn in
       let {Declarations.mind_nparams=nparams;
	    Declarations.mind_packets=packs ;
            Declarations.mind_hyps=hyps;
            Declarations.mind_finite=finite} = mib in
          Cic2acic.Inductive kn,mk_inductive_obj kn mib packs variables nparams hyps (finite<>CoFinite)
    | Globnames.ConstructRef _ ->
       error ("a single constructor cannot be printed in XML")
  in
  let fn = filename_of_path xml_library_root tag in
  let uri = Cic2acic.uri_of_kernel_name tag in
  print_object_kind uri kind;
  print_object uri obj Evd.empty fn
;;

let print_ref qid fn =
  let ref = Nametab.global qid in
  print ref (kind_of_global ref) fn

(* show dest                                                  *)
(*  where dest is either None (for stdout) or (Some filename) *)
(* pretty prints via Xml.pp the proof in progress on dest     *)
let show_pftreestate internal fn (kind,pftst) id =
 if true then
   CErrors.anomaly (Pp.str "Xmlcommand.show_pftreestate is not supported in this version.")

let show fn =
 let pftst = Proof_global.give_me_the_proof () in
 let (id,kind,_) = Pfedit.current_proof_statement () in
  show_pftreestate false fn (kind,pftst) id
;;

(***** Module Printing ****)

let rec print_functor xml_library_root (*fty*) fatom (*is_type env*) mp (*locals*) = function
  |NoFunctor me -> fatom xml_library_root (*is_type env*) mp (*locals*) me
  |MoreFunctor (mbid,mtb1,me2) ->
(*
      nametab_register_modparam mbid mtb1;
      let mp1 = MPbound mbid in
      let pr_mtb1 = fty env mp1 locals mtb1 in
      let env' = Option.map (Modops.add_module_type mp1 mtb1) env in
      let locals' = (mbid, get_new_id locals (MBId.to_id mbid))::locals in
      let kwd = if is_type then "Funsig" else "Functor" in
      hov 2
        (keyword kwd ++ spc () ++
         str "(" ++ pr_id (MBId.to_id mbid) ++ str ":" ++ pr_mtb1 ++ str ")" ++
         spc() ++ print_functor fty fatom is_type env' mp locals' me2)
*) prerr_endline "IGNORING functor"

let rec print_body xml_library_root (*is_impl env*) mp (l,body) =
  (*let name = str (Label.to_string l) in*)
  match body with
    | SFBmodule x -> print_module xml_library_root x.mod_mp x
    | SFBmodtype _ -> assert false (*XXX TODO*)
    | SFBconst _(*cb*) ->
       let kn = Constant.make2 mp l in
       print (Globnames.ConstRef kn) (kind_of_constant kn) xml_library_root
(*
       let u =
         if cb.const_polymorphic then Univ.UContext.instance cb.const_universes
         else Univ.Instance.empty
       in
       let sigma = Evd.empty in
      (match cb.const_body with
        | Def _ -> def "Definition" ++ spc ()
        | OpaqueDef _ when is_impl -> def "Theorem" ++ spc ()
        | _ -> def "Parameter" ++ spc ()) ++ name ++
      (match env with
          | None -> mt ()
          | Some env ->
            str " :" ++ spc () ++
            hov 0 (Printer.pr_ltype_env env sigma
                (Vars.subst_instance_constr u
                  (Typeops.type_of_constant_type env cb.const_type))) ++
            (match cb.const_body with
              | Def l when is_impl ->
                spc () ++
                hov 2 (str ":= " ++
                       Printer.pr_lconstr_env env sigma
                          (Vars.subst_instance_constr u (Mod_subst.force_constr l)))
              | _ -> mt ()) ++ str "." ++
            Printer.pr_universe_ctx sigma (Univ.instantiate_univ_context cb.const_universes)) *)
    | SFBmind mib -> assert false (*XXX TODO*) (*
      try
        let env = Option.get env in
        pr_mutual_inductive_body env (MutInd.make2 mp l) mib
      with e when Errors.noncritical e ->
        let keyword =
          let open Decl_kinds in
          match mib.mind_finite with
          | Finite -> def "Inductive"
          | BiFinite -> def "Variant"
          | CoFinite -> def "CoInductive"
        in
        keyword ++ spc () ++ name *)

and print_structure xml_library_root (*is_type env*) mp (*locals*) struc =
  (*let env' = Option.map
    (Modops.add_structure mp struc Mod_subst.empty_delta_resolver) env in
  nametab_register_module_body mp struc;*)
  (*XXXXX *)
  (*let kwd = if is_type then "Sig" else "Struct" in
  hv 2 (keyword kwd ++ spc () ++ print_struct false env' mp struc ++
        brk (1,-2) ++ keyword "End")*)
  List.iter (print_body xml_library_root (*false env'*) mp) struc

and print_modtype xml_library_root (*env*) mp (*locals*) mtb =
 (* match mtb.mod_type_alg with
  | Some me -> print_expression true env mp locals me
  | None -> print_signature true env mp locals mtb.mod_type*)
 print_signature xml_library_root (*true env*) mp (*locals*) mtb.mod_type

and print_signature xml_library_root (*is_type env*) mp me =
 print_functor xml_library_root (*print_modtype*) print_structure (*is_type env*) mp me

and print_module xml_library_root (*env*) mp mb =
(*
  let name = print_modpath [] mp in
  let pr_equals = spc () ++ str ":= " in
  let body = match mb.mod_expr with
    | Abstract -> mt()
    | Algebraic me -> pr_equals ++ print_expression' false env mp me
    | Struct sign -> pr_equals ++ print_signature' false env mp sign
    | FullStruct -> pr_equals ++ print_signature' false env mp mb.mod_type
  in
  let modtype = match mb.mod_expr, mb.mod_type_alg with
    | FullStruct, _ -> mt ()
    | _, Some ty -> brk (1,1) ++ str": " ++ print_expression' true env mp ty
    | _, _ -> brk (1,1) ++ str": " ++ print_signature' true env mp mb.mod_type
  in
  hv 0 (keyword "Module" ++ spc () ++ name ++ modtype ++ body)
*)
  print_signature xml_library_root (*true env*) mp mb.mod_type

let print_module xml_library_root (*env*) mp mb =
 (* States.with_state_protection
    (fun mb -> eval_ppcmds (print_module xml_library_root env mp mb)) me*)
 print_module xml_library_root mp mb

let print_modtype_of_module xml_library_root mp =
 let mb = Global.lookup_module mp in
 if mb.mod_expr <> FullStruct then begin
  if xml_library_root <> None then
   let dir = filename_of_modpath xml_library_root mp in
    Unix.rename dir (dir^".impl") ;
  print_modtype xml_library_root mp mb
 end

(***** End of Module Printing ****)

(* Let's register the callbacks *)
let xml_library_root =
  try
   Some (Sys.getenv "COQ_XML_LIBRARY_ROOT")
  with Not_found -> None
;;

let proof_to_export = ref None (* holds the proof-tree to export *)
;;

let ignore = ref false;;
let _ = Hook.set Stm.tactic_being_run_hook (function b -> ignore := b);;

let _ =
  Hook.set Declaremods.xml_declare_module
   (function mp -> if not !ignore then
try (Printexc.record_backtrace true ;
begin
     prerr_endline "## DECLARE MODULE" ;
     let me = Global.lookup_module mp in
     print_module xml_library_root (*(Global.env ())*) mp me
    end)
with exn -> Printexc.print_backtrace stderr; raise exn)
;;

let _ =
  Hook.set Declaremods.xml_start_module
   (function mp -> if not !ignore then
try (Printexc.record_backtrace true ;
begin
     let s = "cic:" ^ uri_of_modpath mp in
      theory_output_string ("<ht:MODULE uri=\""^s^"\" as=\"Module\">")
     (*let me = Global.lookup_module mp in
     print_module xml_library_root (Global.env ()) mp me
     *)
    end)
with exn -> Printexc.print_backtrace stderr; raise exn)
;;

let _ =
  Hook.set Declaremods.xml_end_module
   (function mp -> if not !ignore then
try (Printexc.record_backtrace true ;
begin
     theory_output_string ("</ht:MODULE>") ;
     (*let me = Global.lookup_module mp in
     print_module xml_library_root (Global.env ()) mp me *)
     print_modtype_of_module xml_library_root mp
    end)
with exn -> Printexc.print_backtrace stderr; raise exn)
;;

let _ =
  Hook.set Declaremods.xml_start_module_type
   (function mp -> if not !ignore then
try (Printexc.record_backtrace true ;
begin
     let s = "cic:" ^ uri_of_modpath mp in
      theory_output_string ("<ht:MODULE uri=\""^s^"\" as=\"ModuleType\">")
     (*let me = Global.lookup_module mp in
     print_module xml_library_root (Global.env ()) mp me
     *)
    end)
with exn -> Printexc.print_backtrace stderr; raise exn)
;;

let _ =
  Hook.set Declaremods.xml_end_module_type
   (function mp -> if not !ignore then
try (Printexc.record_backtrace true ;
begin
     theory_output_string ("</ht:MODULE>")
     (*let me = Global.lookup_module mp in
     print_module xml_library_root (Global.env ()) mp me
     *)
    end)
with exn -> Printexc.print_backtrace stderr; raise exn)
;;
  

let _ =
  Hook.set Declare.xml_declare_variable
   (function (sp,kn) -> if not !ignore then begin
     let id = Libnames.basename sp in
     print (Globnames.VarRef id) (kind_of_variable id) xml_library_root ;
     proof_to_export := None
     end)
;;

let _ =
  Hook.set Declare.xml_declare_constant
   (function (internal,kn) -> if not !ignore then
try (Printexc.record_backtrace true ;
begin
     match !proof_to_export with
        None ->
          print (Globnames.ConstRef kn) (kind_of_constant kn)
	    xml_library_root
      | Some pftreestate ->
         (* It is a proof. Let's export it starting from the proof-tree *)
         (* I saved in the Pfedit.set_xml_cook_proof callback.          *)
        let fn = filename_of_path xml_library_root (Cic2acic.Constant kn) in
         show_pftreestate internal fn pftreestate
          (Label.to_id (Names.Constant.label kn)) ;
         proof_to_export := None end)
with exn -> Printexc.print_backtrace stderr; raise exn)
;;

let _ =
  Hook.set Declare.xml_declare_inductive
   (function (isrecord,(sp,kn)) -> if not !ignore then begin
      print (Globnames.IndRef (Names.MutInd.make1 kn,0))
        (kind_of_inductive isrecord (Names.MutInd.make1 kn))
        xml_library_root end)
;;

let _ =
  Hook.set Coqtop.xml_start_library
   (function () ->
     library_dp := Lib.library_dp ();
     Buffer.reset theory_buffer;
     theory_output_string "<?xml version=\"1.0\" encoding=\"latin1\"?>\n";
     theory_output_string ("<!DOCTYPE html [\n" ^
      "<!ENTITY % xhtml-lat1.ent    SYSTEM \"http://helm.cs.unibo.it/dtd/xhtml-lat1.ent\">\n" ^
      "<!ENTITY % xhtml-special.ent SYSTEM \"http://helm.cs.unibo.it/dtd/xhtml-special.ent\">\n" ^
      "<!ENTITY % xhtml-symbol.ent  SYSTEM \"http://helm.cs.unibo.it/dtd/xhtml-symbol.ent\">\n\n" ^
      "%xhtml-lat1.ent;\n" ^
      "%xhtml-special.ent;\n" ^
      "%xhtml-symbol.ent;\n" ^
      "]>\n\n");
     theory_output_string "<html xmlns=\"http://www.w3.org/1999/xhtml\" xmlns:ht=\"http://www.cs.unibo.it/helm/namespaces/helm-theory\" xmlns:helm=\"http://www.cs.unibo.it/helm\">\n";
     theory_output_string "<head></head>\n<body>\n")
;;

let _ =
  Hook.set Coqtop.xml_end_library
   (function () ->
      theory_output_string "</body>\n</html>\n";
      let ofn = theory_filename xml_library_root in
       begin
        match ofn with
           None ->
             Buffer.output_buffer stdout theory_buffer ;
         | Some fn ->
             let ch = open_out (fn ^ ".v") in
             Buffer.output_buffer ch theory_buffer ;
             close_out ch;
       end ;
       Option.iter
	(fun fn ->
	  let coqdoc = Filename.concat Envars.coqbin ("coqdoc" ^ Coq_config.exec_extension) in
	  let options = " --no-glob --html -s --body-only --no-index --latin1 --raw-comments" in
          let command cmd =
           if Sys.command cmd <> 0 then
            CErrors.anomaly (Pp.str ("Error executing \"" ^ cmd ^ "\""))
          in
           command (coqdoc^options^" -o "^fn^".xml "^fn^".v");
           command ("rm "^fn^".v " ^ Filename.dirname fn ^"/" ^ "coqdoc.css");
           print_string("\nWriting on file \"" ^ fn ^ ".xml\" was successful\n"))
       ofn)
;;

let _ = Hook.set CLexer.xml_output_comment (theory_output_string ~do_not_quote:true) ;;

let _ =
  Hook.set Lib.xml_open_section
    (fun _ ->
      let s = "cic:" ^ uri_of_dirpath (Lib.cwd ()) in
      theory_output_string ("<ht:SECTION uri=\""^s^"\">"))
;;

let _ =
  Hook.set Lib.xml_close_section
    (fun _ -> theory_output_string "</ht:SECTION>")
;;

let _ =
  Hook.set Library.xml_require
    (fun d -> theory_output_string
      (Printf.sprintf "<b>Require</b> <a helm:helm_link=\"href\" href=\"theory:%s.theory\">%s</a>.<br/>"
       (uri_of_dirpath d) (DirPath.to_string d)))
;;
