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

let uris_of_params hyps =
 List.rev_map (fun id ->
   let dp = Names.DirPath.repr (Decls.variable_path id) in
   "cic:/" ^ String.concat "/" (List.rev_map Id.to_string dp) ^ "/" ^ Names.Id.to_string id ^ ".var"
 ) hyps
;;

let relUri_of_id_list l = String.concat "/" (List.rev_map Id.to_string l)

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
  | Some xml_library_root ->
     let toks = List.map Id.to_string (DirPath.repr !library_dp) in
     (* theory from A/B/C/F.v goes into A/B/C/F.theory *)
     let alltoks = List.rev toks in
       Some (join_dirs xml_library_root alltoks ^ ".theory")

let expr_filename of_ xml_library_root mp =
  match xml_library_root with
    None -> None  (* stdout *)
  | Some xml_library_root ->
     let suffix =
      match of_ with
         `Impl -> ".impl.expr"
       | `MTImpl -> ".expr"
       | `Type -> ".expr" in
     Some (join_dirs xml_library_root (Cic2acic.uripath_of_modpath mp) ^ suffix ^ ".xml")

let print_object uri obj env sigma filename =
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
       ()(*ignore (Unix.system ("gzip " ^ fn' ^ ".xml"))*)
 in
  let (annobj,_,constr_to_ids,_,ids_to_inner_sorts,ids_to_inner_types,_,_) =
   Cic2acic.acic_object_of_cic_object env sigma obj in
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
 List.map (fun x -> (*Id.to_string*) (Context.Named.Declaration.get_id x))
;;

(* Function to collect the variables that occur in a term. *)
(* Used only for variables (since for constants and mutual *)
(* inductive types this information is already available.  *)
(* CSC: they are returned in random order *)
let find_hyps env t =
  let rec aux l t =
   match Constr.kind t with
      Constr.Var id when not (Id.List.mem id l) ->
       let boids,ty =
        match Environ.lookup_named id env with
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
       let hyps = (Environ.lookup_constant con env).Declarations.const_hyps in
        map_and_filter l hyps @ l
    | Constr.Ind (ind,_)
    | Constr.Construct ((ind,_),_) ->
       let hyps = (fst (Inductive.lookup_mind_specif env ind)).Declarations.mind_hyps in
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

let mk_variable_obj env id var =
 let hyps,unsharedbody,typ =
  match var with
     Context.Named.Declaration.LocalAssum (_,typ) -> find_hyps env typ,None,typ
   | Context.Named.Declaration.LocalDef (_,bo,typ) -> find_hyps env typ @ find_hyps env bo, Some (Unshare.unshare bo),typ
 in
  let params = uris_of_params hyps in
   Acic.Variable
    (Id.to_string id, Option.map EConstr.of_constr unsharedbody, Unshare.unshare (EConstr.of_constr typ), params)
;;

let mk_constant_obj id bo ty hyps =
 let hyps = string_list_of_named_context_list hyps in
 let ty = Unshare.unshare ty in
 let params = uris_of_params hyps in
  match bo with
     None ->
      Acic.Constant (Id.to_string id,None,ty,params)
   | Some c ->
      Acic.Constant
       (Id.to_string id, Some (Unshare.unshare c), ty,params)
;;

let mk_inductive_obj env sp mib packs nparams hyps finite =
  let hyps = string_list_of_named_context_list hyps in
  let params = uris_of_params hyps in
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
       let arity = Inductive.type_of_inductive env ((mib,p),inst) in
       let lc = Inductiveops.arities_of_constructors env ((sp,!tyno),inst) in
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
let theory_buffer = Buffer.create 4000

let theory_output_string ?(do_not_quote = false) s =
  (* prepare for coqdoc post-processing *)
  let s = if do_not_quote then s else "(** #"^s^"\n#*)\n" in
   print_if_verbose s;
   Buffer.add_string theory_buffer s

(* The current channel for .expr files *)
let expr_buffer = Buffer.create 400

let expr_output_string = Buffer.add_string expr_buffer

let save_expr_buffer of_ xml_library_root mp =
 let ofn = expr_filename of_ xml_library_root mp in
  begin
   match ofn with
      None ->
        Buffer.output_buffer stdout expr_buffer
    | Some fn ->
        let ch = open_out fn in
        Buffer.output_buffer ch expr_buffer ;
        close_out ch;
  end

let kind_of_inductive env isrecord kn =
 "DEFINITION",
 if (fst (Inductive.lookup_mind_specif env (kn,0))).Declarations.mind_finite <> CoFinite
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
    | IsAssumption Conjectural -> "AXIOM","Conjecture"
    | IsDefinition Definition -> "DEFINITION","Definition"
    | IsDefinition Let -> "DEFINITION","Let"
    | IsDefinition Example -> "DEFINITION","Example"
    | IsDefinition Coercion -> "DEFINITION","Coercion"
    | IsDefinition SubClass -> "DEFINITION","SubClass"
    | IsDefinition CanonicalStructure -> "DEFINITION","CanonicalStructure"
    | IsDefinition Fixpoint -> "DEFINITION","Fixpoint"
    | IsDefinition CoFixpoint -> "DEFINITION","CoFixpoint"
    | IsDefinition Scheme -> "DEFINITION","Scheme"
    | IsDefinition StructureComponent -> "DEFINITION","Projection"
    | IsDefinition IdentityCoercion -> "DEFINITION","IdentityCoercion"
    | IsDefinition Instance -> "DEFINITION","Instance"
    | IsDefinition Method -> "DEFINITION","Method"
    | IsProof (Theorem|Lemma|Corollary|Fact|Remark|Property|Proposition as thm) ->
        "THEOREM",Kindops.string_of_theorem_kind thm
) with Not_found ->
   Feedback.msg_warning (Pp.str ("CRITICAL Looking for " ^ Names.Constant.to_string kn));
   "THEOREM","UNKNOWN"
;;

let kind_of_global env r =
  match r with
  | Globnames.IndRef kn | Globnames.ConstructRef (kn,_) ->
      let isrecord =
	try let _ = Recordops.lookup_projections kn in true
        with Not_found -> false in
      kind_of_inductive env isrecord (fst kn)
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
let print ~in_theory env glob_ref kind xml_library_root =
  let tag,obj =
   match glob_ref with
      Globnames.VarRef id ->
       (* this kn is fake since it is not provided by Coq *)
       let kn = Lib.make_kn id in
       let var = Environ.lookup_named id env in
        Cic2acic.Variable kn,mk_variable_obj env id var
    | Globnames.ConstRef kn ->
       let id = Label.to_id (Names.Constant.label kn) in
       let cb = Environ.lookup_constant kn env in
       let val0 = cb.Declarations.const_body in
       let typ = cb.Declarations.const_type in
       let hyps = cb.Declarations.const_hyps in
       let val0 =
        match val0 with
           Undef _ -> None
         | Def x -> Some (Mod_subst.force_constr x)
         | OpaqueDef x ->
            Some (Opaqueproof.force_proof (Environ.opaque_tables env) x) in
       let val0 = Option.map EConstr.of_constr val0 in
       let typ = EConstr.of_constr typ in
        Cic2acic.Constant kn,mk_constant_obj id val0 typ hyps
    | Globnames.IndRef (kn,_) ->
       let mib = Environ.lookup_mind kn env in
       let {Declarations.mind_nparams=nparams;
	    Declarations.mind_packets=packs ;
            Declarations.mind_hyps=hyps;
            Declarations.mind_finite=finite} = mib in
          Cic2acic.Inductive kn,mk_inductive_obj env kn mib packs nparams hyps (finite<>CoFinite)
    | Globnames.ConstructRef _ ->
       error ("a single constructor cannot be printed in XML")
  in
  let fn = filename_of_path xml_library_root tag in
  let uri = Cic2acic.uri_of_kernel_name tag in
  if in_theory then print_object_kind uri kind;
  print_object uri obj env Evd.empty fn
;;

let print_ref qid fn =
  let ref = Nametab.global qid in
  print ~in_theory:true (Global.env ()) ref (kind_of_global (Global.env ())
   ref) fn

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

let move_to_impl xml_library_root mp =
 if xml_library_root <> None then
  let dir = filename_of_modpath xml_library_root mp in
   Unix.rename dir (dir^".impl")

let rec flatten_app mexpr l = match mexpr with
  | MEapply (mexpr, arg) -> flatten_app mexpr (arg::l)
  | MEident mp -> mp::l
  | MEwith _ -> assert false

let print_expression_body _xml_library_root _to_be_declared env mp mty _delta =
 let rec to_xml =
  function
   | MEident kn -> "<MODULE uri=\"cic:" ^ uri_of_modpath kn ^ "\"/>"
   | MEapply _ ->
       let lapp = flatten_app mty [] in
        "<APP>" ^
         String.concat ""
          (List.map (fun kn -> to_xml (MEident kn)) lapp) ^
        "</APP>"
   | MEwith(me,what) ->
       "<WITH>" ^ to_xml me ^
        (match what with
            WithDef(idl,(c,_)) ->
             let relUri = relUri_of_id_list idl in
              "<DEFINITION relURI=\"" ^ relUri ^ "\">" ^
               "???n"^
              "</DEFINITION>"
          | WithMod(idl,mp') ->
             let relUri = relUri_of_id_list idl in
             let to_ = "cic:" ^ uri_of_modpath mp' in
              "<MODULE relURI=\"" ^ relUri ^ "\" to=\"" ^ to_ ^ "\"/>"
        ) ^ "</WITH>"
 in
  expr_output_string (to_xml mty)

let rec print_functor xml_library_root ~to_be_declared fty ftyend fatom env mp delta = function
  |NoFunctor me -> fatom xml_library_root to_be_declared env mp me delta
  |MoreFunctor (mbid,mtb1,me2) ->
    let ids = Cic2acic.idlist_of_modpath mp in
    Cic2acic.register_mbids [mbid] (Names.DirPath.make (List.rev ids)) ;
    let mp1 = MPbound mbid in
    let env = Modops.add_module_type mp1 mtb1 env in
    fty xml_library_root env mp1 mtb1.mod_type_alg mtb1.mod_type mtb1.mod_delta ;
    print_functor xml_library_root ~to_be_declared:true fty ftyend fatom env mp delta me2 ;
    ftyend () ;
    Cic2acic.unregister_mbids ()

let rec print_body xml_library_root env mp (l,body) =
  match body with
    | SFBmodule mb -> print_module ~struct_already_printed:false xml_library_root env mb.mod_mp mb
    | SFBmodtype mtb ->
       let env = Modops.add_module (Modops.module_body_of_type mtb.mod_mp mtb) env in
       print_modtype xml_library_root env mtb.mod_mp mtb.mod_type_alg mtb.mod_type mtb.mod_delta
    | SFBconst _ ->
       let kn = Constant.make2 mp l in
       print ~in_theory:false env (Globnames.ConstRef kn)
        (kind_of_constant kn) xml_library_root
    | SFBmind mib ->
       let kn = MutInd.make2 mp l in
       let is_record = mib.mind_record <> NotRecord in
       print ~in_theory:false env (Globnames.IndRef (kn,0))
        (kind_of_inductive env is_record kn) xml_library_root

and print_structure xml_library_root to_be_declared env mp struc delta =
  let env =
   if to_be_declared then Modops.add_structure mp struc delta env else env in
  List.iter (print_body xml_library_root env mp) struc

and print_modtype xml_library_root env mp mtb_mod_type_alg mtb_mod_type mtb_mod_delta =
 (match mtb_mod_type_alg with
     None -> ()
   | Some alg -> print_expression `MTImpl xml_library_root env mp alg);
 print_signature xml_library_root ~to_be_declared:true env mp mtb_mod_type mtb_mod_delta

and print_signature xml_library_root ~to_be_declared env mp me delta =
 print_functor xml_library_root ~to_be_declared print_modtype (fun () -> ()) print_structure env mp delta me

and print_expression_abstr _xml_library_root _env mp _mtb_mod_type_alg _mtb_mod_type _mtb_mod_delta =
 let uri = "cic:" ^ uri_of_modpath mp in
 expr_output_string ("<ABS uri=\"" ^ uri ^ "\">")

and print_expression_abstr_end () =
 expr_output_string "</ABS>"

and print_expression of_ xml_library_root env mp expr =
 Buffer.reset expr_buffer ;
 print_functor () ~to_be_declared:false print_expression_abstr print_expression_abstr_end print_expression_body env mp () expr ;
 save_expr_buffer of_ xml_library_root mp

and print_module ~struct_already_printed xml_library_root env mp mb =
  (match mb.mod_expr with
    | Algebraic me -> print_expression `Impl xml_library_root env mp me
    | Struct sign ->
       if not struct_already_printed then
        print_signature xml_library_root ~to_be_declared:false env mp sign mb.mod_delta ;
       move_to_impl xml_library_root mp
    | Abstract -> ()
    | FullStruct -> ());
  (match mb.mod_type_alg with
      None -> ()
    | Some alg -> print_expression `Type xml_library_root env mp alg);
  if not (struct_already_printed && mb.mod_expr = FullStruct) then
   print_signature xml_library_root ~to_be_declared:false env mp mb.mod_type mb.mod_delta

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
     let s = "cic:" ^ uri_of_modpath mp in
      theory_output_string ("<ht:MODULE uri=\""^s^"\" as=\"AlgebraicModule\"/>") ;
     let me = Global.lookup_module mp in
     print_module ~struct_already_printed:false xml_library_root (Global.env ()) mp me
    end)
with exn -> Printexc.print_backtrace stderr; raise exn)
;;

let _ =
  Hook.set Declaremods.xml_declare_module_type
   (function mp -> if not !ignore then
try (Printexc.record_backtrace true ;
begin
     let s = "cic:" ^ uri_of_modpath mp in
      theory_output_string ("<ht:MODULE uri=\""^s^"\" as=\"AlgebraicModuleType\"/>") ;
     let mtb = Global.lookup_modtype mp in
     print_modtype xml_library_root (Global.env ()) mtb.mod_mp mtb.mod_type_alg mtb.mod_type mtb.mod_delta ;
    end)
with exn -> Printexc.print_backtrace stderr; raise exn)
;;

let _ =
  Hook.set Declaremods.xml_start_module
   (function (mp,args) -> if not !ignore then
try (Printexc.record_backtrace true ;
begin
     let s = "cic:" ^ uri_of_modpath mp in
      theory_output_string ("<ht:MODULE uri=\""^s^"\" as=\"Module\">") ;
     Cic2acic.register_mbids args (Lib.cwd ()) ;
     List.iter (fun id ->
       let mp = Names.ModPath.MPbound id in
       let mb = Global.lookup_module mp in
       print_module ~struct_already_printed:false xml_library_root (Global.env ()) mp mb
     ) args
    end)
with exn -> Printexc.print_backtrace stderr; raise exn)
;;

let _ =
  Hook.set Declaremods.xml_end_module
   (function mp -> if not !ignore then
try (Printexc.record_backtrace true ;
begin
     theory_output_string ("</ht:MODULE>") ;
     let mb = Environ.lookup_module mp (Global.env ()) in
     print_module ~struct_already_printed:true xml_library_root (Global.env ()) mp mb ;
     Cic2acic.unregister_mbids ()
    end)
with exn -> Printexc.print_backtrace stderr; raise exn)
;;

let _ =
  Hook.set Declaremods.xml_start_module_type
   (function (mp,args) -> if not !ignore then
try (Printexc.record_backtrace true ;
begin
     let s = "cic:" ^ uri_of_modpath mp in
      theory_output_string ("<ht:MODULE uri=\""^s^"\" as=\"ModuleType\">") ;
     Cic2acic.register_mbids args (Lib.cwd ()) ;
     List.iter (fun id ->
       let mp = Names.ModPath.MPbound id in
       let mb = Global.lookup_module mp in
       print_module ~struct_already_printed:false xml_library_root (Global.env ()) mp mb
     ) args
    end)
with exn -> Printexc.print_backtrace stderr; raise exn)
;;

let _ =
  Hook.set Declaremods.xml_end_module_type
   (function mp -> if not !ignore then
try (Printexc.record_backtrace true ;
begin
     theory_output_string ("</ht:MODULE>")
    end)
with exn -> Printexc.print_backtrace stderr; raise exn)
;;
  

let _ =
  Hook.set Declare.xml_declare_variable
   (function (sp,kn) -> if not !ignore then begin
     let id = Libnames.basename sp in
     print ~in_theory:true (Global.env ()) (Globnames.VarRef id)
      (kind_of_variable id) xml_library_root ;
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
          print ~in_theory:true (Global.env ()) (Globnames.ConstRef kn)
           (kind_of_constant kn)
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
      print ~in_theory:true (Global.env ())
       (Globnames.IndRef (Names.MutInd.make1 kn,0))
        (kind_of_inductive (Global.env ()) isrecord (Names.MutInd.make1 kn))
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
           command ("rm -f "^fn^".v " ^ Filename.dirname fn ^"/" ^ "coqdoc.css");
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
