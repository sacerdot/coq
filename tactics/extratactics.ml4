(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i camlp4deps: "parsing/grammar.cma" i*)

(* $Id$ *)

open Pp
open Pcoq
open Genarg
open Extraargs

(* Equality *)
open Equality

TACTIC EXTEND Rewrite
  [ "Rewrite" orient(b) constr_with_bindings(c) ] -> [general_rewrite_bindings b c]
END

TACTIC EXTEND RewriteIn
 [ "Rewrite" orient(b) constr_with_bindings(c) "in" ident(h) ] ->
 [general_rewrite_in b h c]
END

let h_rewriteLR x = h_rewrite true (x,Rawterm.NoBindings)

TACTIC EXTEND Replace
  [ "Replace" constr(c1) "with" constr(c2) ] -> [ replace c1 c2 ]
END

TACTIC EXTEND ReplaceIn
  [ "Replace" constr(c1) "with" constr(c2) "in" ident(h) ]
  -> [ failwith "Replace in: TODO" ]
END

TACTIC EXTEND Replacetermleft
  [ "Replace" "->" constr(c)  ] -> [ replace_term_left c ]
END

TACTIC EXTEND Replacetermright
  [ "Replace" "<-" constr(c)  ] -> [ replace_term_right c ]
END

TACTIC EXTEND Replaceterm
  [ "Replace" constr(c)  ] -> [ replace_term c ]
END

TACTIC EXTEND ReplacetermInleft
  [ "Replace"  "->" constr(c) "in" ident(h) ]
  -> [ replace_term_in_left c h ]
END

TACTIC EXTEND ReplacetermInright
  [ "Replace"  "<-" constr(c) "in" ident(h) ]
  -> [ replace_term_in_right c h ]
END

TACTIC EXTEND ReplacetermIn
  [ "Replace" constr(c) "in" ident(h) ]
  -> [ replace_term_in c h ]
END

TACTIC EXTEND DEq
  [ "Simplify_eq" quantified_hypothesis_opt(h) ] -> [ dEq h ]
END

TACTIC EXTEND Discriminate
  [ "Discriminate" quantified_hypothesis_opt(h) ] -> [ discr_tac h ]
END

let h_discrHyp id = h_discriminate (Some id)

TACTIC EXTEND Injection
  [ "Injection" quantified_hypothesis_opt(h) ] -> [ injClause h ]
END

let h_injHyp id = h_injection (Some id)

TACTIC EXTEND ConditionalRewrite
  [ "Conditional" tactic(tac) "Rewrite" orient(b) constr_with_bindings(c) ]
    -> [ conditional_rewrite b (snd tac) c ]
END

TACTIC EXTEND ConditionalRewriteIn
  [ "Conditional" tactic(tac) "Rewrite" orient(b) constr_with_bindings(c)
    "in" ident(h) ]
    -> [ conditional_rewrite_in b h (snd tac) c ]
END

TACTIC EXTEND DependentRewrite
| [ "Dependent" "Rewrite" orient(b) ident(id) ] -> [ substHypInConcl b id ]
| [ "CutRewrite" orient(b) constr(eqn) ] -> [ substConcl b eqn ]
| [ "CutRewrite" orient(b) constr(eqn) "in" ident(id) ]
      -> [ substHyp b eqn id ]
END

(* Contradiction *)
open Contradiction

TACTIC EXTEND Absurd
 [ "Absurd" constr(c) ] -> [ absurd c ]
END

TACTIC EXTEND Contradiction
 [ "Contradiction" constr_with_bindings_opt(c) ] -> [ contradiction c ]
END

(* AutoRewrite *)

open Autorewrite
TACTIC EXTEND Autorewrite
  [ "AutoRewrite" "[" ne_preident_list(l) "]" ] ->
    [ autorewrite Refiner.tclIDTAC l ]
| [ "AutoRewrite" "[" ne_preident_list(l) "]" "using" tactic(t) ] ->
    [ autorewrite (snd t) l ]
END

let add_rewrite_hint name ort t lcsr =
  let env = Global.env() and sigma = Evd.empty in
  let f c = Constrintern.interp_constr sigma env c, ort, t in
  add_rew_rules name (List.map f lcsr)

(* V7 *)
VERNAC COMMAND EXTEND HintRewrite_v7
  [ "Hint" "Rewrite" orient(o) "[" ne_constr_list(l) "]" "in" preident(b) ] ->
  [ add_rewrite_hint b o Tacexpr.TacId l ]
| [ "Hint" "Rewrite" orient(o) "[" ne_constr_list(l) "]" "in" preident(b)
    "using" tactic(t) ] ->
  [ add_rewrite_hint b o t l ]
END

(* V8 *)
VERNAC COMMAND EXTEND HintRewrite
  [ "Hint" "Rewrite" orient(o) ne_constr_list(l) ":" preident(b) ] ->
  [ add_rewrite_hint b o Tacexpr.TacId l ]
| [ "Hint" "Rewrite" orient(o) ne_constr_list(l) "using" tactic(t)
    ":" preident(b) ] ->
  [ add_rewrite_hint b o t l ]
END


(* Refine *)

open Refine

TACTIC EXTEND Refine
  [ "Refine" castedopenconstr(c) ] -> [ refine c ]
END

let refine_tac = h_refine

(* Setoid_replace *)

open Setoid_replace

TACTIC EXTEND SetoidReplace
  [ "Setoid_replace" constr(c1) "with" constr(c2) ]
  -> [ setoid_replace c1 c2 None]
END

TACTIC EXTEND SetoidRewrite
  [ "Setoid_rewrite" orient(b) constr(c) ] -> [ general_s_rewrite b c ]
END

VERNAC COMMAND EXTEND AddSetoid
| [ "Add" "Setoid" constr(a) constr(aeq) constr(t) ] -> [ add_setoid a aeq t ]
| [ "Add" "Morphism" constr(m) ":" ident(s) ] -> [ new_named_morphism s m ]
END

(* Inversion lemmas (Leminv) *)

open Inv
open Leminv

VERNAC COMMAND EXTEND DeriveInversionClear
  [ "Derive" "Inversion_clear" ident(na) ident(id) ]
  -> [ inversion_lemma_from_goal 1 na id Term.mk_Prop false inv_clear_tac ]

| [ "Derive" "Inversion_clear" natural(n) ident(na) ident(id) ]
  -> [ inversion_lemma_from_goal n na id Term.mk_Prop false inv_clear_tac ]

| [ "Derive" "Inversion_clear" ident(na) "with" constr(c) "Sort" sort(s) ]
  -> [ add_inversion_lemma_exn na c s false inv_clear_tac ]

| [ "Derive" "Inversion_clear"  ident(na) "with" constr(c) ]
  -> [ add_inversion_lemma_exn na c (Rawterm.RProp Term.Null) false inv_clear_tac ]
END

open Term
open Rawterm

VERNAC COMMAND EXTEND DeriveInversion
| [ "Derive" "Inversion" ident(na) "with" constr(c) "Sort" sort(s) ]
  -> [ add_inversion_lemma_exn na c s false half_inv_tac ]

| [ "Derive" "Inversion" ident(na) "with" constr(c) ]
  -> [ add_inversion_lemma_exn na c (RProp Null) false half_inv_tac ]

| [ "Derive" "Inversion" ident(na) ident(id) ]
  -> [ inversion_lemma_from_goal 1 na id Term.mk_Prop false half_inv_tac ]

| [ "Derive" "Inversion" natural(n) ident(na) ident(id) ]
  -> [ inversion_lemma_from_goal n na id Term.mk_Prop false half_inv_tac ]
END

VERNAC COMMAND EXTEND DeriveDependentInversion
| [ "Derive" "Dependent" "Inversion" ident(na) "with" constr(c) "Sort" sort(s) ]
  -> [ add_inversion_lemma_exn na c s true half_dinv_tac ]
    END

VERNAC COMMAND EXTEND DeriveDependentInversionClear
| [ "Derive" "Dependent" "Inversion_clear" ident(na) "with" constr(c) "Sort" sort(s) ]
  -> [ add_inversion_lemma_exn na c s true dinv_clear_tac ]
END

(* Subst *)

TACTIC EXTEND Subst
| [ "Subst" ne_ident_list(l) ] -> [ subst l ]
| [ "Subst" ] -> [ subst_all ]
END

