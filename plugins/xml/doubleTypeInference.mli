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

type types = { synthesized : Constr.types; expected : Constr.types option; }

val cprop : Names.Constant.t

val whd_betadeltaiotacprop :
  Environ.env -> Evd.evar_map -> EConstr.constr -> EConstr.constr

val double_type_of :
  Environ.env -> Evd.evar_map -> EConstr.constr -> EConstr.constr option ->
   types Acic.CicHash.t -> unit
