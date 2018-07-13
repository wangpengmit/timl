signature EXPR_PARAMS = sig
  type var
  type cvar
  type mod_id
  type idx
  type sort
  type mtype
  val get_constr_names : mtype -> Namespaces.name list
  type ptrn_constr_tag
  type ty
  type kind
end

functor ExprFn (Params : EXPR_PARAMS) = struct

open Params
open Unbound
open Namespaces
open Operators
open Region
open Binders

type ptrn = (cvar * ptrn_constr_tag, mtype) Pattern.ptrn

type return = mtype option * idx option * idx option
                                 
datatype stbind =
         SortingST of ibinder * sort outer
         | TypingST of ptrn

type scoping_ctx = ibinder list * tbinder list * cbinder list * ebinder list

type proj_path = (tuple_record_proj * region) list
                                                                        
datatype expr =
	 EVar of var * (bool(*explicit index arguments (EIA)*) * bool)
         | EConst of expr_const * region
         | EState of string * region
         | EUnOp of expr_un_op * expr * region
         | EBinOp of expr_bin_op * expr * expr
	 | ETriOp of expr_tri_op * expr * expr * expr
         | EEI of expr_EI * expr * idx
         | EET of expr_ET * expr * mtype
         | ET of expr_T * mtype * region
         | ERecord of expr SMap.map * region
         | ETuple of expr list
         | ENewArrayValues of mtype * expr list * region
	 | EAbs of idx StMap.map * (ptrn, expr) bind * (idx * idx) option
	 | EAbsI of (sort, expr) ibind_anno * region
	 | EAppConstr of (cvar * (bool * bool)) * mtype list * idx list * expr * (int * mtype) option
	 | ECase of expr * return * (ptrn, expr) bind list * region
         (* | ECaseSumbool of expr * expr ibind * expr ibind * region *)
         | EIfi of expr * expr ibind * expr ibind * region
	 | ELet of return * (decl tele, expr) bind * region
         | EGet of string * (expr * proj_path) list * Region.region
         | ESet of string * (expr * proj_path) list * expr * Region.region
         | EEnv of env_info * region

     and decl =
         DVal of ebinder * ((tbinder * (idx * idx) outer) list, expr) bind outer * region
         | DValPtrn of ptrn * expr outer * region
         | DRec of ebinder * ((tbinder * (idx * idx) outer) list * stbind tele rebind, (idx StMap.map * idx StMap.map) * (mtype * (idx * idx)) * expr) bind inner * region
         | DIdxDef of ibinder * sort option outer * idx outer
         | DAbsIdx2 of ibinder * sort outer * idx outer
         | DAbsIdx of (ibinder * sort outer * idx outer) * decl tele rebind * region
         | DTypeDef of tbinder * mtype outer
         | DOpen of mod_id inner * scoping_ctx option
         | DConstrDef of cbinder * cvar outer

type name = string * Region.region

datatype spec =
         SpecVal of name * ty
         | SpecIdx of name * sort
         | SpecType of name * kind
         | SpecTypeDef of name * mtype
                                   
type sgn = spec list * region
(* datatype sgn = *)
(*          SigComponents of spec list * region *)
(*          | SigVar of id *)
(*          | SigWhere of sgn * (id * mtype) *)

(* and sig_comp = *)
(*     ScSpec of name * spec * region *)
(* | ScModSpec of name * sgn *)
(* | Include of sgn *)

datatype mod =
         ModComponents of (* mod_comp *)decl list * region
         (* | ModProjectible of mod_id *)
         | ModSeal of mod * sgn
         | ModTransparentAsc of mod * sgn
(* | ModFunctorApp of id * mod (* list *) *)
                                               
(* and mod_comp = *)
(*     McDecl of decl *)
(* | McModBind of name * mod *)

datatype top_bind =
         TBMod of mod
         (* | TopSigBind of name * sgn *)
         (* | TopModSpec of name * sgn *)
         | TBFunctor of (name * sgn) (* list *) * mod
         | TBFunctorApp of mod_id * mod_id (* list *)
         | TBState of mtype
         | TBPragma of string

type prog = (name * top_bind) list

                              
(* type ptrn = (cvar * ptrn_constr_tag, mtype) Pattern.ptrn *)
                                            
(* type return = mtype option * idx option *)
                                 
(* datatype stbind =  *)
(*          SortingST of Binders.ibinder * sort Unbound.outer *)
(*          | TypingST of ptrn *)

(* type scoping_ctx = Binders.ibinder list * Binders.tbinder list * Binders.cbinder list * Binders.ebinder list *)
                                                                                                        
(* datatype expr = *)
(* 	 EVar of var * bool(*explicit index arguments (EIA)*) *)
(*          | EConst of Operators.expr_const * Region.region *)
(*          | EUnOp of Operators.expr_un_op * expr * Region.region *)
(*          | EBinOp of Operators.bin_op * expr * expr *)
(* 	 | ETriOp of Operators.tri_op * expr * expr * expr *)
(*          | EEI of Operators.expr_EI * expr * idx *)
(*          | EET of Operators.expr_ET * expr * mtype *)
(*          | ET of Operators.expr_T * mtype * Region.region *)
(* 	 | EAbs of (ptrn, expr) Unbound.bind *)
(* 	 | EAbsI of (sort, expr) Binders.ibind_anno * Region.region *)
(* 	 | EAppConstr of (cvar * bool) * mtype list * idx list * expr * (int * mtype) option *)
(* 	 | ECase of expr * return * (ptrn, expr) Unbound.bind list * Region.region *)
(* 	 | ELet of return * (decl Unbound.tele, expr) Unbound.bind * Region.region *)

(*      and decl = *)
(*          DVal of Binders.ebinder * (Binders.tbinder list, expr) Unbound.bind Unbound.outer * Region.region Unbound.outer *)
(*          | DValPtrn of ptrn * expr Unbound.outer * Region.region Unbound.outer *)
(*          | DRec of Binders.ebinder * (Binders.tbinder list * stbind Unbound.tele Unbound.rebind, (mtype * idx) * expr) Unbound.bind Unbound.inner * Region.region Unbound.outer *)
(*          | DIdxDef of Binders.ibinder * sort Unbound.outer * idx Unbound.outer *)
(*          | DAbsIdx2 of Binders.ibinder * sort Unbound.outer * idx Unbound.outer *)
(*          | DAbsIdx of (Binders.ibinder * sort Unbound.outer * idx Unbound.outer) * decl Unbound.tele Unbound.rebind * Region.region Unbound.outer *)
(*          | DTypeDef of Binders.tbinder * mtype Unbound.outer *)
(*          | DOpen of mod_id Unbound.outer * scoping_ctx option *)

(* type name = string * Region.region *)

(* datatype spec = *)
(*          SpecVal of name * ty *)
(*          | SpecIdx of name * sort *)
(*          | SpecType of name * kind *)
(*          | SpecTypeDef of name * mtype *)
                                   
(* type sgn = spec list * Region.region *)
(* (* datatype sgn = *) *)
(* (*          SigComponents of spec list * Region.region *) *)
(* (*          | SigVar of id *) *)
(* (*          | SigWhere of sgn * (id * mtype) *) *)

(* (* and sig_comp = *) *)
(* (*     ScSpec of name * spec * Region.region *) *)
(* (* | ScModSpec of name * sgn *) *)
(* (* | Include of sgn *) *)

(* datatype mod = *)
(*          ModComponents of (* mod_comp *)decl list * Region.region *)
(*          (* | ModProjectible of mod_id *) *)
(*          | ModSeal of mod * sgn *)
(*          | ModTransparentAsc of mod * sgn *)
(* (* | ModFunctorApp of id * mod (* list *) *) *)
                                        
(* (* and mod_comp = *) *)
(* (*     McDecl of decl *) *)
(* (* | McModBind of name * mod *) *)

(* datatype top_bind = *)
(*          TopModBind of mod *)
(*          (* | TopSigBind of name * sgn *) *)
(*          (* | TopModSpec of name * sgn *) *)
(*          | TopFunctorBind of (name * sgn) (* list *) * mod *)
(*          | TopFunctorApp of mod_id * mod_id (* list *) *)

(* type prog = (name * top_bind) list *)

end

functor TestExprFnSignatures (Params : EXPR_PARAMS) = struct
structure M : EXPR = ExprFn (Params)
end
                                                   
