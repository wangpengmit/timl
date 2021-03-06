signature EXPR = sig

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
         
  type ptrn = (cvar * ptrn_constr_tag, mtype) Pattern.ptrn
                                              
  type return = mtype option * idx option * idx option
                                   
  datatype stbind = 
           SortingST of Binders.ibinder * sort Unbound.outer
           | TypingST of ptrn

  type scoping_ctx = Binders.ibinder list * Binders.tbinder list * Binders.cbinder list * Binders.ebinder list

  type proj_path = (Operators.tuple_record_proj * Region.region) list
                                                
  datatype expr =
	   EVar of var * (bool(*explicit index arguments (EIA)*) * bool(*will have implicit index/type arguments *))
           | EConst of Operators.expr_const * Region.region
           | EState of string * Region.region
           | EUnOp of Operators.expr_un_op * expr * Region.region
           | EBinOp of Operators.expr_bin_op * expr * expr
	   | ETriOp of Operators.expr_tri_op * expr * expr * expr
           | EEI of Operators.expr_EI * expr * idx
           | EET of Operators.expr_ET * expr * mtype
           | ET of Operators.expr_T * mtype * Region.region
           | ERecord of expr SMap.map * Region.region
           | ETuple of expr list
           | ENewArrayValues of int * mtype * expr list * Region.region
	   | EAbs of idx StMap.map * (ptrn, expr) Unbound.bind * (idx * idx) option
	   | EAbsI of (sort, expr) Binders.ibind_anno * Region.region
	   | EAppConstr of (cvar * (bool * bool)) * mtype list * idx list * expr * (int * mtype) option
	   | ECase of expr * return * (ptrn, expr) Unbound.bind list * Region.region
           (* | ECaseSumbool of expr * expr Binders.ibind * expr Binders.ibind * Region.region *)
           | EIfi of expr * expr Binders.ibind * expr Binders.ibind * Region.region
	   | ELet of return * (decl Unbound.tele, expr) Unbound.bind * Region.region
           | EGet of string * (expr * proj_path) list * Region.region
           | ESet of string * (expr * proj_path) list * expr * Region.region
           | EEnv of Operators.env_info * Region.region
           | EAscState of expr * idx StMap.map
           | EDispatch of (string * expr * mtype option * mtype option) list * Region.region
           (* | EDebugLog of expr *)
           (* these constructs won't show up in source program *)
           (* | EAbsT of (sort, expr) tbind_anno * region *)

       and decl =
           DVal of Binders.ebinder * ((Binders.tbinder * (idx * idx) Unbound.outer) list, expr) Unbound.bind Unbound.outer * Region.region
           | DValPtrn of ptrn * expr Unbound.outer * Region.region
           | DRec of Binders.ebinder * ((Binders.tbinder * (idx * idx) Unbound.outer) list * stbind Unbound.tele Unbound.rebind, (idx StMap.map * idx StMap.map) * (mtype * (idx * idx)) * expr) Unbound.bind Unbound.inner * Region.region
           | DIdxDef of Binders.ibinder * sort option Unbound.outer * idx Unbound.outer
           | DAbsIdx2 of Binders.ibinder * sort Unbound.outer * idx Unbound.outer
           | DAbsIdx of (Binders.ibinder * sort Unbound.outer * idx Unbound.outer) * decl Unbound.tele Unbound.rebind * Region.region
           | DTypeDef of Binders.tbinder * mtype Unbound.outer
           | DOpen of mod_id Unbound.inner * scoping_ctx option
  (* these constructs won't show up in source program *)
           | DConstrDef of Binders.cbinder * cvar Unbound.outer
           (* | DBlock of decl Unbound.tele Unbound.rebind *)

  type name = string * Region.region

  datatype spec =
           SpecVal of name * ty
           | SpecIdx of name * sort
           | SpecType of name * kind
           | SpecTypeDef of name * mtype

  type sgn = spec list * Region.region
  (* datatype sgn = *)
  (*          SigComponents of spec list * Region.region *)
  (*          | SigVar of id *)
  (*          | SigWhere of sgn * (id * mtype) *)

  (* and sig_comp = *)
  (*     ScSpec of name * spec * Region.region *)
  (* | ScModSpec of name * sgn *)
  (* | Include of sgn *)

  datatype mod =
           ModComponents of decl list * Region.region
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

end
