structure Ast = struct
open Region
open Operators
       
type id = string * region
type long_id = id option * id
                             
datatype idx = 
	 IVar of long_id
	 | INat of int * region
	 | ITime of string * region
         (* | UnOpI of idx_un_op * idx * region *)
	 | IBinOp of idx_bin_op * idx * idx * region
	 | ITT of region
         | IAbs of id list * idx * region
         | IDiv of idx * (int * region) * region

datatype prop =
	 PConst of string * region
         | PNot of prop * region
	 | PBinConn of bin_conn * prop * prop * region
	 | PBinPred of bin_pred * idx * idx * region

datatype bsort =
         BSId of id

datatype sort =
	 SBasic of bsort
	 | SSubset of bsort * id * prop * region
         | SBigO of string * bsort * idx * region

datatype quan =
	 Forall of unit

datatype abs = 
	 AbsFn of unit
	 | AbsRec of unit

type sort_bind = id * sort * region
type bsort_bind = id * bsort * region

fun sortings (ids, s, r) = map (fn id => (id, s, r)) ids
fun bsortings (ids, b, r) = map (fn id => (id, b, r)) ids

type id_or_bsort_bind = (id, bsort_bind) sum 
                               
type state = (id * idx) list
val empty_state = []

datatype ty =
	 TVar of long_id
	 | TArrow of (state * ty) * (idx * idx) * (state * ty) * region
	 | TProd of ty * ty * region
	 | TQuan of quan * sort_bind list * ty * region
	 | TAppT of ty * ty * region
	 | TAppI of ty * idx * region
	 | TAbs of id_or_bsort_bind list * ty * region

datatype ptrn =
	 PnConstr of (long_id * bool) * string list * ptrn option * region
         | PnTuple of ptrn list * region
         | PnAlias of id * ptrn * region
         | PnAnno of ptrn * ty * region

datatype bind =
	 BindTyping of ptrn
	 | BindSorting of sort_bind

type return = ty option * idx option * idx option

type constr_core = ty * ty option
type constr_decl = id * sort_bind list * constr_core option * region
type datatype_def = string * string list * bsort_bind list * bsort list * constr_decl list * region

datatype exp_const =
         ECInt of int
         | ECNat of int
         | ECString of string
         | ECChar of Char.char

datatype expr_tri_op =
         ETIte of unit
         | ETIfDec of unit

datatype visi =
         ViPublic
         | ViPrivate

datatype ast_expr_binop =
         EBTiML of expr_bin_op
         | EBStrConcat of unit
         | EBSetRef of unit

datatype ast_expr_triop =
         ETTiML of expr_tri_op
         | ETIfi of unit
                         
datatype exp = 
	 EVar of long_id * (bool * bool)
         | ETuple of exp list * region
         | EAbs of bind list * return * exp * region
         | EAppI of exp * idx * region
         | ECase of exp * return * (ptrn * exp) list * region
         | EAsc of exp * ty * region
         | EAscTime of exp * idx * region
         | EAscSpace of exp * idx * region
         | ELet of return * decl list * exp * region
         | EConst of exp_const * region
         | EUnOp of expr_un_op * exp * region
         | EBinOp of ast_expr_binop * exp * exp * region
         | ETriOp of ast_expr_triop * exp * exp * exp * region
         | ENever of region
         | ESetModify of bool(*is modify?*) * (id * exp list) * exp * region
         | EGet of (id * exp list) * region
         | EField of exp * id * region

     and decl =
         DVal of id list * ptrn * exp * region
         | DRec of id list * id * bind list * state * state option * return * exp * region
         | DDatatype of datatype_def
         | DIdxDef of id * sort option * idx
         | DAbsIdx2 of id * sort option * idx
         | DAbsIdx of id * sort option * idx option * decl list * region
         | DTypeDef of id * ty
         | DOpen of id
         | DState of id * ty

datatype spec =
         SpecVal of id * id list * ty * region
         | SpecDatatype of datatype_def
         | SpecIdx of id * sort
         | SpecType of id list * bsort list * region
         | SpecTypeDef of id * ty
                                   
datatype sgn =
         SigComponents of spec list * region

datatype mod =
         ModComponents of decl list * region
         | ModSeal of mod * sgn
         | ModTransparentAsc of mod * sgn
                                               
datatype top_bind =
         TBMod of id * mod
         | TBFunctor of id * (id * sgn) * mod
         | TBFunctorApp of id * id * id
         | TBState of id * ty
         | TBPragma of id * string
       | TBInterface of id * sgn

type prog = top_bind list

(* datatype sig_anno = *)
(*          Seal of sgn *)
(*          | Transparent of sgn *)

(* fun add_sig_anno m sg = *)
(*     case sg of *)
(*         NONE => m *)
(*       | SOME sg => *)
(*         case sg of *)
(*             Seal sg => ModSeal (m, sg) *)
(*           | Transparent sg => ModTransparentAsc (m, sg) *)

type reporter = string * pos * pos -> unit

fun get_region_long_id (m, (_, r)) =
    case m of
        NONE => r
      | SOME (_, r1) => combine_region r1 r

fun get_region_t t =
    case t of
        TVar x => get_region_long_id x
      | TArrow (_, _, _, r) => r
      | TProd (_, _, r) => r
      | TQuan (_, _, _, r) => r
      | TAppT (_, _, r) => r
      | TAppI (_, _, r) => r
      | TAbs (_, _, r) => r

fun get_region_pn pn =
    case pn of
        PnConstr (_, _, _, r) => r
      | PnTuple (_, r) => r
      | PnAlias (_, _, r) => r
      | PnAnno (_, _, r) => r

fun underscore r = (NONE, ("_", r))

fun chop_first_last s = String.extract (s, 1, SOME (String.size s - 2))

fun IUnOp (opr, i, r) = IBinOp (IBApp (), IVar (NONE, (str_idx_un_op opr, r)), i, r)

fun TPureArrow (t1, i, t2) = TArrow ((empty_state, t1), i, (empty_state, t2))
                               
fun ETriOp' (opr, e1, e2, e3, r) = ETriOp (ETTiML opr, e1, e2, e3, r)
fun EBinOp' (opr, e1, e2, r) = EBinOp (EBTiML opr, e1, e2, r)
fun EIte (e1, e2, e3, r) = ETriOp' (ETIte (), e1, e2, e3, r)
(* fun EIfDec (e1, e2, e3, r) = ETriOp (ETIfDec, e1, e2, e3, r) *)
fun EApp (e1, e2, r) = EBinOp' (EBApp (), e1, e2, r)
fun short_id id = ((NONE, id), false)
fun short_eid id = ((NONE, id), (false, false))
fun PnShortVar (x, r) = PnConstr (short_id (x, r), [], NONE, r)
(* fun EIte (e, e1, e2, r) = Case (e, (NONE, NONE), [(PShortVar ("true", r), e1), (PShortVar ("false", r), e2)], r) *)
fun EShortVar id = EVar (short_eid id)
fun ECons (e1, e2, r) = EApp (EShortVar ("Cons", r), ETuple ([e1, e2], r), r)
fun PnCons (pn1, pn2, r) = PnConstr (short_id ("Cons", r), [], SOME (PnTuple ([pn1, pn2], r)), r)
fun ENil r = EShortVar ("Nil", r)
fun EList (es, r) = foldr (fn (e, acc) => ECons (e, acc, r)) (ENil r) es
fun PnNil r = PnShortVar ("Nil", r)
fun PnList (pns, r) = foldr (fn (pn, acc) => PnCons (pn, acc, r)) (PnNil r) pns
fun ESemiColon (e1, e2, r) = ELet ((NONE, NONE, NONE), [DVal ([], PnShortVar ("_", r), e1, r)], e2, r)
fun EInc r =EShortVar ("inc", r)
fun EAdd r =EShortVar ("add", r)
fun ESubBy r =EShortVar ("subBy", r)
fun EAscTimeSpace (e, (i, j), r) = EAscSpace (EAscTime (e, i, r), j, r)
fun EIfi (e1, e2, e3, r) = ETriOp (ETIfi (), e1, e2, e3, r)
fun EStrConcat (e1, e2, r) = EBinOp (EBStrConcat (), e1, e2, r)
fun ESetRef (e1, e2, r) = EBinOp (EBSetRef (), e1, e2, r)
                               
end

