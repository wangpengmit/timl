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
         | TRecord of (id * ty) list * region
         | TPtr of ty

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

datatype visi =
         ViPublic
         | ViPrivate
         | ViExternal
         | ViInternal

datatype expr_const =
         ECInt of string
         | ECNat of int
         | ECString of string
         | ECChar of Char.char
         | ECZero of unit
         | ECNow of unit
         | ECThis of unit

datatype ast_expr_unop =
         EUTiML of expr_un_op
         | EUDeref of bool(*is storage?*)
         | EUReturn of unit
         | EUThrow of unit
         | EUAsm of unit
         | EUCall of unit
         | EUSend of unit
         | EUAttach of unit
         | EUFire of unit
         | EUSHA3 of unit
         | EUSHA256 of unit
         | EUECREC of unit
                       
datatype ast_expr_binop =
         EBTiML of expr_bin_op
         | EBStrConcat of unit
         | EBSetRef of bool
         | EBWhile of unit

datatype ast_expr_triop =
         ETIte of unit
         (* | ETIfDec of unit *)
         | ETIfi of unit

datatype storage =
         StMemory
         | StStorage
         (* | StIndexed *)
                      
type proj_path = (tuple_record_proj * region) list
                                                
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
         | EConst of expr_const * region
         | EUnOp of ast_expr_unop * exp * region
         | EBinOp of ast_expr_binop * exp * exp * region
         | ETriOp of ast_expr_triop * exp * exp * exp * region
         | ENever of region
         | ESetModify of bool(*is modify?*) * id * (exp * proj_path) list * exp * region
         | EGet of id * (exp * proj_path) list * region
         | ERecord of (id * exp) list * region
         | ENewArrayValues of exp list * region
         | ESemis of exp list * region
         | ELet2 of storage option * ptrn * exp option * region
         | EIfs of ifelse list * region
         | EFor of id * ty option * exp * exp * exp * exp * region
         | EState of id
         | EOffsetProjs of exp * (exp, tuple_record_proj * region) sum list

     and decl =
         DVal of id list * ptrn * exp * region
         | DRec of id list * id * bind list * state * state option * return * exp * region
         | DDatatype of datatype_def
         | DIdxDef of id * sort option * idx
         | DAbsIdx2 of id * sort option * idx
         | DAbsIdx of id * sort option * idx option * decl list * region
         | DTypeDef of id * ty
         | DOpen of id
         | DState of id * ty * init option
         | DEvent of id * (ty * bool) list

     and ifelse =
         If of exp * exp * region
         | Elseif of exp * exp * region
         | Else of exp * region

     and fun_modifier =
         FmView
         | FmPure
         | FmPayable
         | FmConst
         | FmGuard of exp list
         | FmVisi of visi
         | FmPre of state
         | FmPost of state
             
     and init =
         InitExpr of exp * region
         | InitVector of exp list * region

type index_proj = (exp, tuple_record_proj * region) sum
type index_proj_path = index_proj list
                                      
datatype spec =
         SpecVal of id * id list * ty * region
         | SpecDatatype of datatype_def
         | SpecIdx of id * sort
         | SpecType of id list * bsort list * region
         | SpecTypeDef of id * ty
         | SpecFun of id * ty list * return
         | SpecEvent of id * (ty * bool) list
                                   
datatype sgn =
         SigComponents of spec list * region

datatype mod =
         ModComponents of id list * decl list * region
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
      | TRecord (_, r) => r

fun get_region_pn pn =
    case pn of
        PnConstr (_, _, _, r) => r
      | PnTuple (_, r) => r
      | PnAlias (_, _, r) => r
      | PnAnno (_, _, r) => r

fun underscore r = (NONE, ("_", r))

fun chop_first_last s = String.extract (s, 1, SOME (String.size s - 2))

fun IUnOp (opr, i, r) = IBinOp (IBApp (), IVar (NONE, (str_idx_un_op opr, r)), i, r)

fun TPureArrow (t1, i, t2, r) = TArrow ((empty_state, t1), i, (empty_state, t2), r)
fun TTuple (ts, r) = foldl_nonempty (fn (t, acc) => TProd (acc, t, r)) ts
                               
fun EUnOp' (opr, e, r) = EUnOp (EUTiML opr, e, r)
fun EBinOp' (opr, e1, e2, r) = EBinOp (EBTiML opr, e1, e2, r)
fun EIte (e1, e2, e3, r) = ETriOp (ETIte (), e1, e2, e3, r)
(* fun EIfDec (e1, e2, e3, r) = ETriOp (ETIfDec, e1, e2, e3, r) *)
fun EApp (e1, e2, r) = EBinOp' (EBApp (), e1, e2, r)
fun short_cid id = ((NONE, id), false)
fun short_eid id = ((NONE, id), (false, false))
fun PnShortVar (x, r) = PnConstr (short_cid (x, r), [], NONE, r)
(* fun EIte (e, e1, e2, r) = Case (e, (NONE, NONE), [(PShortVar ("true", r), e1), (PShortVar ("false", r), e2)], r) *)
fun EShortVar id = EVar (short_eid id)
fun ECons (e1, e2, r) = EApp (EShortVar ("Cons", r), ETuple ([e1, e2], r), r)
fun PnCons (pn1, pn2, r) = PnConstr (short_cid ("Cons", r), [], SOME (PnTuple ([pn1, pn2], r)), r)
fun ENil r = EShortVar ("Nil", r)
fun EList (es, r) = foldr (fn (e, acc) => ECons (e, acc, r)) (ENil r) es
fun PnNil r = PnShortVar ("Nil", r)
fun PnList (pns, r) = foldr (fn (pn, acc) => PnCons (pn, acc, r)) (PnNil r) pns
fun ESemiColon (e1, e2, r) = ELet ((NONE, NONE, NONE), [DVal ([], PnShortVar ("_", r), e1, r)], e2, r)
fun EInc r =EShortVar ("inc", r)
fun EDec r =EShortVar ("dec", r)
fun EAdd r =EShortVar ("addBy", r)
fun ESubBy r =EShortVar ("subBy", r)
fun EOrBy r =EShortVar ("orBy", r)
fun EAscTimeSpace (e, (i, j), r) = EAscSpace (EAscTime (e, i, r), j, r)
fun EIfi (e1, e2, e3, r) = ETriOp (ETIfi (), e1, e2, e3, r)
fun EStrConcat (e1, e2, r) = EBinOp (EBStrConcat (), e1, e2, r)
fun ESetRef (is_storage, e1, e2, r) = EBinOp (EBSetRef is_storage, e1, e2, r)
fun ESetMemRef (e1, e2, r) = ESetRef (false, e1, e2, r)
fun ESetStorageRef (e1, e2, r) = ESetRef (true, e1, e2, r)
fun EZero r = EConst (ECZero (), r)
fun ENow r = EConst (ECNow (), r)
fun EThis r = EConst (ECThis (), r)
fun EInt (n, r) = EConst (ECInt n, r)
fun ENat (n, r) = EConst (ECNat n, r)
fun EReturn (e, r) = EUnOp (EUReturn (), e, r)
fun EThrow (e, r) = EUnOp (EUThrow (), e, r)
fun EThrowError r = EThrow (EInt ("0x1234567890", r), r)                          
fun EAsm (e, r) = EUnOp (EUAsm (), e, r)
fun EField (e, id, r) = EUnOp' (EUField (fst id, NONE), e, r)
fun EWhile (e1, e2, r) = EBinOp (EBWhile (), e1, e2, r)
fun ESet (x, es, e, r) = ESetModify (false, x, es, e, r)
fun ETT r = ETuple ([], r)
fun EPushBack (e1, e2, r) = EApp (EShortVar ("push_back", r), ETuple ([e1, e2], r), r)
fun ECall (e, r) = EUnOp (EUCall (), e, r)
fun ESend (e, r) = EUnOp (EUSend (), e, r)
fun EFire (e, r) = EUnOp (EUFire (), e, r)
fun EAttach (e, r) = EUnOp (EUAttach (), e, r)
fun EDeref (b, e, r) = EUnOp (EUDeref b, e, r)
fun EMemDeref (e, r) = EDeref (false, e, r)
fun EStorageDeref (e, r) = EDeref (true, e, r)

type typing = id * ty
type indexed_typing = id * (ty * bool)

end

