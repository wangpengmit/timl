signature CAN_TO_STRING = sig
  type var
  type idx
  include UVAR_I
  include UVAR_T
  val str_var : (ToStringUtil.context -> string list) -> ToStringUtil.global_context -> string list -> var -> string
  val lookup_module : ToStringUtil.global_context -> string -> string * ToStringUtil.context
  val map_uvar_bs : ('basic_sort -> 'basic_sort2) -> 'basic_sort uvar_bs -> 'basic_sort2 uvar_bs
  val map_uvar_i : ('basic_sort -> 'basic_sort2) * ('idx -> 'idx2) -> ('basic_sort, 'idx) uvar_i -> ('basic_sort2, 'idx2) uvar_i
  val map_uvar_s : ('basic_sort -> 'basic_sort2) * ('sort -> 'sort2) -> ('basic_sort, 'sort) uvar_s -> ('basic_sort2, 'sort2) uvar_s
  val map_uvar_mt : ('basic_sort -> 'basic_sort2) * ('kind -> 'kind2) * ('mtype -> 'mtype2) -> ('basic_sort, 'kind, 'mtype) uvar_mt -> ('basic_sort2, 'kind2, 'mtype2) uvar_mt
  val str_uvar_bs : ('a -> string) -> 'a uvar_bs -> string
  val str_uvar_i : ('basic_sort -> string) * ('idx -> string) -> ('basic_sort, 'idx) uvar_i -> string
  val str_uvar_s : ('sort -> string) -> ('basic_sort, 'sort) uvar_s -> string
  val str_uvar_mt : ('sort -> string) * ('kind -> string) * ('mtype -> string) -> ('sort, 'kind, 'mtype) uvar_mt -> string
  val pp_uvar_mt : ('sort -> string) * ('kind -> string) * ('mtype -> unit) * (string -> unit) -> ('sort, 'kind, 'mtype) uvar_mt -> unit
end

functor ToStringFn (structure Expr : IDX_TYPE_EXPR where type Idx.base_sort = BaseSorts.base_sort
                                               and type Type.base_type = BaseTypes.base_type
                                               and type Idx.region = Region.region
                                               and type Idx.name = string * Region.region
                                               and type Type.name = string * Region.region
                                               and type Type.region = Region.region
                                               and type mod_id = string * Region.region
                    structure CanToString : CAN_TO_STRING
                    sharing type Expr.Type.basic_sort = Expr.Idx.basic_sort
                    sharing type CanToString.var = Expr.var
                    sharing type CanToString.idx = Expr.Idx.idx
                    sharing type CanToString.uvar_bs = Expr.Idx.uvar_bs
                    sharing type CanToString.uvar_i = Expr.Idx.uvar_i
                    sharing type CanToString.uvar_s = Expr.Idx.uvar_s
                    sharing type CanToString.uvar_mt = Expr.Type.uvar_mt
                   ) = struct

open CanToString
open Expr
open Idx
open Type
open Gctx
open List
open Util
open BaseSorts
open BaseTypes
open Operators
open Pattern
open Region
structure IdxUtil = IdxUtilFn (Idx)
open IdxUtil
structure TypeUtil = TypeUtilFn (Type)
open TypeUtil
structure ExprUtil = ExprUtilFn (Expr)
open ExprUtil
open Bind

infixr 0 $

(* structure StringUVar = struct *)
(* type 'a uvar_bs = string *)
(* type ('a, 'b) uvar_i = string *)
(* type ('a, 'b) uvar_s = string *)
(* type ('a, 'b, 'c) uvar_mt = string *)
(* end *)
                         
structure StringUVar = struct
type 'a uvar_bs = 'a uvar_bs
type ('a, 'b) uvar_i = ('a, 'b) uvar_i
type ('a, 'b) uvar_s = ('a, 'b) uvar_s
type ('a, 'b, 'c) uvar_mt = ('a, 'b, 'c) uvar_mt
end
                         
structure NamefulIdx = IdxFn (structure UVarI = StringUVar
                             type base_sort = base_sort
                             type var = string
                             type name = name
                             type region = region
                             type 'idx exists_anno = unit
                            )
(* open NamefulIdx *)
(* structure T = NamefulIdx *)

structure NamefulType = TypeFn (structure Idx = NamefulIdx
                                structure UVarT = StringUVar
                                type base_type = base_type
                            )

structure NamefulTypeUtil = TypeUtilFn (NamefulType)
       
structure NamefulExpr = ExprFn (
  type var = string
  type cvar = string
  type mod_id = string
  type idx = NamefulIdx.idx
  type sort = NamefulIdx.sort
  type mtype = NamefulType.mtype
  val get_constr_names = NamefulTypeUtil.get_constr_names
  type ptrn_constr_tag = ptrn_constr_tag
  type ty = NamefulType.ty
  type kind = NamefulType.kind
)

structure ToStringNameful = ToStringNamefulFn (structure Expr = struct
                                               structure Idx = NamefulIdx
                                               structure Type = NamefulType
                                               open NamefulExpr
                                               end
                                               open CanToString
                                              )
structure SN = ToStringNameful
                                              
structure ExportIdx = ExportIdxFn (structure Params = struct
                                   structure S = Idx
                                   structure T = NamefulIdx
                                   end
                                   open CanToString
                                  )
open ExportIdx

fun str_bs b =
  let
    val b = export_bs b
  in
    SN.strn_bs b
  end
    
fun str_i gctx ctx b =
  let
    val b = export_i gctx ctx b
  in
    SN.strn_i b
  end
    
fun str_s gctx ctx b =
  let
    val b = export_s gctx ctx b
  in
    SN.strn_s b
  end
    
fun str_p gctx ctx b =
  let
    val b = export_p gctx ctx b
  in
    SN.strn_p b
  end
    
structure ExportType = ExportTypeFn (structure Params = struct
                                     structure S = Type
                                     structure T = NamefulType
                                     end
                                     open CanToString
                                     open ExportIdx
                                  )
open ExportType

fun str_k a = (SN.strn_k o export_k) a
    
fun str_mt gctx ctx b =
  let
    val b = export_mt gctx ctx b
  in
    SN.strn_mt b
  end
    
and str_t gctx ctx b =
  let
    val b = export_t gctx ctx b
  in
    SN.strn_t b
  end
    
structure ExportExpr = ExportExprFn (structure Params = struct
                                     structure S = Expr
                                     structure T = NamefulExpr
                                     end
                                     open CanToString
                                     open ExportIdx
                                     open ExportType
                                    )
open ExportExpr

fun str_e gctx ctx b =
  let
    val b = export_e gctx ctx b
  in
    SN.strn_e b
  end

fun str_decl gctx ctx b =
  let
    val (b, ctx) = export_decl gctx ctx b
  in
    (SN.strn_decl b, ctx)
  end

fun str_decls gctx ctx b =
  let
    val (b, ctx) = export_decls gctx ctx b
  in
    (map SN.strn_decl $ unTeles b, ctx)
  end

end
