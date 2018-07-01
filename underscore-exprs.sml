structure Underscore = struct
open Util
type 'bsort uvar_bs = unit
type ('bsort, 'idx) uvar_i = unit
type ('bsort, 'sort) uvar_s = unit
type ('sort, 'kind, 'mtype) uvar_mt = unit
fun eq_uvar_bs _ = false
fun eq_uvar_i _ = false
fun eq_uvar_s _ = false
fun eq_uvar_mt _ = false
fun map_uvar_bs _ = id
fun map_uvar_i _ = id
fun map_uvar_s _ = id
fun map_uvar_mt _ = id
fun str_uvar_bs _ _ = "_"
fun str_uvar_i _ _ = "_"
fun str_uvar_s _ _ = "_"
fun str_uvar_mt _ _ = "_"
fun pp_uvar_mt (str_s, str_k, pp_t, str) _ = str "_"
end

structure NamefulExpr = IdxTypeExprFn (type v = string
                                structure UVarI = Underscore
                                structure UVarT = Underscore
                                type ptrn_constr_tag = unit
                               )
                               
structure StringLongIdCanToString = struct

open LongId
open Gctx
       
fun str_raw_v x = x
fun str_raw_var a = str_raw_long_id str_raw_v a
                                    
fun str_v ctx x : string = x
                                    
fun lookup_module gctx m = (m, ([], [], [], []))
                
(* fun export_var sel gctx ctx id =  *)
(*   case id of *)
(*       ID (x, r) => ID (str_v ctx x, r) *)
(*     | QID ((m, r1), (x, r2)) => QID ((m, r1), (str_v ctx x, r2)) *)
    
fun str_var sel gctx ctx id = str_long_id (str_v ctx) id
    
end
                                   
structure NamefulCanToString = struct
open Underscore
open NamefulExpr
open StringLongIdCanToString
end
                       
structure NamefulToString = ToStringFn (structure Expr = NamefulExpr
                                        structure CanToString = NamefulCanToString
                                )
                                
structure NamefulToStringRaw = ToStringRawFn (structure Expr = NamefulExpr
                                              open NamefulCanToString
                                   )
                                
(* structure NamefulPrettyPrint0 = PrettyPrintFn *)
(*                                  (structure Expr = NamefulExpr *)
(*                                   structure CanToString = NamefulCanToString *)
(*                                   val str_ptrn_constr_tag = fn () => "" *)
(*                                  ) *)
                                
structure NamefulPrettyPrint = struct
structure PP = PPNamefulFn
                 (structure Expr = NamefulExpr
                  open Underscore
                  val str_var = LongId.str_long_id id
                  val str_cvar = LongId.str_long_id id
                  val str_mod_id = fst
                  val str_ptrn_constr_tag = fn () => ""
                 )
open NamefulToString
open PP
fun pp_prog_to_string e = pp_prog_to_string_fn (str_bs, str_i Gctx.empty [], str_s Gctx.empty [], str_k) e
end
                                
structure NamefulHasEqual = struct
open Underscore
open NamefulExpr
open LongIdHasEqual
fun eq_name ((s, _) : name, (s', _)) = s = s'
end
                       
structure NamefulEqual = EqualFn (structure IdxType = struct
                                  structure Idx = NamefulExpr.Idx
                                  structure Type = NamefulExpr.Type
                                  end
                                  structure HasEqual = NamefulHasEqual
                                  val str_raw_mt = NamefulToStringRaw.str_raw_mt
                                 )
                          
structure UnderscoredExpr = IdxTypeExprFn (type v = int
                                    structure UVarI = Underscore
                                    structure UVarT = Underscore
                                    type ptrn_constr_tag = unit
                                   )

structure UnderscoredCanToString = struct
open Underscore
open UnderscoredExpr
open IntLongIdCanToString
end
                       
structure UnderscoredToString = ToStringFn (structure Expr = UnderscoredExpr
                                            structure CanToString = UnderscoredCanToString
                                )
                                
structure UnderscoredPrettyPrint = PrettyPrintFn
                                 (structure Expr = UnderscoredExpr
                                  structure CanToString = UnderscoredCanToString
                                  val str_ptrn_constr_tag = fn () => ""
                                 )
                                
structure UnderscoredToStringRaw = ToStringRawFn (structure Expr = UnderscoredExpr
                                                  open UnderscoredCanToString
                                   )
                                
structure UnderscoredHasEqual = struct
open Underscore
open UnderscoredExpr
open LongIdHasEqual
fun eq_name ((s, _) : name, (s', _)) = s = s'
end
                       
structure UnderscoredEqual = EqualFn (structure IdxType = struct
                                      structure Idx = UnderscoredExpr.Idx
                                      structure Type = UnderscoredExpr.Type
                                      end
                                      structure HasEqual = UnderscoredHasEqual
                                      val str_raw_mt = UnderscoredToStringRaw.str_raw_mt
                          )
                          
structure UnderscoredSubst = SubstFn (structure IdxType = struct
                                      structure Idx = UnderscoredExpr.Idx
                                      structure Type = UnderscoredExpr.Type
                                      end
                                      structure SubstableVar = LongIdSubst
)
                          
structure UnderscoredExprVisitor = ExprVisitorFn (structure S = UnderscoredExpr
                                                  structure T = UnderscoredExpr)

structure UnderscoredSubst = SubstFn (structure IdxType = struct
                           structure Idx = UnderscoredExpr.Idx
                           structure Type = UnderscoredExpr.Type
                           end
                           structure SubstableVar = LongIdSubst
)
                          
structure UnderscoredExprShift = ExprShiftFn (structure Expr = UnderscoredExpr
                                              structure ShiftableVar = LongIdSubst
                                              open UnderscoredSubst
                                             )
                                                 
