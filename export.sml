functor ExportIdxFn (
  structure Params : IDX_VISITOR_PARAMS where type S.name = string * Region.region
                                          and type T.var = string
                                          and type 'a T.exists_anno = unit
  val str_var : (ToStringUtil.context -> string list) -> ToStringUtil.global_context -> string list -> Params.S.var -> string
  val map_uvar_bs : ('basic_sort -> 'basic_sort2) -> 'basic_sort Params.S.uvar_bs -> 'basic_sort2 Params.T.uvar_bs
  val map_uvar_i : ('basic_sort -> 'basic_sort2) * ('idx -> 'idx2) -> ('basic_sort, 'idx) Params.S.uvar_i -> ('basic_sort2, 'idx2) Params.T.uvar_i
  val map_uvar_s : ('basic_sort -> 'basic_sort2) * ('sort -> 'sort2) -> ('basic_sort, 'sort) Params.S.uvar_s -> ('basic_sort2, 'sort2) Params.T.uvar_s
) = struct

open Params
open Gctx
open List
open Util
open VisitorUtil
open Operators
       
structure IdxVisitor = IdxVisitorFn (Params)
(* open IdxVisitor *)
structure IV = IdxVisitor
                           
(******** the "export" visitor: convertnig de Bruijn indices to nameful terms **************)    
fun export_idx_visitor_vtable cast gctx (* : ((* 'this *)string list IV.idx_visitor, ToStringUtil.scontext) IV.idx_visitor_vtable *) =
  let
    fun extend this env name = (fst name :: env, name)
    fun visit_var this ctx x =
      str_var #1 gctx ctx x
    fun visit_uvar_bs this ctx u =
      let
        val vtable = cast this
      in
        map_uvar_bs (#visit_basic_sort vtable this []) u
      end
    fun visit_uvar_i this ctx (u, r) =
      let
        val vtable = cast this
        val u = map_uvar_i (#visit_basic_sort vtable this [], #visit_idx vtable this []) u
      in
        (u, r)
      end
    fun visit_uvar_s this ctx (u, r) =
      let
        val vtable = cast this
        val u = map_uvar_s (#visit_basic_sort vtable this [], #visit_sort vtable this []) u
      in
        (u, r)       
      end
  in
    IV.default_idx_visitor_vtable
      cast
      extend
      visit_var
      visit_uvar_bs
      visit_uvar_i
      visit_uvar_s
      (ignore_this_env strip_quan)
  end

fun new_export_idx_visitor a = IV.new_idx_visitor export_idx_visitor_vtable a
    
fun export_bs b =
  let
    val visitor as (IV.IdxVisitor vtable) = new_export_idx_visitor empty
  in
    #visit_basic_sort vtable visitor [] b
  end

fun export_i gctx ctx b =
  let
    val visitor as (IV.IdxVisitor vtable) = new_export_idx_visitor gctx
  in
    #visit_idx vtable visitor ctx b
  end

fun export_p gctx ctx b =
  let
    val visitor as (IV.IdxVisitor vtable) = new_export_idx_visitor gctx
  in
    #visit_prop vtable visitor ctx b
  end

fun export_s gctx ctx b =
  let
    val visitor as (IV.IdxVisitor vtable) = new_export_idx_visitor gctx
  in
    #visit_sort vtable visitor ctx b
  end

end

functor ExportTypeFn (
  structure Params : TYPE_VISITOR_PARAMS where type S.name = string * Region.region
                                           and type T.var = string
  val str_var : (ToStringUtil.context -> string list) -> ToStringUtil.global_context -> string list -> Params.S.var -> string
  val export_bs : Params.S.basic_sort -> Params.T.basic_sort
  val export_i : ToStringUtil.global_context -> string list -> Params.S.idx -> Params.T.idx
  val export_s : ToStringUtil.global_context -> string list -> Params.S.sort -> Params.T.sort
  val map_uvar_mt : ('basic_sort -> 'basic_sort2) * ('kind -> 'kind2) * ('mtype -> 'mtype2) -> ('basic_sort, 'kind, 'mtype) Params.S.uvar_mt -> ('basic_sort2, 'kind2, 'mtype2) Params.T.uvar_mt
) = struct

open Params
open Util
open VisitorUtil
       
structure TypeVisitor = TypeVisitorFn (Params)
structure TV = TypeVisitor
                           
fun export_k (n, sorts) = (n, map export_bs sorts)
  
fun export_type_visitor_vtable cast gctx (* : ((string list * string list) TV.type_visitor, string list * string list) TV.type_visitor_vtable *) =
  let
    fun extend_i this (sctx, kctx) name = ((fst name :: sctx, kctx), name)
    fun extend_t this (sctx, kctx) name = ((sctx, fst name :: kctx), name)
    fun visit_var this (sctx, kctx) x =
      str_var #2 gctx kctx x
    fun for_idx f this (sctx, kctx) data = f gctx sctx data
    fun visit_uvar_mt this ctx (u, r) =
      let
        val vtable = cast this
        val empty_ctx = ([], [])
        val u = 
            map_uvar_mt (#visit_basic_sort vtable this empty_ctx, #visit_kind vtable this empty_ctx, #visit_mtype vtable this empty_ctx) u
      in
        (u, r)
      end
  in
    TV.default_type_visitor_vtable
      cast
      extend_i
      extend_t
      visit_var
      (ignore_this_env export_bs)
      (for_idx export_i)
      (for_idx export_s)
      (ignore_this_env export_k)
      visit_uvar_mt
  end

fun new_export_type_visitor a = TV.new_type_visitor export_type_visitor_vtable a
    
fun export_mt gctx ctx b =
  let
    val visitor as (TV.TypeVisitor vtable) = new_export_type_visitor gctx
  in
    #visit_mtype vtable visitor ctx b
  end

fun export_t gctx ctx b =
  let
    val visitor as (TV.TypeVisitor vtable) = new_export_type_visitor gctx
  in
    #visit_ty vtable visitor ctx b
  end

end                           

functor ExportExprFn (
  structure Params : EXPR_VISITOR_PARAMS where type T.var = string
                                           and type T.cvar = string
                                           and type S.mod_id = string * Region.region
                                           and type T.mod_id = string
  sharing type Params.S.cvar = Params.S.var
  sharing type Params.T.ptrn_constr_tag = Params.S.ptrn_constr_tag
  val str_var : (ToStringUtil.context -> string list) -> ToStringUtil.global_context -> string list -> Params.S.var -> string
  val lookup_module : ToStringUtil.global_context -> string -> string * ToStringUtil.context
  val export_i : ToStringUtil.global_context -> string list -> Params.S.idx -> Params.T.idx
  val export_s : ToStringUtil.global_context -> string list -> Params.S.sort -> Params.T.sort
  val export_k : Params.S.kind -> Params.T.kind
  val export_mt : ToStringUtil.global_context -> string list * string list -> Params.S.mtype -> Params.T.mtype
  val export_t : ToStringUtil.global_context -> string list * string list -> Params.S.ty -> Params.T.ty
) = struct

open Binders
open Util
       
infixr 0 $
         
structure ToStringExprVisitor = ExprVisitorFn (Params)
structure EV = ToStringExprVisitor

fun export_expr_visitor_vtable cast gctx =
  let
    fun extend_i this (sctx, kctx, cctx, tctx) name = ((Name2str name :: sctx, kctx, cctx, tctx), name)
    fun extend_t this (sctx, kctx, cctx, tctx) name = ((sctx, Name2str name :: kctx, cctx, tctx), name)
    fun extend_c this (sctx, kctx, cctx, tctx) name = ((sctx, kctx, Name2str name :: cctx, tctx), name)
    fun extend_e this (sctx, kctx, cctx, tctx) name = ((sctx, kctx, cctx, Name2str name :: tctx), name)
    fun visit_cvar this (sctx, kctx, cctx, tctx) x =
      str_var #3 gctx cctx x
    fun visit_var this (sctx, kctx, cctx, tctx) x =
      str_var #4 gctx tctx x
    fun visit_mod_id this (sctx, kctx, cctx, tctx) (m, r) =
      fst $ lookup_module gctx m
    fun for_idx f this (sctx, kctx, cctx, tctx) data = f gctx sctx data
    fun for_type f this (sctx, kctx, cctx, tctx) data = f gctx (sctx, kctx) data
  in
    EV.default_expr_visitor_vtable
      cast
      extend_i
      extend_t
      extend_c
      extend_e
      visit_var
      visit_cvar
      visit_mod_id
      (for_idx export_i)
      (for_idx export_s)
      (for_type export_mt)
      (for_type export_t)
      (ignore_this_env export_k)
      visit_noop
  end

fun new_export_expr_visitor a = EV.new_expr_visitor export_expr_visitor_vtable a
    
fun export_e gctx ctx b =
  let
    val visitor as (EV.ExprVisitor vtable) = new_export_expr_visitor gctx
  in
    #visit_expr vtable visitor ctx b
  end

fun export_decl gctx env b =
  let
    val visitor = new_export_expr_visitor gctx
  in
    EV.visit_decl_acc visitor (b, env)
  end

fun export_decls gctx env b =
  let
    val visitor = new_export_expr_visitor gctx
  in
    EV.visit_decls_acc visitor (b, env)
  end

(* val empty_ctx = ([], [], [], []) *)
      
(* fun export_sig gctx decls = *)
(*   let *)
(*     val visitor as (EV.ExprVisitor vtable) = new_export_expr_visitor gctx *)
(*   in *)
(*     EV.visit_sgn_acc visitor (decls, empty_ctx) *)
(*   end *)
    
(* fun export_module gctx decls = *)
(*   let *)
(*     val visitor as (EV.ExprVisitor vtable) = new_export_expr_visitor gctx *)
(*   in *)
(*     EV.visit_mod_acc visitor (decls, empty_ctx) *)
(*   end *)

(* open Params *)
(* open T *)

(* fun export_top_bind gctx (name, bind) =  *)
(*     case bind of *)
(*         S.TBMod m => *)
(*         let *)
(*           val (m, ctx) = export_module gctx m *)
(*         in *)
(*           (TBMod m, [(name, Sig ctx)]) *)
(*         end *)
(*       (* | S.TopModSpec ((name, r), sg) => *) *)
(*       (*   let *) *)
(*       (*     val (sg = export_sig gctx sg *) *)
(*       (*     val () = open_module (name, sg) *) *)
(*       (*   in *) *)
(*       (*     [(name, Sig sg)] *) *)
(*       (*   end *) *)
(*       | S.TBFunctor (((arg_name, r2), arg), m) => *)
(*         let *)
(*           val (arg, arg_ctx) = export_sig gctx arg *)
(*           val gctx = Gctx.add (arg_name, Sig arg_ctx) gctx *)
(*           val (m, body_ctx) = export_module gctx m *)
(*         in *)
(*           (TBFunctor (((arg_name, r2), arg), m), [(name, FunctorBind ((arg_name, arg_ctx), body_ctx))]) *)
(*         end *)
(*       | S.TBFunctorApp ((f, f_r), m) => *)
(*         let *)
(*           fun is_FunctorBind s = *)
(*               case s of *)
(*                   FunctorBind a => SOME a *)
(*                 | _ => NONE *)
(*           fun lookup_functor (gctx : ns_sigcontext) m = *)
(*             opt_bind (Gctx.find (gctx, m)) is_FunctorBind *)
(*           fun fetch_functor gctx (m, r) = *)
(*               case lookup_functor gctx m of *)
(*                   SOME a => a *)
(*                 | NONE => raise Error (r, "Unbound functor " ^ m) *)
(*           val ((formal_arg_name, formal_arg), body) = fetch_functor gctx (f, f_r) *)
(*         in *)
(*           (TBFunctorApp ((f, f_r), m), [(name, Sig body), (formal_arg_name, Sig formal_arg)]) *)
(*         end *)
(*       | S.TBState (b, t) => *)
(*         let *)
(*           val () = add_ref st_ref name *)
(*         in *)
(*           (TBState (b, export_mtype Gctx.empty ([], []) t), []) *)
(*         end *)
(*       | S.TBPragma s => (TBPragma s, []) *)
          
(* and export_prog gctx binds = *)
(*     let *)
(*       fun iter (((name, r), bind), (binds, acc, gctx)) = *)
(*           let *)
(*             val (bind, gctxd) = export_top_bind gctx (name, bind) *)
(*           in *)
(*             (((name, r), bind) :: binds, gctxd @ acc, addList (gctx, gctxd)) *)
(*           end *)
(*       val (binds, gctxd, gctx) = foldl iter ([], [], gctx) binds *)
(*       val binds = rev binds *)
(*     in *)
(*       (binds, gctxd, gctx) *)
(*     end *)

end
