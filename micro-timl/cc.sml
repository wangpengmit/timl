(* Closure Conversion *)

structure CC = struct

open Util
       
infixr 0 $
         
fun eq_fst ((x, _), (x', _)) = x = x'
                                     
fun free_vars_with_anno_0 f b =
  let
    val r = ref []
    fun output item = push_ref r item
    val _ = f output b
  in
    dedup eq_fst $ !r
  end

open Expr
open CompilerUtil
open MicroTiMLVisitor
open MicroTiMLExLongId
open MicroTiMLExLocallyNameless
open MicroTiMLExUtil
open MicroTiMLEx
       
fun free_ivars_with_anno_idx_visitor_vtable cast output =
  let
    fun visit_VarI this env (data as (var, sorts)) =
        let
          val sorts = visit_list (#visit_sort (cast this) this) env sorts
          val () = 
              case var of
                  QID (_, (x, _)) =>
                  (case sorts of
                       s :: _ => output (Free_i x, s)
                     | [] => raise Impossible $ "free_ivars_with_anno_i/VarI/QID/sorts=[]: " ^ str_int x
                  )
                | _ => ()
        in
          VarI data
        end
    val vtable = 
        default_idx_visitor_vtable
          cast
          extend_noop
          (visit_imposs "free_ivars_with_anno_i/visit_var")
          visit_noop
          visit_noop
          visit_noop
          visit_noop
    val vtable = override_visit_VarI vtable visit_VarI
  in
    vtable
  end

fun new_free_ivars_with_anno_idx_visitor a = new_idx_visitor free_ivars_with_anno_idx_visitor_vtable a
    
fun free_ivars_with_anno_i_fn output b =
  let
    val visitor as (IdxVisitor vtable) = new_free_ivars_with_anno_idx_visitor output
  in
    #visit_idx vtable visitor () b
  end
    
fun free_ivars_with_anno_s_fn output b =
  let
    val visitor as (IdxVisitor vtable) = new_free_ivars_with_anno_idx_visitor output
  in
    #visit_sort vtable visitor () b
  end
    
fun free_ivars_with_anno_ty_visitor_vtable cast (output, visit_i, visit_s) =
    default_ty_visitor_vtable
      cast
      extend_noop
      extend_noop
      visit_noop
      visit_noop
      (ignore_this_env $ visit_i output)
      (ignore_this_env $ visit_s output)
      
fun new_free_ivars_with_anno_ty_visitor params = new_ty_visitor free_ivars_with_anno_ty_visitor_vtable params
    
fun free_ivars_with_anno_t_fn output b =
  let
    val visitor as (TyVisitor vtable) = new_free_ivars_with_anno_ty_visitor (output, free_ivars_with_anno_i_fn, free_ivars_with_anno_s_fn)
  in
    #visit_ty vtable visitor () b
  end

fun free_ivars_with_anno_expr_visitor_vtable cast (output, visit_i, visit_s, visit_t) =
    default_expr_visitor_vtable
      cast
      extend_noop
      extend_noop
      extend_noop
      extend_noop
      visit_noop
      visit_noop
      (ignore_this_env $ visit_i output)
      (ignore_this_env $ visit_s output)
      (ignore_this_env $ visit_t output)

fun new_free_ivars_with_anno_expr_visitor params = new_expr_visitor free_ivars_with_anno_expr_visitor_vtable params
    
fun free_ivars_with_anno_e_fn output b =
  let
    val visitor as (ExprVisitor vtable) = new_free_ivars_with_anno_expr_visitor (output, free_ivars_with_anno_i_fn, free_ivars_with_anno_s_fn, free_ivars_with_anno_t_fn)
  in
    #visit_expr vtable visitor () b
  end

fun free_ivars_idx_visitor_vtable cast output =
  let
    fun visit_VarI this env (data as (var, sorts)) =
        let
          val () =
              case var of
                  QID (_, (x, _)) => output $ Free_i x
                | _ => ()
        in
          VarI data
        end
    val vtable = 
        default_idx_visitor_vtable
          cast
          extend_noop
          (visit_imposs "free_ivars_i/visit_var")
          visit_noop
          visit_noop
          visit_noop
          visit_noop
    val vtable = override_visit_VarI vtable visit_VarI
  in
    vtable
  end

fun new_free_ivars_idx_visitor a = new_idx_visitor free_ivars_idx_visitor_vtable a
    
fun free_ivars_s_fn output b =
  let
    val visitor as (IdxVisitor vtable) = new_free_ivars_idx_visitor output
  in
    #visit_sort vtable visitor () b
  end
    
fun free_vars_0 f b =
  let
    val r = ref []
    fun output item = push_ref r item
    val _ = f output b
  in
    dedup op= $ !r
  end

fun free_ivars_s a = free_vars_0 free_ivars_s_fn a
      
structure TopoSort = TopoSortFn (structure M = IntBinaryMap
                                 structure S = IntBinarySet
                                )
                                
fun free_ivars_with_anno_e e =
    let
      val vars_anno = free_vars_with_anno_0 free_ivars_with_anno_e_fn e
      val vars_anno = map (mapFst unFree_i) vars_anno
      fun free_ivars_s_set s = TopoSort.SU.to_set $ map unFree_i $ free_ivars_s s
      fun make_dep_graph vars_anno = TopoSort.MU.to_map $ map (mapSnd free_ivars_s_set)  vars_anno
      val in_graph = make_dep_graph vars_anno
      val var2anno = TopoSort.MU.to_map vars_anno
      val vars = TopoSort.topo_sort in_graph
                 handle
                 TopoSortFailed =>
                 let
                   val msg = sprintf "topo_sort failed on expr: $\n" [ExportPP.pp_e_to_string (NONE, NONE) $ ExportPP.export ([], [], [], []) e]
                   val msg = msg ^ sprintf "with dep graph: $\n" [str_ls (str_pair (str_int, str_ls str_int o TopoSort.SU.to_list)) $ IntBinaryMap.listItemsi in_graph]
                 in
                   raise Impossible msg
                 end
      fun attach_values m ks = map (fn k => (k, IntBinaryMap.find (m, k))) ks
      val vars_anno = map (mapSnd valOf) $ attach_values var2anno vars
      val vars_anno = map (mapFst Free_i) vars_anno
    in
      vars_anno
    end

fun free_tvars_with_anno_ty_visitor_vtable cast output (* : ('this, unit, 'var, 'bsort, 'idx, 'sort, 'var, 'bsort, 'idx, 'sort) ty_visitor_vtable *) =
  let
    fun visit_TVar this env (data as (var, ks)) =
        case var of
            QID (_, (x, _)) =>
            (case ks of
                 k :: _ => (output (Free_t x, k); TVar data)
               | [] => raise Impossible "free_tvars_with_anno_t/TVar/QID/ks=[]"
            )
          | _ => TVar data
    val vtable = 
        default_ty_visitor_vtable
          cast
          extend_noop
          extend_noop
          (visit_imposs "free_tvars_with_anno_t/visit_var")
          visit_noop
          visit_noop
          visit_noop
    val vtable = override_visit_TVar vtable visit_TVar
  in
    vtable
  end

fun new_free_tvars_with_anno_ty_visitor a = new_ty_visitor free_tvars_with_anno_ty_visitor_vtable a
    
fun free_tvars_with_anno_t_fn output b =
  let
    val visitor as (TyVisitor vtable) = new_free_tvars_with_anno_ty_visitor output
  in
    #visit_ty vtable visitor () b
  end
    
fun free_tvars_with_anno_t a = free_vars_with_anno_0 free_tvars_with_anno_t_fn a
      
fun free_tvars_with_anno_expr_visitor_vtable cast (output, visit_t) (* : ('this, int, 'var, 'idx, 'sort, 'kind, 'ty, 'var, 'idx, 'sort, 'kind, 'ty2) expr_visitor_vtable *) =
    default_expr_visitor_vtable
      cast
      extend_noop
      extend_noop
      extend_noop
      extend_noop
      visit_noop
      visit_noop
      visit_noop
      visit_noop
      (ignore_this_env $ visit_t output)

fun new_free_tvars_with_anno_expr_visitor params = new_expr_visitor free_tvars_with_anno_expr_visitor_vtable params
    
fun free_tvars_with_anno_e_fn output b =
  let
    val visitor as (ExprVisitor vtable) = new_free_tvars_with_anno_expr_visitor (output, free_tvars_with_anno_t_fn)
  in
    #visit_expr vtable visitor () b
  end

fun free_tvars_with_anno_e a = free_vars_with_anno_0 free_tvars_with_anno_e_fn a

val code_blocks = ref ([] : (free_e * string * (var, idx, sort, bsort kind, (var, bsort, idx, sort) ty) expr) list)
val code_labels = ref IntBinarySet.empty
fun add_code_block (decl as (x, _, _)) =
    (push_ref code_blocks decl;
     binop_ref (curry IntBinarySet.add) code_labels (unFree_e x)
    )
                      
fun free_evars_with_anno_expr_visitor_vtable cast (excluded, output) (* : ('this, unit, 'var, 'idx, 'sort, 'kind, 'ty, 'var, 'idx, 'sort, 'kind, 'ty) expr_visitor_vtable *) =
  let
    fun visit_EAscType this env (e, t) =
      let
        val (e_core, _) = collect_EAscTypeTime e
      in
        case e_core of
            EVar (QID (_, (x, _))) =>
            let
              val () =
                  if IntBinarySet.member (excluded, x) then ()
                  else output (Free_e x, t)
            in
              EAscType (e, t)
            end
          | _ => EAscType (#visit_expr (cast this) this env e, t)
      end
    fun visit_var this env var =
        case var of
            QID (_, (x, _)) =>
            if IntBinarySet.member (excluded, x) then var
            else 
              raise Impossible $ "free_evars_with_anno/visit_var/QID without EAscType: " ^ str_int x
          | _ => var
    val vtable = 
        default_expr_visitor_vtable
          cast
          extend_noop
          extend_noop
          extend_noop
          extend_noop
          visit_var
          visit_noop
          visit_noop
          visit_noop
          visit_noop
    val vtable = override_visit_EAscType vtable visit_EAscType
  in
    vtable
  end

fun new_free_evars_with_anno_expr_visitor params = new_expr_visitor free_evars_with_anno_expr_visitor_vtable params

fun free_evars_with_anno_fn excluded output b =
  let
    val visitor as (ExprVisitor vtable) = new_free_evars_with_anno_expr_visitor (excluded, output)
  in
    #visit_expr vtable visitor () b
  end

fun free_evars_with_anno excluded a = free_vars_with_anno_0 (free_evars_with_anno_fn excluded) a
      
fun IV (x, s) = VarI (make_Free_i x, [s])
fun TV (x, k) = TVar (make_Free_t x, [k])

fun TExists bind = TQuan (Exists (), bind)
                         
val ETT = EConst ECTT

fun ceil_half n = (n + 1) div 2

fun callcc (f : ('a -> unit) -> 'a) : 'a = Cont.callcc (fn k => f (fn v => Cont.throw k v))
                                
(* convert lists to Unsafe.Array to support random access *)
fun make_Record_k make_Prod make_Unit ls return =
    let
      val make_Record = make_Record make_Prod make_Unit
      val len = length ls
      val () = if len = 0 then return make_Unit else ()
      val () = if len = 1 then return $ hd ls else ()
      val len_fst_half = ceil_half len
      val fst_half = take len_fst_half ls
      val snd_half = drop len_fst_half ls
    in
      make_Prod (make_Record fst_half, make_Record snd_half)
    end

and make_Record make_Prod make_Unit ls = callcc $ make_Record_k make_Prod make_Unit ls

fun TRecord a = make_Record TProd TUnit a
fun ERecord a = make_Record EPair ETT a

fun ERecordProj_k (len, i) e return =
    let
      val () = if len = 0 then return ETT else ()
      val () = if len = 1 then return e else ()
      val len_fst_half = ceil_half len
    in
      if i < len_fst_half then
        ERecordProj (len_fst_half, i) $ EFst e
      else
        ERecordProj (len - len_fst_half, i - len_fst_half) $ ESnd e
    end

and ERecordProj (len, i) e = callcc $ ERecordProj_k (len, i) e
      
infixr 0 %$
fun a %$ b = EApp (a, b)

(* fun unBindSimpOpen_t bind = *)
(*     let *)
(*       val (name, b) = unBindSimpName bind *)
(*       val x = fresh_tvar () *)
(*       val b = open0_t_e x b *)
(*     in *)
(*       (x, name, b) *)
(*     end *)
                      
fun unBindSimpOpen_e bind =
    let
      val (name, b) = unBindSimpName bind
      val x = fresh_evar ()
      val b = open0_e_e x b
    in
      (x, name, b)
    end

fun cc_t t =
  case t of
      TArrow _ =>
      cc_t_arrow t
    | TQuan (Forall, _) =>
      cc_t_arrow t
    | TQuanI (Forall, _) =>
      cc_t_arrow t
    | TVar _ => t
    | TConst _ => t
    | TBinOp (opr, t1, t2) => TBinOp (opr, cc_t t1, cc_t t2)
    | TQuan (q, bind) =>
      let
        val (k, (name, t)) = unBindAnnoName bind
        val a = fresh_tvar ()
        val t = open0_t_t a t
        val t = cc_t t
      in
        TQuan (q, close0_t_t_anno ((a, fst name, k), t))
      end
    | TQuanI (q, bind) =>
      let
        val (s, (name, t)) = unBindAnnoName bind
        val a = fresh_ivar ()
        val t = open0_i_t a t
        val t = cc_t t
      in
        TQuanI (q, close0_i_t_anno ((a, fst name, s), t))
      end
    | TRec bind =>
      let
        val (k, (name, t)) = unBindAnnoName bind
        val a = fresh_tvar ()
        val t = open0_t_t a t
        val t = cc_t t
      in
        TRec $ close0_t_t_anno ((a, fst name, k), t)
      end
    | TAbsT bind =>
      let
        val (k, (name, t)) = unBindAnnoName bind
        val a = fresh_tvar ()
        val t = open0_t_t a t
        val t = cc_t t
      in
        TAbsT $ close0_t_t_anno ((a, fst name, k), t)
      end
    | TAbsI bind =>
      let
        val (s, (name, t)) = unBindAnnoName bind
        val a = fresh_ivar ()
        val t = open0_i_t a t
        val t = cc_t t
      in
        TAbsI $ close0_i_t_anno ((a, fst name, s), t)
      end
    | TNat _ => t
    | TAppT (t, t') => TAppT (cc_t t, cc_t t')
    | TAppI (t, i) => TAppI (cc_t t, i)
    | TArr (t, i) => TArr (cc_t t, i)
    | TProdEx _ =>
      let
        val s = (* substr 0 100 $  *)ExportPP.pp_t_to_string NONE $ ExportPP.export_t ([], []) t
      in
        raise Unimpl $ "cc_t() on: " ^ s
      end

and cc_t_arrow t =
    let
      val (binds, t) = open_collect_TForallIT t
      val (t1, i, t2) = assert_TArrow t
      val t1 = cc_t t1
      val t2 = cc_t t2
      val alpha = fresh_tvar ()
      val t = TArrow (TProd (TV (alpha, KType), t1), i, t2)
      val t = close_TForallITs (binds, t)
      val t = TProd (t, TV (alpha, KType))
      val t = TExists $ close0_t_t_anno ((alpha, "'a", KType), t)
    in
      t
    end

fun cc_expr_un_op opr =
    case opr of
        EUProj _ => opr
      | EUInj (inj, t) => EUInj (inj, cc_t t)
      | EUFold t => EUFold $ cc_t t
      | EUUnfold => opr

fun collect_TForallIT b =
  case b of
      TQuanI (Forall, bind) =>
      let
        val (s, (name, b)) = unBindAnnoName bind
        val (binds, b) = collect_TForallIT b
      in
        (inl (name, s) :: binds, b)
      end
    | TQuan (Forall, bind) =>
      let
        val (k, (name, b)) = unBindAnnoName bind
        val (binds, b) = collect_TForallIT b
      in
        (inr (name, k) :: binds, b)
      end
    | _ => ([], b)

fun apply_TForallIT b args =
    case (b, args) of
        (TQuanI (Forall, bind), inl v :: args) =>
        let
          val (_, (_, b)) = unBindAnnoName bind
        in
          apply_TForallIT (subst0_i_t v b) args
        end
      | (TQuan (Forall, bind), inr v :: args) =>
        let
          val (_, (_, b)) = unBindAnnoName bind
        in
          apply_TForallIT (subst0_t_t v b) args
        end
      | (_, []) => b
      | _ => raise Impossible "apply_TForallIT"

fun cc e =
  let
    (* val () = print $ "cc() started: " *)
    (* val e_str = (* substr 0 400 $  *)ExportPP.pp_e_to_string (SOME 2, SOME 1) $ ExportPP.export ([], [], [], []) e *)
    (* val () = println $ e_str *)
    val e =
    case e of
        EBinOp (EBApp, e1, e2) =>
        let
          val () = println "cc() on EApp"
          val (e1, itargs) = collect_EAppIT e1
          (* val (e1, t_e1) = assert_EAscType e1 *)
          (* val t_e1 = cc_t t_e1 *)
          (* val (_, t_pair) = assert_TExists t_e1 *)
          (* val (t_code, _) = assert_TProd t_pair *)
          val gamma = fresh_tvar ()
          val z = fresh_evar ()
          val z_code = fresh_evar ()
          val z_env = fresh_evar ()
          val e = EAppITs (EV z_code, map (map_inr cc_t) itargs) %$ EPair (EV z_env, cc e2)
          val () = println $ "cc()/EApp: before ELetManyClose()"
          val e = ELetManyClose ([(z_code, "z_code", EFst $ EV z), (z_env, "z_env", ESnd $ EV z)], e)
          val () = println $ "cc()/EApp: after ELetManyClose()"
          val e = EUnpackClose (cc e1, (gamma, "'c"), (z, "z"), e)
          val () = println "cc() done on EApp"
        in
          e
        end
      | EAbsT _ => cc_abs e
      | EAbsI _ => cc_abs e
      | EAbs _ => cc_abs e
      | ERec _ => cc_abs e
      | EBinOp (opr, e1, e2) => EBinOp (opr, cc e1, cc e2)
      | ELet (e1, bind) =>
        let
          val e1 = cc e1
          val (x, name, e2) = unBindSimpOpen_e bind
          val e2 = cc e2
        in
          ELetClose ((x, fst name, e1), e2)
        end
      | ECase (e, bind1, bind2) =>
        let
          val e = cc e
          val (x1, name1, e1) = unBindSimpOpen_e bind1
          val (x2, name2, e2) = unBindSimpOpen_e bind2
        in
          ECaseClose (e, ((x1, fst name1), cc e1), ((x2, fst name2), cc e2))
        end
      | EPack (tp, t, e) => EPack (cc_t tp, cc_t t, cc e)
      | EUnpack (e1, bind) =>
        let
          val e1 = cc e1
          val (name_a, bind) = unBindSimpName bind
          val (name_x, e2) = unBindSimpName bind
          val a = fresh_tvar ()
          val x = fresh_evar ()
          val e2 = open0_t_e a e2
          val e2 = open0_e_e x e2
          val e2 = cc e2
        in
          EUnpackClose (e1, (a, fst name_a), (x, fst name_x), e2)
        end
      | EPackI (tp, i, e) => EPackI (cc_t tp, i, cc e)
      | EUnpackI (e1, bind) =>
        let
          val () = println "before cc()/EUnpackI/cc#1"
          val e1 = cc e1
          val () = println "after cc()/EUnpackI/cc#1"
          val (name_a, bind) = unBindSimpName bind
          val (name_x, e2) = unBindSimpName bind
          val a = fresh_ivar ()
          val x = fresh_evar ()
          val () = println "before cc()/EUnpackI/open0_i_e()"
          (* this could be slow *)
          val e2 = open0_i_e a e2
          val () = println "after cc()/EUnpackI/open0_i_e()"
          val e2 = open0_e_e x e2
          val () = println "before cc()/EUnpackI/cc#2"
          val e2 = cc e2
          val () = println "after cc()/EUnpackI/cc#2"
          val e = EUnpackIClose (e1, (a, fst name_a), (x, fst name_x), e2)
          val () = println "done cc()/EUnpackI"
        in
          e
        end
      | EVar _ => e
      | EConst _ => e
      | EUnOp (opr, e) => EUnOp (cc_expr_un_op opr, cc e)
      | EAscType (e, t) => EAscType (cc e, cc_t t)
      | EAscTime (e, i) => EAscTime (cc e, i)
      | ENever t => ENever (cc_t t)
      | EBuiltin t => EBuiltin (cc_t t)
      | EWrite (e1, e2, e3) => EWrite (cc e1, cc e2, cc e3)
      | EHalt e => EHalt (cc e)
      | _ => raise Unimpl $ "cc(): " ^ (ExportPP.pp_e_to_string (NONE, NONE) $ ExportPP.export ([], [], [], []) e)
    (* val () = println $ "cc() finished: " ^ e_str *)
  in
    e
  end

and cc_abs e_all =
    let
      val () = println $ "cc_abs(): before open_collect_EAbsIT()"
      val (binds, e) = open_collect_EAbsIT e_all
      val () = println $ "cc_abs(): after open_collect_EAbsIT()"
    in
      case e of
          ERec bind => cc_ERec (* e_all *) binds bind
        (* | EAbs bind => cc_EAbs e_all binds bind *)
        | _ => raise Impossible "cc_abs"
    end

and cc_ERec (* e_all *) outer_binds bind =
    let
      val (t_x, (name_x, e)) = unBindAnnoName bind
      val () = println $ "cc() on: " ^ fst name_x
      val x = fresh_evar ()
      val e = open0_e_e x e
      val () = println $ "cc(): before open_collect_EAbsIT()"
      val (inner_binds, e) = open_collect_EAbsIT e
      val () = println $ "cc(): after open_collect_EAbsIT()"
      val (t_z, (name_z, e)) = assert_EAbs e
      val z = fresh_evar ()
      val e = open0_e_e z e
      val e = cc e
      val () = println $ "cc() really on: " ^ fst name_x
      val () = println $ "cc(): before collect_TForallIT_open_with()"
      val (_, t_arrow) = collect_TForallIT_open_with inner_binds t_x
      val () = println $ "cc(): after collect_TForallIT_open_with()"
      val (_, i, _) = assert_TArrow t_arrow
      val () = println $ "cc(): before getting free vars"
      val excluded = IntBinarySet.addList (!code_labels, map unFree_e [x, z])
      val ys_anno = free_evars_with_anno excluded e
      val (ys, sigmas) = unzip $ ys_anno
      fun add_name prefix (i, (a, b)) = (a, prefix ^ str_int (1+i), b)
      (* val () = println "before free_ivars" *)
      val free_ivars = mapi (add_name "a") $ free_ivars_with_anno_e e
      (* val () = println "after free_ivars" *)
      val free_tvars = mapi (add_name "'a") $ free_tvars_with_anno_e e
      val outer_inner_binds = outer_binds @ inner_binds
      fun eq_bind xx' =
          case xx' of
              (inl (x, _, _), inl (x', _, _)) => x = x'
            | (inr (x, _, _), inr (x', _, _)) => x = x'
            | _ => false
      val betas = map inl free_ivars @ map inr free_tvars
      val betas = diff eq_bind betas outer_inner_binds
      val () = println $ "cc(): after getting free vars"
      val t_env = TRecord sigmas
      val t_z = cc_t t_z
      val t_arrow = TArrow (TProd (t_env, t_z), i, TUnit)
      val z_code = fresh_evar ()
      val z_env = fresh_evar ()
      fun EAppITs_binds (e, binds) =
          let
            (* fun proj_3_1 (a1, _, _) = a1 *)
            fun make_var f (x, _, anno) = f (x, anno)
          in
            EAppITs (e, map (map_inl_inr (make_var IV) (make_var TV)) binds)
          end
      val def_x = EPack (cc_t t_x, t_env, EPair (EAppITs_binds (EV z_code, betas @ outer_binds), EV z_env))
      val len_ys = length ys
      val ys_defs = mapi (fn (i, y) => (y, "y" ^ str_int (1+i), ERecordProj (len_ys, i) $ EV z_env)) ys
      val () = println $ "cc(): before ELetManyClose()"
      val e = ELetManyClose ((x, fst name_x, def_x) :: ys_defs, e)
      val () = println $ "cc(): after ELetManyClose()"
      val e = EAbsPairClose ((z_env, "z_env", t_env), (z, fst name_z, t_z), e)
      val betas_outer_inner_binds = betas @ outer_inner_binds
      val () = println $ "cc(): before close_EAbsITs()"
      val e = close_EAbsITs (betas_outer_inner_binds, e)
      val () = println $ "cc(): after close_EAbsITs()"
      val () = println $ "cc(): before close_TForallITs()"
      val t_rawcode = close_TForallITs (betas_outer_inner_binds, t_arrow)
      val () = println $ "cc(): after close_TForallITs()"
      (* val t_code = TForallITClose (inner_binds, t_arrow) *)
      val v_code = ERec $ close0_e_e_anno ((z_code, fst name_x ^ "_code", t_rawcode), e)
      fun EV_anno (y, anno) = EAscType (EV y, anno)
      val v_env = ERecord $ map EV_anno ys_anno
      val x_code = fresh_evar ()
      val () = println $ "cc(): before close_TForallITs()#2"
      val e = EPack (cc_t $ close_TForallITs (outer_binds, t_x), t_env, EPair (EAppITs_binds (EV x_code(* v_code *), betas), v_env))
      val () = println $ "cc(): after close_TForallITs()#2"
      val x_v_code = (x_code, fst name_x ^ "_code", v_code)
      val () = add_code_block x_v_code
      (* val e = ELetClose (x_v_code, e) *)
      val () = println $ "cc() done on: " ^ fst name_x
    in
      e
    end

(* and cc_EAbs e_all outer_binds bind = *)
(*     let *)
(*       val (t_z, (name_z, e)) = unBindAnnoName bind *)
(*       val z = fresh_evar () *)
(*       val e = open0_e_e z e *)
(*       val (e, i) = assert_EAscTime e *)
(*       val t_e_all = TForallIT (outer_binds, TArrow (t_z, i, TUnit)) *)
(*       val (ys, sigmas) = unzip $ free_vars_with_anno e_all *)
(*       val betas = free_tvars e_all *)
(*       val t_env = cc_t $ TRecord sigmas *)
(*       val t_z = cc_t t_z *)
(*       val t_arrow = TArrow (TProd (t_env, t_z), i, TUnit) *)
(*       (* val t_rawcode = TForallITClose (betas @ outer_binds, t_arrow) *) *)
(*       (* val t_code = TForallITClose (outer_binds, t_arrow) *) *)
(*       val z_env = fresh_evar () *)
(*       val len_ys = length ys *)
(*       val ys_defs = mapi (fn (i, y) => (y, "y" ^ str_int (1+i), ERecordProj (len_ys, i) $ EV z_env)) ys *)
(*       val e = ELetManyClose (ys_defs, cc e) *)
(*       val e = EAbsPairClose ((z_env, "z_env", t_env), (z, name_z, t_z), e) *)
(*       val v_code = EAbsITClose (betas @ outer_binds, e) *)
(*       val v_env = ERecord ys *)
(*       val e = EPack (cc_t $ t_e_all, t_env, EPair (EAppITs (v_code, betas), v_env)) *)
(*     in *)
(*       e *)
(*     end *)

(* fun free_itvars_with_anno_e e = *)
(*     let *)
(*     in *)
(*     end *)

val cc =
 fn e =>
    let
      val e = convert_EAbs_to_ERec e
      val () = code_blocks := []
      val () = code_labels := IntBinarySet.empty
      val e = cc e
      val decls = rev $ !code_blocks
      val e = ELetManyClose (decls, e)
    in
      e
    end

val cc_tc_flags =
    let
      open MicroTiMLTypecheck
    in
      [AnnoEAbs, AnnoEVar]
    end
                     
val forget_var = Subst.forget_var
val forget_i_i = Subst.forget_i_i
val forget_i_s = Subst.forget_i_s
fun forget_i_t a = shift_i_t_fn (forget_i_i, forget_i_s) a
fun forget_t_t a = shift_t_t_fn forget_var a
fun forget_i_e a = shift_i_e_fn (forget_i_i, forget_i_s, forget_i_t) a
fun forget_t_e a = shift_t_e_fn (forget_t_t) a
fun forget_e_e a = shift_e_e_fn forget_var a
                               
fun check_ERec_closed_expr_visitor_vtable cast output =
  let
    val vtable = 
        default_expr_visitor_vtable
          cast
          extend_noop
          extend_noop
          extend_noop
          extend_noop
          visit_noop
          visit_noop
          visit_noop
          visit_noop
          visit_noop
    fun visit_ERec this env bind =
        let
          (* call super *)
          val e = #visit_ERec vtable this env bind
          val (_, (name, _)) = unBindAnnoName bind
          val name = fst name
          val () =
              let
                val large = 1000000000
                val _ = forget_i_e 0 large e
                val _ = forget_t_e 0 large e
                val _ = forget_e_e 0 large e
              in
                (* println $ name ^ " is closed" *)
                ()
              end
              handle _ =>
                     (* println $ name ^ " is open" *)
                     output name
        in
          e
        end
    val vtable = override_visit_ERec vtable visit_ERec
  in
    vtable
  end

fun new_check_ERec_closed_expr_visitor params = new_expr_visitor check_ERec_closed_expr_visitor_vtable params

fun check_ERec_closed b =
    let
      val r = ref []
      fun output item = push_ref r item
      val visitor as (ExprVisitor vtable) = new_check_ERec_closed_expr_visitor output
      val _ = #visit_expr vtable visitor () b
      val opens = !r
    in
      if not $ null opens then
        raise Impossible $ "These ERec's are not closed: " ^ str_ls id opens
      else ()
    end

structure UnitTest = struct

structure TestUtil = struct

open CPS
open LongId
open Util
open MicroTiML
open MicroTiMLVisitor
open MicroTiMLExLongId
open MicroTiMLEx
       
infixr 0 $
infixr 0 !!
         
fun short_to_long_id x = ID (x, dummy)
fun export_var (sel : 'ctx -> string list) (ctx : 'ctx) id =
  let
    fun unbound s = "__unbound_" ^ s
    (* fun unbound s = raise Impossible $ "Unbound identifier: " ^ s *)
  in
    case id of
        ID (x, _) =>
        short_to_long_id $ nth_error (sel ctx) x !! (fn () => unbound $ str_int x)
        (* short_to_long_id $ str_int x *)
      | QID _ => short_to_long_id $ unbound $ CanToString.str_raw_var id
  end
(* val export_i = return2 *)
fun export_i a = ToString.export_i Gctx.empty a
fun export_s a = ToString.export_s Gctx.empty a
fun export_t a = export_t_fn (export_var snd, export_i, export_s) a
fun export a = export_e_fn (export_var #4, export_var #3, export_i, export_s, export_t) a
val str = PP.string
fun str_var x = LongId.str_raw_long_id id(*str_int*) x
fun str_i a =
  (* ToStringRaw.str_raw_i a *)
  ToString.SN.strn_i a
  (* const_fun "<idx>" a *)
fun str_bs a =
  ToStringRaw.str_raw_bs a
fun str_s a =
  (* ToStringRaw.str_raw_s a *)
  ToString.SN.strn_s a
  (* const_fun "<sort>" a *)
fun pp_t_to s b =
  MicroTiMLPP.pp_t_to_fn (str_var, str_bs, str_i, str_s, const_fun "<kind>") s b
  (* str s "<ty>" *)
fun pp_t b = MicroTiMLPP.pp_t_fn (str_var, str_bs, str_i, str_s, const_fun "<kind>") b
fun pp_e a = MicroTiMLExPP.pp_e_fn (
    str_var,
    str_i,
    str_s,
    const_fun "<kind>",
    pp_t_to
  ) a
fun fail () = OS.Process.exit OS.Process.failure
                   
end

open TestUtil
       
fun test1 dirname =
  let
    val () = println "CC.UnitTest started"
    val filename = join_dir_file (dirname, "cc-test1.pkg")
    val filenames = ParseFilename.expand_pkg (fn msg => raise Impossible msg) filename
    open Parser
    val prog = concatMap parse_file filenames
    open Elaborate
    val prog = elaborate_prog prog
    open NameResolve
    val (prog, _, _) = resolve_prog empty prog
                                    
    open TypeCheck
    val () = TypeCheck.turn_on_builtin ()
    val () = println "Started TiML typechecking ..."
    val ((prog, _, _), (vcs, admits)) = typecheck_prog empty prog
    val vcs = VCSolver.vc_solver filename vcs
    val () = if null vcs then ()
             else
               raise curry TypeCheck.Error dummy $ (* str_error "Error" filename dummy *) [sprintf "Typecheck Error: $ Unproved obligations:" [str_int $ length vcs], ""] @ (
               (* concatMap (fn vc => str_vc true filename vc @ [""]) $ map fst vcs *)
               concatMap (VCSolver.print_unsat true filename) vcs
             )
    val () = println "Finished TiML typechecking"
                     
    open MergeModules
    val decls = merge_prog prog []
    open TiML2MicroTiML
    val e = SMakeELet (Teles decls, Expr.ETT dummy)
    val () = println "Simplifying ..."
    val e = SimpExpr.simp_e [] e
    val () = println "Finished simplifying"
    (* val () = println $ str_e empty ToStringUtil.empty_ctx e *)
    (* val () = println "" *)
    val () = println "Started translating ..."
    val e = trans_e e
    val () = println "Finished translating"
    (* val () = pp_e $ export ToStringUtil.empty_ctx e *)
    (* val () = println "" *)
                     
    open MicroTiMLTypecheck
    open TestUtil
    val () = println "Started MicroTiML typechecking #1 ..."
    val ((e, t, i), vcs, admits) = typecheck cps_tc_flags ([], [], [](* , HeapMap.empty *)) e
    val () = println "Finished MicroTiML typechecking #1"
    val () = println "Type:"
    val () = pp_t NONE $ export_t ([], []) t
    val () = println "Time:"
    val i = simp_i i
    val () = println $ ToString.str_i Gctx.empty [] i
    (* val () = println $ "#VCs: " ^ str_int (length vcs) *)
    (* val () = println "VCs:" *)
    (* val () = app println $ concatMap (fn ls => ls @ [""]) $ map (str_vc false "") vcs *)
    (* val () = pp_e $ export ToStringUtil.empty_ctx e *)
    (* val () = println "" *)
                     
    val () = println "Started CPS conversion ..."
    val (e, _) = cps (e, TUnit) (EHaltFun TUnit, T_0)
    (* val (e, _) = cps (e, TUnit) (Eid TUnit, T_0) *)
    val () = println "Finished CPS conversion"
    (* val () = pp_e $ export ToStringUtil.empty_ctx e *)
    (* val () = println "" *)
    val e_str = ExportPP.pp_e_to_string (NONE, NONE) $ export ToStringUtil.empty_ctx e
    val () = write_file ("cc-unit-test-after-cps.tmp", e_str)
    val () = println "Started MicroTiML typechecking #2 ..."
    val ((e, t, i), vcs, admits) = typecheck cc_tc_flags ([], [], [](* , HeapMap.empty *)) e
    val () = println "Finished MicroTiML typechecking #2"
    val () = println "Type:"
    val () = pp_t NONE $ export_t ([], []) t
    val () = println "Time:"
    val i = simp_i i
    val () = println $ ToString.str_i Gctx.empty [] i
    val () = pp_e (NONE, NONE) $ export ToStringUtil.empty_ctx e
    val () = println ""
                     
    val () = println "Started CC ..."
    val e = cc e
    val () = println "Finished CC"
    (* val () = pp_e $ export ToStringUtil.empty_ctx e *)
    (* val () = println "" *)
    val e_str = ExportPP.pp_e_to_string (NONE, NONE) $ export ToStringUtil.empty_ctx e
    val () = write_file ("cc-unit-test-after-cc.tmp", e_str)
    val () = println e_str
    val () = println ""
    (* val () = println "Done" *)
    (* val () = println "Checking closed-ness of ERec's" *)
    (* val () = check_ERec_closed e *)
    val () = println "Started MicroTiML typechecking #3 ..."
    val ((e, t, i), vcs, admits) = typecheck [] ([], [], [](* , HeapMap.empty *)) e
    val () = println "Finished MicroTiML typechecking #3"
    val () = println "Type:"
    val () = pp_t NONE $ export_t ([], []) t
    val () = println "Time:"
    val i = simp_i i
    val () = println $ ToString.str_i Gctx.empty [] i
                     
    val () = println "CC.UnitTest passed"
  in
    ((* t, e *))
  end
  handle MicroTiMLTypecheck.MTCError msg => (println $ "MTiMLTC.MTCError: " ^ substr 0 1000 msg; fail ())
       | TypeCheck.Error (_, msgs) => (app println $ "TC.Error: " :: msgs; fail ())
       | NameResolve.Error (_, msg) => (println $ "NR.Error: " ^ msg; fail ())
    
val test_suites = [
      test1
]
                            
end
                       
end
