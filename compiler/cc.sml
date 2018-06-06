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
open MicroTiMLLongId
open MicroTiMLLocallyNameless
open MicroTiMLUtil
open MicroTiML
       
fun free_ivars_with_anno_idx_visitor_vtable cast output =
  let
    fun visit_IVar this env (data as (var, sorts)) =
        let
          val sorts = visit_list (#visit_sort (cast this) this) env sorts
          val () = 
              case var of
                  QID (_, (x, _)) =>
                  (case sorts of
                       s :: _ => output (Free_i x, s)
                     | [] => raise Impossible $ "free_ivars_with_anno_i/IVar/QID/sorts=[]: " ^ str_int x
                  )
                | _ => ()
        in
          IVar data
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
    val vtable = override_visit_IVar vtable visit_IVar
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
    fun visit_IVar this env (data as (var, sorts)) =
        let
          val () =
              case var of
                  QID (_, (x, _)) => output $ Free_i x
                | _ => ()
        in
          IVar data
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
    val vtable = override_visit_IVar vtable visit_IVar
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
                   val msg = sprintf "topo_sort failed on expr: $\n" [ExportPP.pp_e_to_string (NONE, NONE) $ ExportPP.export (NONE, NONE) ([], [], [], []) e]
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

fun free_tvars_with_anno_ty_visitor_vtable cast output (* : ('this, unit, 'var, 'basic_sort, 'idx, 'sort, 'var, 'basic_sort, 'idx, 'sort) ty_visitor_vtable *) =
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

val code_blocks = ref ([] : (free_e * string * (var, idx, sort, basic_sort kind, (var, basic_sort, idx, sort) ty) expr) list)
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
      
fun IV (x, s) = IVar (make_Free_i x, [s])
fun TV (x, k) = TVar (make_Free_t x, [k])

fun TExists bind = TQuan (Exists (), bind)
                         
val ETT = EConst (ECTT ())

fun ceil_half n = (n + 1) div 2

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

fun cc_ty_visitor_vtable cast () =
  let
    val vtable =
        default_ty_visitor_vtable
          cast
          extend_noop
          extend_noop
          visit_noop
          visit_noop
          visit_noop
          visit_noop
    fun visit_ty this env t =
      let
        fun cc_t t = #visit_ty (cast this) this env t
      in
      case t of
          TArrow _ => cc_t_arrow t
        | TQuan (Forall (), _) => cc_t_arrow t
        | TQuanI (Forall (), _) => cc_t_arrow t
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
            val (s, (name, (_, t))) = unBindAnnoName bind
            val a = fresh_ivar ()
            val t = open0_i_t a t
            val t = cc_t t
          in
            TQuanI0 (q, close0_i_t_anno ((a, fst name, s), t))
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
        | _ => #visit_ty vtable this env t (* call super *)
      end
    val vtable = override_visit_ty vtable visit_ty
  in
    vtable
  end

and new_cc_ty_visitor a = new_ty_visitor cc_ty_visitor_vtable a
    
and cc_t t =
  let
    val visitor as (TyVisitor vtable) = new_cc_ty_visitor ()
  in
    #visit_ty vtable visitor () t
  end
    
and cc_t_arrow t =
    let
      val (binds, t) = open_collect_TForallIT t
      val ((st1, t1), i, (st2, t2)) = assert_TArrow t
      val t1 = cc_t t1
      val t2 = cc_t t2
      val alpha = fresh_tvar ()
      val t = TArrow ((st1, TProd (TV (alpha, KType ()), t1)), i, (st2, t2))
      val t = close_TForallITs (binds, t)
      val t = TProd (t, TV (alpha, KType ()))
      val t = TExists $ close0_t_t_anno ((alpha, "'a", KType ()), t)
    in
      t
    end

fun apply_TForallIT b args =
    case (b, args) of
        (TQuanI (Forall (), bind), inl v :: args) =>
        let
          val (_, (_, (_, b))) = unBindAnnoName bind
        in
          apply_TForallIT (subst0_i_t v b) args
        end
      | (TQuan (Forall (), bind), inr v :: args) =>
        let
          val (_, (_, b)) = unBindAnnoName bind
        in
          apply_TForallIT (subst0_t_t v b) args
        end
      | (_, []) => b
      | _ => raise Impossible "apply_TForallIT"

fun cc_expr_visitor_vtable cast () =
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
          (ignore_this_env cc_t)
    fun visit_expr this env e =
      let
        (* val () = print $ "cc() started: " *)
        (* val e_str = (* substr 0 400 $  *)ExportPP.pp_e_to_string (NONE, NONE) $ ExportPP.export (SOME 1, SOME 1) ([], [], [], []) e *)
        (* val () = println $ e_str *)
        (* fun err () = raise Impossible $ "unknown case of cc() on: " ^ (ExportPP.pp_e_to_string (NONE, NONE) $ ExportPP.export (NONE, NONE) ([], [], [], []) e) *)
        fun cc_t t = #visit_ty (cast this) this env t
        fun cc_e e = #visit_expr (cast this) this env e
        val e =
            case e of
                EBinOp (EBApp (), e1, e2) =>
                let
                  (* val () = println "cc() on EApp" *)
                  val (e1, itargs) = collect_EAppIT e1
                  (* val (e1, t_e1) = assert_EAscType e1 *)
                  (* val t_e1 = cc_t t_e1 *)
                  (* val (_, t_pair) = assert_TExists t_e1 *)
                  (* val (t_code, _) = assert_TProd t_pair *)
                  val gamma = fresh_tvar ()
                  val z = fresh_evar ()
                  val z_code = fresh_evar ()
                  val z_env = fresh_evar ()
                  val p = fresh_evar ()
                  val p_def = EPair (EV z_env, cc e2)
                  val e = EAppITs (EV z_code, map (map_inr cc_t) itargs) %$ EV p
                  (* val () = println $ "cc()/EApp: before ELetManyClose()" *)
                  val e = ELetManyClose ([(z_code, "z_code", EFst $ EV z), (z_env, "z_env", ESnd $ EV z), (p, "p", p_def)], e)
                  (* val () = println $ "cc()/EApp: after ELetManyClose()" *)
                  val e = EUnpackClose (cc e1, (gamma, "'c"), (z, "z"), e)
                                       (* val () = println "cc() done on EApp" *)
                in
                  e
                end
              | EAbsT _ => cc_abs e
              | EAbsI _ => cc_abs e
              | EAbs _ => cc_abs e
              | ERec _ => cc_abs e
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
              | EIfi (e, bind1, bind2) =>
                let
                  val e = cc e
                  val (x1, name1, e1) = unBindSimpOpen_e bind1
                  val (x2, name2, e2) = unBindSimpOpen_e bind2
                in
                  EIfiClose (e, ((x1, fst name1), cc e1), ((x2, fst name2), cc e2))
                end
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
              | EUnpackI (e1, bind) =>
                let
                  (* val () = println "before cc()/EUnpackI/cc#1" *)
                  val e1 = cc e1
                  (* val () = println "after cc()/EUnpackI/cc#1" *)
                  val (name_a, bind) = unBindSimpName bind
                  val (name_x, e2) = unBindSimpName bind
                  val a = fresh_ivar ()
                  val x = fresh_evar ()
                  (* val () = println "before cc()/EUnpackI/open0_i_e()" *)
                  (* this could be slow *)
                  val e2 = open0_i_e a e2
                  (* val () = println "after cc()/EUnpackI/open0_i_e()" *)
                  val e2 = open0_e_e x e2
                  (* val () = println "before cc()/EUnpackI/cc#2" *)
                  val e2 = cc e2
                  (* val () = println "after cc()/EUnpackI/cc#2" *)
                  val e = EUnpackIClose (e1, (a, fst name_a), (x, fst name_x), e2)
                                        (* val () = println "done cc()/EUnpackI" *)
                in
                  e
                end
              | _ => #visit_expr vtable this env e (* call super *)
        (* val () = println $ "cc() finished: " ^ e_str *)
      in
        e
      end
    val vtable = override_visit_expr vtable visit_expr
  in
    vtable
  end

and new_cc_expr_visitor params = new_expr_visitor cc_expr_visitor_vtable params

and cc b =
  let
    val visitor as (ExprVisitor vtable) = new_cc_expr_visitor ()
  in
    #visit_expr vtable visitor () b
  end

and cc_abs e_all =
    let
      val () = println $ "cc_abs(): before open_collect_EAbsIT()"
      val (binds, e) = open_collect_EAbsIT e_all (* todo: this could be slow, should be combined *)
      val () = println $ "cc_abs(): after open_collect_EAbsIT()"
    in
      case e of
          ERec bind => cc_ERec e_all binds bind
        | _ => raise Impossible "cc_abs"
    end

and cc_ERec e_all outer_binds bind =
    let
      val (t_x, (name_x, e)) = unBindAnnoName bind
      val () = println $ "cc() on: " ^ fst name_x
      val x = fresh_evar ()
      val e = open0_e_e x e
      val () = println $ "cc(): before open_collect_EAbsIT()"
      val (inner_binds, e) = open_collect_EAbsIT e (* todo: this could be slow, should be combined *)
      val () = println $ "cc(): after open_collect_EAbsIT()"
      val (st, (t_z, (name_z, e))) = assert_EAbs e
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
      fun eq_bind xx' =
          case xx' of
              (inl (x, _, _), inl (x', _, _)) => x = x'
            | (inr (x, _, _), inr (x', _, _)) => x = x'
            | _ => false
      val outer_inner_binds = outer_binds @ inner_binds
      val () = println "before free_ivars"
      (* val free_ivars = mapi (add_name "a") $ free_ivars_with_anno_e e *)
      val free_ivars = mapi (add_name "a") $ free_ivars_with_anno_e e_all (* need [e_all] here because the [e_all - e] part may contain free vars *) (* todo: e can be much smaller than e_all because e is after CC, so collecting free vars on e_all could be slow *)
      val () = println "after free_ivars"
      (* val free_tvars = mapi (add_name "'a") $ free_tvars_with_anno_e e *)
      val free_tvars = mapi (add_name "'a") $ free_tvars_with_anno_e e_all (* need [e_all] here because the [e_all - e] part may contain free vars *)
      val betas = map inl free_ivars @ map inr free_tvars
      (* val betas = diff eq_bind betas outer_inner_binds *) (* no need when we use e_all to collect free vars *)
      val () = println $ "cc(): after getting free vars"
      val t_env = TTuple sigmas
      val t_z = cc_t t_z
      val t_arrow = cont_type ((st, TProd (t_env, t_z)), i)
      val z_code = fresh_evar ()
      val z_env = fresh_evar ()
      fun EAppITs_binds (e, binds) =
          let
            (* fun proj_3_1 (a1, _, _) = a1 *)
            fun make_var f (x, _, anno) = f (x, anno)
          in
            EAppITs (e, map (map_inl_inr (make_var IV) (make_var TV)) binds)
          end
      val p = fresh_evar ()
      val p_def = EPair (EAppITs_binds (EV z_code, betas @ outer_binds), EV z_env)
      val def_x = EPack (cc_t t_x, t_env, EV p)
      val len_ys = length ys
      val ys_defs = mapi (fn (i, y) => (y, "y" ^ str_int (1+i), ETupleProj (EV z_env, i))) ys
      val () = println $ "cc(): before ELetManyClose()"
      val e = ELetManyClose ((p, "p", p_def) :: (x, fst name_x, def_x) :: ys_defs, e)
      val () = println $ "cc(): after ELetManyClose()"
      val e = EAbsPairClose (st, (z_env, "z_env", t_env), (z, fst name_z, t_z), e)
      val betas_outer_inner_binds = betas @ outer_inner_binds
      val () = println $ "cc(): before close_EAbsITs()"
      val e = close_EAbsITs (betas_outer_inner_binds, e)
      val () = println $ "cc(): after close_EAbsITs()"
      val () = println $ "cc(): before close_TForallITs()"
      val t_rawcode = close_TForallITs (betas_outer_inner_binds, t_arrow)
      val () = println $ "cc(): after close_TForallITs()"
      (* val t_code = TForallITClose (inner_binds, t_arrow) *)
      fun decorate_code_name s = "code_" ^ s
      val v_code = ERec $ close0_e_e_anno ((z_code,  decorate_code_name $ fst name_x, t_rawcode), e)
      fun EV_anno (y, anno) = EAscType (EV y, anno)
                                       
      val v_env = ETuple $ map EV_anno ys_anno
      val x_code = fresh_evar ()
      val () = println $ "cc(): before close_TForallITs()#2"
      val e = EPack (cc_t $ close_TForallITs (outer_binds, t_x), t_env, EPair (EAppITs_binds (EV x_code(* v_code *), betas), v_env))
      val () = println $ "cc(): after close_TForallITs()#2"
                    
      (* val tuple_def = ETuple $ map EV_anno ys_anno *)
      (* val tuple = fresh_evar () *)
      (* val x_code = fresh_evar () *)
      (* val pair_def = EPair (EAppITs_binds (EV x_code(* v_code *), betas), EV tuple) *)
      (* val pair = fresh_evar () *)
      (* val () = println $ "cc(): before close_TForallITs()#2" *)
      (* val e = EPack (cc_t $ close_TForallITs (outer_binds, t_x), t_env, EV pair) *)
      (* val () = println $ "cc(): after close_TForallITs()#2" *)
      (* val e = ELetManyClose ([(tuple, "t", tuple_def), (pair, "p", pair_def)], e) *)
                    
      val x_v_code = (x_code, decorate_code_name $ fst name_x, v_code)
      val () = add_code_block x_v_code
      (* val e = ELetClose (x_v_code, e) *)
      val () = println $ "cc() done on: " ^ fst name_x
    in
      e
    end

fun convert_EAbs_to_ERec_expr_visitor_vtable cast () =
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
          val (t_x, (name_x, e)) = unBindAnnoName bind
          val (binds, e) = collect_EAbsIT e
          val (st, (t_y, (name_y, e))) = assert_EAbs e
          val (e, _) = assert_EAscState e
          val (e, _) = assert_EAscTimeSpace e
          val (e, _) = assert_EAscType e
          val e = #visit_expr (cast this) this env e
          val e = EAbs (st, EBindAnno ((name_y, t_y), e))
        in
          ERec $ EBindAnno ((name_x, t_x), EAbsITs (binds, e))
        end
    val mark_begin = "__$begin$_"
    val len_mark_begin = String.size mark_begin
    val mark_end = #"$"
    val default_fun_name = "__f"
    fun visit_EAbs this env (pre, bind) =
      let
        val (t_y, ((name_y, r), e)) = unBindAnnoName bind
        (* val () = println $ "visit_EAbs()/name_y: " ^ name_y *)
        val (fun_name, name_y) =
            if String.isPrefix mark_begin name_y then
              (case String.fields (curry op= mark_end) $ String.extract (name_y, len_mark_begin, NONE) of
                   [fun_name, name_y] => (fun_name, name_y)
                 | _ => (default_fun_name, name_y)
              )
            else (default_fun_name, name_y)
        val (e, post) = assert_EAscState e
        val (e, i) = assert_EAscTimeSpace e
        val (_, t_e) = assert_EAscType e
        val e = #visit_expr (cast this) this env e
        val e = EAbs (pre, EBindAnno (((name_y, r), t_y), e))
      in
        ERec $ EBindAnno (((fun_name, dummy), TArrow ((pre, t_y), i, (post, t_e))), shift01_e_e e)
      end
    fun visit_ELet this env (data as (e1, bind)) =
        let
          val ((name_x, _), _) = unBindSimpName bind
          val (e1, ascs) = collect_EAscTypeTime e1
          val (binds, e1) = collect_EAbsIT e1
          val e1 = 
              case e1 of
                  EAbs (st, bind1) =>
                  let
                    val (t_y, ((name_y, r), e1)) = unBindAnnoName bind1
                  in
                    EAbs (st, EBindAnno (((mark_begin ^ name_x ^ String.str mark_end ^ name_y, r), t_y), e1))
                  end
                | _ => e1
          val e1 = EAbsITs (binds, e1)
          val e1 = EAscTypeTimes (e1, ascs)
        in
          (* call super *)
          #visit_ELet vtable this env (e1, bind)
        end
    val vtable = override_visit_ERec vtable visit_ERec
    val vtable = override_visit_EAbs vtable visit_EAbs
    val vtable = override_visit_ELet vtable visit_ELet
  in
    vtable
  end

fun new_convert_EAbs_to_ERec_expr_visitor params = new_expr_visitor convert_EAbs_to_ERec_expr_visitor_vtable params

fun convert_EAbs_to_ERec b =
  let
    val visitor as (ExprVisitor vtable) = new_convert_EAbs_to_ERec_expr_visitor ()
  in
    #visit_expr vtable visitor () b
  end

fun remove_var_anno_idx_visitor_vtable cast () =
  let
    fun visit_IVar this env (var, sorts) =
      IVar (var, [])
    val vtable = 
        default_idx_visitor_vtable
          cast
          extend_noop
          (visit_imposs "remove_var_anno_i/visit_var")
          visit_noop
          visit_noop
          visit_noop
          visit_noop
    val vtable = override_visit_IVar vtable visit_IVar
  in
    vtable
  end

fun new_remove_var_anno_idx_visitor a = new_idx_visitor remove_var_anno_idx_visitor_vtable a
    
fun remove_var_anno_i b =
  let
    val visitor as (IdxVisitor vtable) = new_remove_var_anno_idx_visitor ()
  in
    #visit_idx vtable visitor () b
  end
    
fun remove_var_anno_s b =
  let
    val visitor as (IdxVisitor vtable) = new_remove_var_anno_idx_visitor ()
  in
    #visit_sort vtable visitor () b
  end
    
fun remove_var_anno_ty_visitor_vtable cast () =
  let
    fun visit_TVar this env (var, ks) =
      TVar (var, [])
    val vtable = 
        default_ty_visitor_vtable
          cast
          extend_noop
          extend_noop
          (visit_imposs "remove_var_anno_t/visit_var")
          visit_noop
          (ignore_this_env remove_var_anno_i)
          (ignore_this_env remove_var_anno_s)
    val vtable = override_visit_TVar vtable visit_TVar
  in
    vtable
  end

fun new_remove_var_anno_ty_visitor a = new_ty_visitor remove_var_anno_ty_visitor_vtable a
    
fun remove_var_anno_t b =
  let
    val visitor as (TyVisitor vtable) = new_remove_var_anno_ty_visitor ()
  in
    #visit_ty vtable visitor () b
  end
    
fun remove_var_anno_expr_visitor_vtable cast () =
  let
    fun visit_EAscType this env (e, t) =
      let
        val vtable = cast this
        val (e_core, annos) = collect_EAscTypeTime e
        val e = #visit_expr vtable this env e
        val annos = map (map_inl_inr (#visit_ty vtable this env) (#visit_idx vtable this env)) annos
        val e = EAscTypeTimes (e, annos)
      in
        case e_core of
            EVar _ => e
          | _ => EAscType (e, #visit_ty vtable this env t)
      end
    val vtable = 
        default_expr_visitor_vtable
          cast
          extend_noop
          extend_noop
          extend_noop
          extend_noop
          visit_noop
          visit_noop
          (ignore_this_env remove_var_anno_i)
          (ignore_this_env remove_var_anno_s)
          (ignore_this_env remove_var_anno_t)
    val vtable = override_visit_EAscType vtable visit_EAscType
  in
    vtable
  end

fun new_remove_var_anno_expr_visitor params = new_expr_visitor remove_var_anno_expr_visitor_vtable params

fun remove_var_anno_e b =
  let
    val visitor as (ExprVisitor vtable) = new_remove_var_anno_expr_visitor ()
  in
    #visit_expr vtable visitor () b
  end

fun combine_non_compute_expr_visitor_vtable cast () =
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
    fun visit_ELet this env (data as (e1, bind)) =
      let
        val vtable = cast this
        val e1 = #visit_expr vtable this env e1
        fun is_non_compute e =
          let
            val f = is_non_compute
          in
            case e of
                EVar _ => true
              | EState _ => true (* todo: why? *)
              | EAppI (e, _) => f e
              (* | EPackI (_, _, e) => f e *)
              | _ => false
          end
      in
        if is_non_compute e1 then
          let
            val (_, e2) = unBind bind
          in
            #visit_expr vtable this env $ subst0_e_e e1 e2
          end
        else
          let
            fun visit_ebind this = visit_bind_simp (#extend_e (cast this) this)
            val bind = visit_ebind this (#visit_expr vtable this) env bind
          in
            ELet (e1, bind)
          end
      end
    val vtable = override_visit_ELet vtable visit_ELet
  in
    vtable
  end

fun new_combine_non_compute_expr_visitor params = new_expr_visitor combine_non_compute_expr_visitor_vtable params
    
fun combine_non_compute b =
  let
    val visitor as (ExprVisitor vtable) = new_combine_non_compute_expr_visitor ()
  in
    #visit_expr vtable visitor () b
  end
    
val cc =
 fn e =>
    let
      val e = convert_EAbs_to_ERec e
      val () = code_blocks := []
      val () = code_labels := IntBinarySet.empty
      val e = cc e
      val decls = rev $ !code_blocks
      val e = ELetManyClose (decls, e)
      val e = remove_var_anno_e e
      val e = ANF.anf e
      (* val e = MicroTiMLPostProcess.post_process e *)
      val e = combine_non_compute e
      val e = ExportPP.uniquefy_e ToStringUtil.empty_ctx e
    in
      e
    end

val cc_tc_flags =
    let
      open MicroTiMLTypecheck
    in
      [Anno_EAbs, Anno_EVar, Anno_EAbs_state]
    end
                     
(* val forget_var = Subst.forget_var *)
(* val forget_i_i = Subst.forget_i_i *)
(* val forget_i_s = Subst.forget_i_s *)
(* fun forget_i_t a = shift_i_t_fn (forget_i_i, forget_i_s) a *)
(* fun forget_t_t a = shift_t_t_fn forget_var a *)
(* fun forget_i_e a = shift_i_e_fn (forget_i_i, forget_i_s, forget_i_t) a *)
(* fun forget_t_e a = shift_t_e_fn (forget_t_t) a *)
(* fun forget_e_e a = shift_e_e_fn forget_var a *)
                               
(* fun check_ERec_closed_expr_visitor_vtable cast output = *)
(*   let *)
(*     val vtable =  *)
(*         default_expr_visitor_vtable *)
(*           cast *)
(*           extend_noop *)
(*           extend_noop *)
(*           extend_noop *)
(*           extend_noop *)
(*           visit_noop *)
(*           visit_noop *)
(*           visit_noop *)
(*           visit_noop *)
(*           visit_noop *)
(*     fun visit_ERec this env bind = *)
(*         let *)
(*           (* call super *) *)
(*           val e = #visit_ERec vtable this env bind *)
(*           val (_, (name, _)) = unBindAnnoName bind *)
(*           val name = fst name *)
(*           val () = *)
(*               let *)
(*                 val large = 1000000000 *)
(*                 val _ = forget_i_e 0 large e *)
(*                 val _ = forget_t_e 0 large e *)
(*                 val _ = forget_e_e 0 large e *)
(*               in *)
(*                 (* println $ name ^ " is closed" *) *)
(*                 () *)
(*               end *)
(*               handle _ => *)
(*                      (* println $ name ^ " is open" *) *)
(*                      output name *)
(*         in *)
(*           e *)
(*         end *)
(*     val vtable = override_visit_ERec vtable visit_ERec *)
(*   in *)
(*     vtable *)
(*   end *)

(* fun new_check_ERec_closed_expr_visitor params = new_expr_visitor check_ERec_closed_expr_visitor_vtable params *)

(* fun check_ERec_closed b = *)
(*     let *)
(*       val r = ref [] *)
(*       fun output item = push_ref r item *)
(*       val visitor as (ExprVisitor vtable) = new_check_ERec_closed_expr_visitor output *)
(*       val _ = #visit_expr vtable visitor () b *)
(*       val opens = !r *)
(*     in *)
(*       if not $ null opens then *)
(*         raise Impossible $ "These ERec's are not closed: " ^ str_ls id opens *)
(*       else () *)
(*     end *)

structure UnitTest = struct

structure TestUtil = struct

open CPS
open LongId
open Util
open MicroTiML
open MicroTiMLVisitor
open MicroTiMLLongId
open MicroTiML
       
fun fail () = OS.Process.exit OS.Process.failure
                   
end

open TestUtil
       
fun test1 dirname =
  let
    val () = println "CC.UnitTest started"
    val filename = join_dir_file (dirname, "cc-test1.pkg")
    val filenames = map snd $ ParseFilename.expand_pkg (fn msg => raise Impossible msg) (true, filename)
    open Parser
    val prog = concatMap parse_file filenames
    open Elaborate
    val prog = elaborate_prog prog
    open NameResolve
    val (prog, _, _) = resolve_prog empty prog
                                    
    open TypeCheck
    val () = TypeCheck.turn_on_builtin ()
    val () = println "Started TiML typechecking ..."
    val () = TypeCheck.clear_st_types ()
    val ((prog, _, _), (vcs, admits)) = typecheck_prog empty prog
    val st_types = fst $ TypeCheck.get_st_types ()
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
    val empty_ctx = ToStringUtil.empty_ctx
    (* val () = println $ str_e empty empty_ctx e *)
    (* val () = println "" *)
    val () = println "Started translating ..."
    val e = trans_e e
    val st_types = StMap.map (mapSnd trans_mt) st_types
    val () = println "Finished translating"
    (* val () = pp_e $ export empty_ctx e *)
    (* val () = println "" *)
                     
    open MicroTiMLTypecheck
    open TestUtil
    val () = println "Started MicroTiML typechecking #1 ..."
    val ((e, t, i, st), (vcs, admits)) = typecheck (cps_tc_flags, st_types) (([], [], []), IEmptyState) e
    val () = println "Finished MicroTiML typechecking #1"
    val () = println "Type:"
    open ExportPP
    val () = pp_t NONE $ export_t NONE ([], []) t
    fun print_time_space (i, j) =
        let
          val () = println "Time:"
          val () = println $ ToString.str_i Gctx.empty [] $ simp_i i
          val () = println "Space:"
          val () = println $ ToString.str_i Gctx.empty [] $ simp_i j
        in
          ()
        end
    val () = print_time_space i
    (* val () = println $ "#VCs: " ^ str_int (length vcs) *)
    (* val () = println "VCs:" *)
    (* val () = app println $ concatMap (fn ls => ls @ [""]) $ map (str_vc false "") vcs *)
    (* val () = pp_e $ export empty_ctx e *)
    (* val () = println "" *)
                     
    val () = println "Started CPS conversion ..."
    open MicroTiMLUtil
    val (e, _) = cps (e, TUnit, IEmptyState) (EHaltFun TUnit TUnit, TN0)
    (* val (e, _) = cps (e, TUnit) (Eid TUnit, T_0) *)
    val () = println "Finished CPS conversion"
    (* val () = pp_e $ export empty_ctx e *)
    (* val () = println "" *)
    val e_str = ExportPP.pp_e_to_string (NONE, NONE) $ export (NONE, NONE) empty_ctx e
    val () = write_file ("cc-unit-test-after-cps.tmp", e_str)
    val () = println e_str
    val () = println ""
    val () = println "Started MicroTiML typechecking #2 ..."
    val ((e, t, i, st), (vcs, admits)) = typecheck (cc_tc_flags, st_types) (([], [], []), IEmptyState) e
    val () = println "Finished MicroTiML typechecking #2"
    val () = println "Type:"
    val () = pp_t NONE $ export_t NONE ([], []) t
    val () = print_time_space i
    (* val () = pp_e (NONE, NONE) $ export (NONE, NONE) empty_ctx e *)
    (* val () = println "" *)
                     
    val () = println "Started CC ..."
    val e = cc e
    val () = println "Finished CC"
    (* val () = pp_e $ export empty_ctx e *)
    (* val () = println "" *)
    val e_str = ExportPP.pp_e_to_string (NONE, NONE) $ export (NONE, NONE) empty_ctx e
    val () = write_file ("cc-unit-test-after-cc.tmp", e_str)
    val () = println e_str
    val () = println ""
    (* val () = println "Done" *)
    (* val () = println "Checking closed-ness of ERec's" *)
    (* val () = check_ERec_closed e *)
    val () = println "Started MicroTiML typechecking #3 ..."
    val ((e, t, i, st), (vcs, admits)) = typecheck ([], st_types) (([], [], []), IEmptyState) e
    val () = println "Finished MicroTiML typechecking #3"
    val () = println "Type:"
    val () = pp_t NONE $ export_t NONE ([], []) t
    val () = print_time_space i
                     
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
