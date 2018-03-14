structure MicroTiMLTypecheck = struct

open UVar
open TypecheckUtil
open FreshUVar
open Expr

exception MTCError of string
exception MSCError of region * string list
exception MUnifyError of region * string list

structure Unify = UnifyFn (struct exception UnifyError = MUnifyError end)
open Unify
       
infixr 0 $
infixr 0 !!

infix 9 %@
infix 8 %^
infix 7 %*
infix 6 %+ 
infix 4 %<=
infix 4 %<
infix 4 %>=
infix 4 %=
infixr 3 /\
infixr 2 \/
infixr 1 -->
infix 1 <->
        
fun is_wf_bsort_UVarBS data = UVarBS data
    
fun get_bsort_UVarI gctx ctx (data as (x, r)) =
  let
    val (_, ctx, bs_ret) = get_uvar_info x !! (fn () => raise Impossible "get_bsort_UVarI")
  in
    (UVarI data, foldl (fn ((_, bs_arg), acc) => BSArrow (bs_arg, acc)) bs_ret ctx)
  end

fun match_BSArrow gctx ctx r bs =
  case update_bs bs of
      BSArrow data => data
    | _ => raise Impossible $ "match_BSArrow: " ^ str_bs bs

fun get_sort_type_UVarS gctx ctx data = UVarS data

fun open_close add ns ctx f = f $ add ns ctx

type state = (scontext * prop) list
val vcs : state ref = ref []
val admits : state ref = ref []
                 
(* fun check_prop ctx p = push_ref vcs (ctx, p) *)
fun check_prop ctx p = ()
fun add_admit ctx p = push_ref admits (ctx, p)               
                         
fun write_prop ctx (p, r) = check_prop ctx p
fun write_admit ctx (p, r) = add_admit ctx p
                                       
structure Sortcheck = SortcheckFn (structure U = Expr
                                   structure T = Expr
                                   type sigcontext = sigcontext
                                   val str_bs = str_bs
                                   val str_i = str_i
                                   val str_s = str_s
                                   val U_str_i = str_i
                                   val fetch_sort = fetch_sort
                                   val is_wf_bsort_UVarBS = is_wf_bsort_UVarBS
                                   val get_bsort_UVarI = get_bsort_UVarI
                                   val match_BSArrow = match_BSArrow
                                   val get_sort_type_UVarS = get_sort_type_UVarS
                                   val unify_bs = unify_bs
                                   val get_region_i = get_region_i
                                   val get_region_s = get_region_s
                                   val U_get_region_i = U.get_region_i
                                   val U_get_region_p = U.get_region_p
                                   val open_close = open_close
                                   val add_sorting = add_sorting
                                   val update_bs = update_bs
                                   exception Error = MSCError
                                   val get_base = get_base
                                   val gctx_names = gctx_names
                                   val normalize_s = normalize_s
                                   val subst_i_p = subst_i_p
                                   val write_admit = write_admit
                                   val write_prop = write_prop
                                   val get_uvar_info = get_uvar_info
                                   val refine = refine
                                  )
open Sortcheck

open MicroTiMLExLongId
open MicroTiMLExUtil
open MicroTiMLEx

fun sc ctx i = get_bsort Gctx.empty (ctx, i)
fun sc_against_sort ctx (i, s) = check_sort Gctx.empty (ctx, i, s)

fun is_wf_sort ctx s = Sortcheck.is_wf_sort Gctx.empty (ctx, s)

fun INat n = ConstIN (n, dummy)
val TInt = TConst TCInt
val unTQuan = unBindAnnoName
val unTQuanI = unBindAnnoName
val unTAbsI = unBindAnnoName
fun unELetIdx (def, bind) =
    (def, unBindSimpName bind)
val unELetType = unELetIdx
val unELet = unELetIdx
val unELetConstr = unELetIdx
fun unEUnpack (def, bind) =
  let
    val (name1, bind) = unBindSimp bind
    val (name2, e) = unBindSimp bind
  in
    (def, (unName name1, unName name2, e))
  end
val unEAbs = unBindAnnoName
fun unECase (e, bind1, bind2) =
  let
    val (name1, e1) = unBindSimp bind1
    val (name2, e2) = unBindSimp bind2
  in
    (e, (unName name1, e1), (unName name2, e2))
  end
               
fun is_eq_bsort x = unify_bs dummy x
  
fun BasicSort b = Basic (b, dummy)
                        
fun is_eq_idx ctx (i, i') = check_prop ctx (i %= i')

open Bind
       
fun is_eq_sort ctx (s, s') =
  case (s, s') of
      (Basic (bs, _), Basic (bs', _)) =>
      is_eq_bsort (bs, bs')
    | (Subset ((bs, r1), Bind ((name, _), p), _), Subset ((bs', _), Bind (_, p'), _)) =>
      let
	val () = is_eq_bsort (bs, bs')
	val () = check_prop (add_sorting (name, BasicSort bs) ctx) (p --> p')
      in
        ()
      end
    | (Subset ((bs, r1), Bind ((name, _), p), _), Basic (bs', _)) =>
      let
	val () = is_eq_bsort (bs, bs')
      in
        ()
      end
    | (Basic (bs, r1), Subset ((bs', _), Bind ((name, _), p), _)) =>
      let
	val () = is_eq_bsort (bs, bs')
	val () = check_prop (add_sorting (name, BasicSort bs) ctx) p
      in
        ()
      end
    | _ => raise MTCError "is_eq_sort"
                                       
fun is_eq_kind (k, k') =
  case (k, k') of
      (KType, KType) => ()
    | (KArrow (b, k), KArrow (b', k')) =>
      let
        val () = is_eq_bsort (b, b')
        val () = is_eq_kind (k, k')
      in
        ()
      end
    | (KArrowT (k1, k2), KArrowT (k1', k2')) =>
      let
        val () = is_eq_kind (k1, k1')
        val () = is_eq_kind (k2, k2')
      in
        ()
      end
    | _ => raise MTCError "can't unify kinds" 
       
fun get_ty_const_kind c =
  case c of
      TCUnit => KType
    | TCInt => KType
    | TCEmpty => KType

fun get_ty_bin_op_arg1_kind opr =
  case opr of
      TBProd => KType
    | TBSum => KType
                 
fun get_ty_bin_op_arg2_kind opr =
  case opr of
      TBProd => KType
    | TBSum => KType
                 
fun get_ty_bin_op_res_kind opr =
  case opr of
      TBProd => KType
    | TBSum => KType

fun nth_error_local ls x =
  case x of
      ID (n, _) => nth_error ls n
    | QID _ => raise MTCError "nth_error QID"
                      
type icontext = (string * sort) list
type tcontext = (string * bsort kind) list
                            
fun add_sorting_it new (ictx, tctx) = (new :: ictx, tctx)
fun add_kinding_it new (ictx, tctx) = (ictx, new :: tctx)

fun kc (ctx as (ictx, tctx) : icontext * tcontext) t_input =
  case t_input of
      TVar (x, ks) =>
      (case ks of
           k :: ks =>
           let
             val _ = kc_against_kind ctx (TVar (x, ks), k)
           in
             (t_input, k)
           end
         | [] =>
           case nth_error_local tctx x of
               SOME (_, k) => (TVar (x, [k]), k)
             | NONE => raise MTCError "unbound type variable"
      )
    | TConst c => (t_input, get_ty_const_kind c)
    | TBinOp (opr, t1, t2) =>
      let
        val t1 = kc_against_kind ctx (t1, get_ty_bin_op_arg1_kind opr)
        val t2 = kc_against_kind ctx (t2, get_ty_bin_op_arg2_kind opr)
      in
        (TBinOp (opr, t1, t2), get_ty_bin_op_res_kind opr)
      end
    | TArrow (t1, i, t2) =>
      let
        val t1 = kc_against_kind ctx (t1, KType)
        val i = sc_against_sort ictx (i, STime)
        val t2 = kc_against_kind ctx (t2, KType)
      in
        (TArrow (t1, i, t2), KType)
      end
    | TAbsI data =>
      let
        val (b, (name, t)) = unTAbsI data
        val (t, k) = kc (add_sorting_it (fst name, BasicSort b) ctx) t
      in
        (TAbsI $ IBindAnno ((name, b), t), KArrow (b, k))
      end
    | TAppI (t, i) =>
      let
        val (t, k') = kc ctx t
        val (b, k) = case k' of
                         KArrow data => data
                       | _ => raise MTCError "TAppI"
        val i = sc_against_sort ictx (i, BasicSort b)
      in
        (TAppI (t, i), k)
      end
    | TAbsT data =>
      let
        val (k1, (name, t)) = unTAbsT data
        val (t, k2) = kc (add_kinding_it (fst name, k1) ctx) t
      in
        (TAbsT $ TBindAnno ((name, k1), t), KArrowT (k1, k2))
      end
    | TAppT (t1, t2) =>
      let
        val (t1, k') = kc ctx t1
        val (k1, k2) = case k' of
                         KArrowT data => data
                       | _ => raise MTCError "TAppT"
        val t2 = kc_against_kind ctx (t2, k1)
      in
        (TAppT (t1, t2), k2)
      end
    | TQuanI (q, data) =>
      let
        val (s, (name, t)) = unTQuanI data
        val s = is_wf_sort ictx s
        val t = kc_against_kind (add_sorting_it (fst name, s) ctx) (t, KType)
      in
        (TQuanI (q, IBindAnno ((name, s), t)), KType)
      end
    | TQuan (q, data) =>
      let
        val (k, (name, t)) = unTQuan data
        val t = kc_against_kind (add_kinding_it (fst name, k) ctx) (t, KType)
      in
        (TQuan (q, TBindAnno ((name, k), t)), KType)
      end
    | TRec data =>
      let
        val (k, (name, t)) = unBindAnnoName data
        val t = kc_against_kind (add_kinding_it (fst name, k) ctx) (t, k)
      in
        (TRec $ TBindAnno ((name, k), t), k)
      end
    | TNat i =>
      let
        val i = sc_against_sort ictx (i, SNat)
      in
        (TNat i, KType)
      end
    | TArr (t, i) =>
      let
        val t = kc_against_kind ctx (t, KType)
        val i = sc_against_sort ictx (i, SNat)
      in
        (TArr (t, i), KType)
      end
    | TProdEx ((t1, b1), (t2, b2)) =>
      let
        val t1 = kc_against_kind ctx (t1, KType)
        val t2 = kc_against_kind ctx (t2, KType)
      in
        (TProdEx ((t1, b1), (t2, b2)), KType)
      end
    | TArrowTAL (ts, i) =>
      let
        val ts = Rctx.map (fn t => kc_against_kind ctx (t, KType)) ts
        val i = sc_against_sort ictx (i, STime)
      in
        (TArrowTAL (ts, i), KType)
      end

and kc_against_kind ctx (t, k) =
  let
    val (t, k') = kc ctx t
    val () = is_eq_kind (k', k)
  in
    t
  end

(* (***************** the "subst_i_t" visitor  **********************)     *)

(* fun subst_i_ty_visitor_vtable cast ((subst_i_i, subst_i_s), d, x, v) : ('this, int, 'var, 'bsort, 'idx, 'sort, 'var, 'bsort, 'idx2, 'sort2) ty_visitor_vtable = *)
(*   let *)
(*     fun extend_i this env _ = env + 1 *)
(*     fun visit_idx this env b = subst_i_i (d + env) (x + env) v b *)
(*     fun visit_sort this env b = subst_i_s (d + env) (x + env) v b *)
(*   in *)
(*     default_ty_visitor_vtable *)
(*       cast *)
(*       extend_i *)
(*       extend_noop *)
(*       visit_noop *)
(*       visit_noop *)
(*       visit_idx *)
(*       visit_sort *)
(*   end *)

(* fun new_subst_i_ty_visitor params = new_ty_visitor subst_i_ty_visitor_vtable params *)
    
(* fun subst_i_t_fn substs d x v b = *)
(*   let *)
(*     val visitor as (TyVisitor vtable) = new_subst_i_ty_visitor (substs, d, x, v) *)
(*   in *)
(*     #visit_ty vtable visitor 0 b *)
(*   end *)

fun ictx_names ictx = map fst ictx
fun itctx_names (ictx, tctx) = (map fst ictx, map fst tctx)
fun ctx_names (ictx, tctx, ectx(* , _ *)) = (map fst ictx, map fst tctx, [], map fst ectx)
                                   
fun is_eq_ty (ctx as (ictx, tctx)) (t, t') =
    let
      val t = whnf ctx t
      val t' = whnf ctx t'
      fun t_str () = ExportPP.pp_t_to_string NONE $ ExportPP.export_t NONE (itctx_names ctx) t
      fun t'_str () = ExportPP.pp_t_to_string NONE $ ExportPP.export_t NONE (itctx_names ctx) t'
      val assert_b = fn b => flip assert_b_m b $ (fn () => sprintf "Can't unify types:\n$\nand\n$\n" [t_str (), t'_str ()])
      (* val () = println $ sprintf "comparing types:\n  $  $" [ *)
      (*       t_str (), *)
      (*       t'_str () *)
      (*     ] *)
    in
      case (t, t') of
          (TVar (x, _), TVar (x', _)) => assert_b (eq_var (x, x'))
        | (TConst c, TConst c') => assert_b (c = c')
        | (TBinOp (opr, t1, t2), TBinOp (opr', t1', t2')) =>
          let
            val () = assert_b (opr = opr')
            val () = is_eq_ty ctx (t1, t1')
            val () = is_eq_ty ctx (t2, t2')
          in
            ()
          end
        | (TArrow (t1, i, t2), TArrow (t1', i', t2')) =>
          let
            val () = is_eq_ty ctx (t1, t1')
            val () = is_eq_idx ictx (i, i')
            val () = is_eq_ty ctx (t2, t2')
          in
            ()
          end
        | (TQuanI (q, data), TQuanI (q', data')) =>
          let
            val () = assert_b (q = q')
            val (s, (name, t)) = unTQuanI data
            val (s', (_, t')) = unTQuanI data'
            val () = is_eq_sort ictx (s, s')
            val () = is_eq_ty (add_sorting_it (fst name, s) ctx) (t, t')
          in
            ()
          end
        | (TQuan (q, data), TQuan (q', data')) =>
          let
            val () = assert_b (q = q')
            val (k, (name, t)) = unTQuan data
            val (k', (_, t')) = unTQuan data'
            val () = is_eq_kind (k, k')
            val () = is_eq_ty (add_kinding_it (fst name, k) ctx) (t, t')
          in
            ()
          end
        | (TRec data, TRec data') =>
          let
            val (k, (name, t)) = unTQuan data
            val (k', (_, t')) = unTQuan data'
            val () = is_eq_kind (k, k')
            val () = is_eq_ty (add_kinding_it (fst name, k) ctx) (t, t')
          in
            ()
          end
        | (TNat i, TNat i') => is_eq_idx ictx (i, i')
        | (TArr (t, i), TArr (t', i')) =>
          let
            val () = is_eq_ty ctx (t, t')
            val () = is_eq_idx ictx (i, i')
          in
            ()
          end
        | (TAbsT data, TAbsT data') =>
          let
            val (k, (name, t)) = unTAbsT data
            val (k', (_, t')) = unTAbsT data'
            val () = is_eq_kind (k, k')
            val () = is_eq_ty (add_kinding_it (fst name, k) ctx) (t, t')
          in
            ()
          end
        | (TAppT (t1, t2), TAppT (t1', t2')) =>
          let
            val () = is_eq_ty ctx (t1, t1')
            val () = is_eq_ty ctx (t2, t2')
          in
            ()
          end
        | (TAbsI data, TAbsI data') =>
          let
            val (b, (name, t)) = unTAbsI data
            val (b', (_, t')) = unTAbsI data'
            val () = is_eq_bsort (b, b')
            val () = is_eq_ty (add_sorting_it (fst name, BasicSort b) ctx) (t, t')
          in
            ()
          end
        | (TAppI (t, i), TAppI (t', i')) =>
          let
            val () = is_eq_ty ctx (t, t')
            val () = is_eq_idx ictx (i, i')
          in
            ()
          end
        | (TProdEx ((t1, b1), (t2, b2)), TProdEx ((t1', b1'), (t2', b2'))) =>
          let
            val () = is_eq_ty ctx (t1, t1')
            val () = is_eq_ty ctx (t2, t2')
            val () = assert_b (b1 = b1')
            val () = assert_b (b2 = b2')
          in
            ()
          end
        | _ => raise MTCError $ sprintf "unknown case in is_eq_ty:\n  $  $"
                     [
                       ExportPP.pp_t_to_string NONE $ ExportPP.export_t NONE (itctx_names ctx) t,
                       ExportPP.pp_t_to_string NONE $ ExportPP.export_t NONE (itctx_names ctx) t'
                     ]
    end      

fun forget_i_t a = shift_i_t_fn (forget_i_i, forget_i_s) a
fun forget_t_t a = shift_t_t_fn forget_var a
                               
fun forget01_i_i x = forget_i_i 0 1 x
fun forget01_i_t x = forget_i_t 0 1 x
fun forget01_t_t x = forget_t_t 0 1 x

fun collect_TAppIT_rev t =
  let
    val self = collect_TAppIT_rev
  in
    case t of
        TAppI (t, i) =>
        let
          val (t, args) = self t
        in
          (t, inl i :: args)
        end
      | TAppT (t, t') =>
        let
          val (t, args) = self t
        in
          (t, inr t' :: args)
        end
      | _ => (t, [])
  end
fun collect_TAppIT t = mapSnd rev $ collect_TAppIT_rev t

fun TAppITs t args =
  foldl (fn (arg, t) => case arg of inl i => TAppI (t, i) | inr t' => TAppT (t, t')) t args

fun get_expr_const_type c =
  case c of
      ECTT => TUnit
    | ECNat n => TNat $ INat n
    | ECInt _ => TInt

fun get_prim_expr_bin_op_arg1_ty opr =
  case opr of
      PEBIntAdd => TInt
    | PEBIntMult => TInt
      
fun get_prim_expr_bin_op_arg2_ty opr =
  case opr of
      PEBIntAdd => TInt
    | PEBIntMult => TInt
      
fun get_prim_expr_bin_op_res_ty opr =
  case opr of
      PEBIntAdd => TInt
    | PEBIntMult => TInt

val T0 = T0 dummy
val T1 = T1 dummy

val shift01_i_i = shift_i_i
fun shift01_i_t a = shift_i_t 0 1 a
fun shift01_t_t a = shift_t_t 0 1 a
  
(* structure IntMap = IntBinaryMap *)
(* structure HeapMap = IntMap *)

type mtiml_ty = (Expr.var, bsort, idx, sort) ty
type lazy_ty = int ref * int ref * mtiml_ty ref
                                     
type econtext = (string * lazy_ty) list

fun new_lazy_t t = (ref 0, ref 0, ref t)
(* New refs should be created here, because the old refs may still be used later in unshifted contexts. Refs are only for avoid duplicate computations when we retrieve a variable more than once. [lazy_ty] can be defined just as [int * int * mtiml_ty], in which case every retrieval needs to perform shifting (potentially expensive). *)
fun lazy_shift_i_t n (ni, nt, t) = (ref (!ni+n), ref (!nt), ref (!t))
fun lazy_shift01_i_t a = lazy_shift_i_t 1 a
fun lazy_shift01_t_t (ni, nt, t) = (ref (!ni), ref (!nt+1), ref (!t))
fun force_t (ni_ref, nt_ref, t_ref) =
  let
    val ni = !ni_ref
    val nt = !nt_ref
    val t = !t_ref
    val changed = false
    fun trace_around _ _ f = f ()
    val (t, changed) = if nt > 0 then (trace_around "^" "$" (fn () => shift_t_t 0 nt t), true) else (t, changed)
    val (t, changed) = if ni > 0 then (trace_around "^" "$" (fn () => shift_i_t 0 ni t), true) else (t, changed)
    (* val (t, changed) = if ni > 0 then ((trace "$" o shift_i_t 0 ni o trace_noln "^") t, true) else (t, changed) *)
    val () = if changed then
               (ni_ref := 0;
                nt_ref := 0;
                t_ref := t)
             else ()
  in
    t
  end
                                                      
fun add_sorting_full new (ictx, tctx, ectx) =
    let
      val ret = 
          (new :: ictx, tctx, map (mapSnd (lazy_shift01_i_t (* o trace_noln "." *))) ectx)
      (* val () = println "" *)
    in
      ret
    end
fun add_kinding_full new (ictx, tctx, ectx) = (ictx, new :: tctx, map (mapSnd lazy_shift01_t_t) ectx)
fun add_typing_full (name, t) (ictx, tctx, ectx) = (ictx, tctx, (name, new_lazy_t t) :: ectx)

open Unbound
       
fun eval_constr_expr_visitor_vtable cast () =
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
    fun visit_EAppConstr this env (e1, ts, is, e2) =
      let
        val vtable = cast this
        val e1 = #visit_expr vtable this env e1
        val ts = map (#visit_ty vtable this env) ts
        val is = map (#visit_idx vtable this env) is
        val e2 = #visit_expr vtable this env e2
      in
        case e1 of
            EAbsConstr data =>
            let
              val ((tnames, inames, ename), e) = unBind data
              val di = length is
              val e = fst $ foldl (fn (v, (b, dt)) => (subst_t_e (IDepth di, TDepth dt) dt v b, dt - 1)) (e, length ts - 1) ts
              val e = fst $ foldl (fn (v, (b, di)) => (subst_i_e di di v b, di - 1)) (e, di - 1) is
              val e = subst0_e_e e2 e
            in
              #visit_expr vtable this env e
            end
          | _ => EAppConstr (e1, ts, is, e2)
      end
    val vtable = override_visit_EAppConstr vtable visit_EAppConstr
  in
    vtable
  end

fun new_eval_constr_expr_visitor params = new_expr_visitor eval_constr_expr_visitor_vtable params
    
fun eval_constr b =
  let
    val visitor as (ExprVisitor vtable) = new_eval_constr_expr_visitor ()
  in
    #visit_expr vtable visitor () b
  end

fun assert_cons ls =
    case ls of
        x :: xs => (x, xs)
      | [] => raise Impossible "assert_cons fails"

fun smart_EAscType (e, t) =
    let
      val (e, is) = collect_EAscTime e
      val e = 
          case e of
              EAscType (e, _) => e
            | _ => e
      val e = EAscTimes (e, is)
      val e = EAscType (e, t)
    in
      e
    end
      
infix 0 %:
fun a %: b = smart_EAscType (a, b)
infix 0 |>
fun a |> b = EAscTime (a, b)

val anno_EVar = ref false
val anno_EProj = ref false
val anno_EFold = ref false
val anno_EUnfold = ref false
val anno_EApp = ref false
val anno_EPair = ref false
val anno_EBPrim = ref false
val anno_ENew = ref false
val anno_ERead = ref false
val anno_ENatAdd = ref false
val anno_EWrite = ref false
val anno_ECase = ref false
val anno_EAbs = ref false
val anno_EAppT = ref false
val anno_EAppI = ref false
val anno_EPack = ref false
val anno_EPackI = ref false
val anno_EUnpack = ref false
val anno_EUnpackI = ref false
val anno_ELet = ref false
           
fun tc (ctx as (ictx, tctx, ectx : econtext)) e_input =
  let
    (* val () = print "tc() start: " *)
    (* val e_input_str = (* substr 0 100 $  *)ExportPP.pp_e_to_string (NONE, NONE) $ ExportPP.export (SOME 1, SOME 1) (ctx_names ctx) e_input *)
    (* val () = print $ e_input_str *)
    val itctx = (ictx, tctx)
    fun main () =
        case e_input of
        EVar x =>
        (case nth_error_local ectx x of
             SOME (_, t) =>
             let
               val t = force_t t
               val e = e_input
               val e = if !anno_EVar then e %: t else e
             in
               (e, t, T0)
             end
           | NONE => raise MTCError "Unbound term variable"
        )
      | EConst c => (e_input, get_expr_const_type c, T0)
      (* | ELoc l => *)
      (*   (case HeapMap.find (hctx, l) of *)
      (*        SOME (t, i) => (e_input, TArr (t, i), T0) *)
      (*      | NONE => raise MTCError "Unbound location" *)
      (*   ) *)
      | EUnOp (EUProj proj, e) =>
        let
          val (e, t_e, i) = tc ctx e
          val t_e = whnf itctx t_e
          val (t1, t2) = case t_e of
                             TBinOp (TBProd, t1, t2) => (t1, t2)
                           | _ => raise MTCError "EProj"
          val e = if !anno_EProj then e %: t_e else e
        in
          (EProj (proj, e), choose (t1, t2) proj, i)
        end
      | EUnOp (EUInj (inj, t'), e) =>
        let
          val t' = kc_against_kind itctx (t', KType)
          val (e, t, i) = tc ctx e
          fun inject (t, t') inj =
            case inj of
                InjInl => (t, t')
              | InjInr => (t', t)
        in
          (EInj (inj, t', e), TSum $ inject (t, t') inj, i)
        end
      | EUnOp (EUFold t', e) =>
        let
          val t' = kc_against_kind itctx (t', KType)
          val t' = whnf itctx t'
          val (t, args) = collect_TAppIT t'
          val (k, (_, t1)) = case t of
                                 TRec data => unBindAnnoName data
                               | _ => raise MTCError "EFold"
          val t = TAppITs (subst0_t_t t t1) args
          (* val () = println "EFold: before tc_against_ty" *)
          (* val () = println $ "EFold: " ^ (ExportPP.pp_t_to_string $ ExportPP.export_t (itctx_names itctx) t) *)
          val (e, i) = tc_against_ty ctx (e, t) 
          (* val () = println "EFold: after tc_against_ty" *)
          val e = if !anno_EFold then e %: t else e
        in
          (EFold (t', e), t', i)
        end
      | EUnOp (EUUnfold, e) =>
        let
          val (e, t_e, i) = tc ctx e
          val t_e = whnf itctx t_e
          val (t, args) = collect_TAppIT t_e
          val (k, (_, t1)) = case t of
                                 TRec data => unBindAnnoName data
                               | _ => raise MTCError "EUnfold"
          val e = if !anno_EUnfold then e %: t_e else e
        in
          (EUnfold e, TAppITs (subst0_t_t t t1) args, i)
        end
      | EBinOp (EBApp, e1, e2) =>
        let
          val (e1, t_e1, i1) = tc ctx e1
          val t_e1 = whnf itctx t_e1
          val (t1, i, t2) = case t_e1 of
                                TArrow data => data
                              | _ => raise MTCError "EApp"
          val (e2, i2) = tc_against_ty ctx (e2, t1)
          val e1 = if !anno_EApp then e1 %: t_e1 else e1
        in
          (EApp (e1, e2), t2, i1 %+ i2 %+ T1 %+ i)
        end
      | EBinOp (EBPair, e1, e2) =>
        let
          val (e1, t1, i1) = tc ctx e1
          val (e2, t2, i2) = tc ctx e2
          val (e1, e2) = if !anno_EPair then (e1 %: t1, e2 %: t2) else (e1, e2)
        in
          (EPair (e1, e2), TProd (t1, t2), i1 %+ i2)
        end
      | EBinOp (EBPrim opr, e1, e2) =>
        let
          val (e1, t1, i1) = tc ctx e1
          val () = is_eq_ty itctx (t1, get_prim_expr_bin_op_arg1_ty opr)
          val (e2, t2, i2) = tc ctx e2
          val () = is_eq_ty itctx (t2, get_prim_expr_bin_op_arg2_ty opr)
          val (e1, e2) = if !anno_EBPrim then (e1 %: t1, e2 %: t2) else (e1, e2)
        in
          (EBinOpPrim (opr, e1, e2), get_prim_expr_bin_op_res_ty opr, i1 %+ i2)
        end
      | EBinOp (EBNew, e1, e2) =>
        let
          val (e1, t1, j1) = tc ctx e1
          val t1 = whnf itctx t1
          val i = case t1 of
                      TNat i => i
                    | _ => raise MTCError "ENew"
          val (e2, t2, j2) = tc ctx e2
          val (e1, e2) = if !anno_ENew then (e1 %: t1, e2 %: t2) else (e1, e2)
        in
          (ENew (e1, e2), TArr (t2, i), j1 %+ j2)
        end
      | EBinOp (EBRead, e1, e2) =>
        let
          val (e1, t1, j1) = tc ctx e1
          val (t, i1) = case whnf itctx t1 of
                            TArr data => data
                          | _ => raise MTCError "ERead 1"
          val (e2, t2, j2) = tc ctx e2
          val t2 = whnf itctx t2
          val i2 = case t2 of
                       TNat i => i
                     | _ => raise MTCError "ERead 2"
          val () = check_prop ictx (i2 %< i1)
          val (e1, e2) = if !anno_ERead then (e1 %: t1, e2 %: t2) else (e1, e2)
        in
          (ERead (e1, e2), t, j1 %+ j2)
        end
      | EBinOp (EBNatAdd, e1, e2) =>
        let
          val (e1, t1, j1) = tc ctx e1
          val t1 = whnf itctx t1
          val i1 = case t1 of
                       TNat i => i
                     | _ => raise MTCError "ENatAdd 1"
          val (e2, t2, j2) = tc ctx e2
          val t2 = whnf itctx t2
          val i2 = case t2 of
                       TNat i => i
                     | _ => raise MTCError "ENatAdd 2"
          val (e1, e2) = if !anno_ENatAdd then (e1 %: t1, e2 %: t2) else (e1, e2)
        in
          (ENatAdd (e1, e2), TNat (i1 %+ i2), j1 %+ j2)
        end
      | EWrite (e1, e2, e3) =>
        let
          val (e1, t1, j1) = tc ctx e1
          val t1 = whnf itctx t1
          val (t, i1) = case t1 of
                            TArr data => data
                          | _ => raise MTCError "ERead 1"
          val (e2, t2, j2) = tc ctx e2
          val t2 = whnf itctx t2
          val i2 = case t2 of
                       TNat i => i
                     | _ => raise MTCError "ERead 2"
          val () = check_prop ictx (i2 %< i1)
          val (e3, j3) = tc_against_ty ctx (e3, t)
          val (e1, e2, e3) = if !anno_EWrite then (e1 %: t1, e2 %: t2, e3 %: t) else (e1, e2, e3)
        in
          (EWrite (e1, e2, e3), TUnit, j1 %+ j2 %+ j3)
        end
      | ECase data =>
        let
          val (e, (name1, e1), (name2, e2)) = unECase data
          val (e, t_e, i) = tc ctx e
          val t_e = whnf itctx t_e
          val (t1, t2) = case t_e of
                             TBinOp (TBSum, t1, t2) => (t1, t2)
                           | _ => raise MTCError $ "ECase: " ^ (ExportPP.pp_t_to_string NONE $ ExportPP.export_t NONE (map fst ictx, map fst tctx) t_e)
          val (e1, t1, i1) = tc (add_typing_full (fst name1, t1) ctx) e1
          val (e2, t2, i2) = tc (add_typing_full (fst name2, t2) ctx) e2
          val () = is_eq_ty itctx (t1, t2)
          val e = if !anno_ECase then e %: t_e else e
        in
          (MakeECase (e, (name1, e1), (name2, e2)), t1, i %+ IMax (i1, i2))
        end
      | EAbs data =>
        let
          val (t1 : mtiml_ty, (name, e)) = unEAbs data
          val t1 = kc_against_kind itctx (t1, KType)
          val (e, t2, i) = tc (add_typing_full (fst name, t1) ctx) e
          val e = if !anno_EAbs then e %: t2 |> i else e
          val e = MakeEAbs (name, t1, e)
        in
          (e, TArrow (t1, i, t2), T0)
        end
      | ERec data =>
        let
          val (t, (name, e)) = unBindAnnoName data
          val () = println $ "tc() on: " ^ fst name
          val () = case snd $ collect_EAbsIT e of
                       EAbs _ => ()
                     | _ => raise MTCError "ERec: body should be EAbsITMany (EAbs (...))"
          val t = kc_against_kind itctx (t, KType)
          val e = tc_against_ty_time (add_typing_full (fst name, t) ctx) (e, t, T0)
        in
          (MakeERec (name, t, e), t, T0)
        end
      | EAbsT data =>
        let
          val (k, (name, e)) = unEAbsT data
          val () = assert_b "EAbsT: is_value e" (is_value e)
          val (e, t) = tc_against_time (add_kinding_full (fst name, k) ctx) (e, T0)
        in
          (MakeEAbsT (name, k, e), MakeTForall (k, name, t), T0)
        end
      | EAbsI _ =>
        let
          (* val () = println "tc() on EAbsI" *)
          val (binds, e) = collect_EAbsI e_input
          val regions = map (snd o fst) binds
          val binds = map (mapFst fst) binds
          (* val () = println "before tc()/EAbsI/is_wf_sorts()" *)
          fun is_wf_sorts ctx binds =
              let
                fun foo ((name, s), (binds, ctx)) =
                    let
                      val s = is_wf_sort ctx s
                      val bind = (name, s)
                    in
                      (bind :: binds, bind :: ctx)
                    end
                val (binds, ctx) = foldl foo ([], ctx) binds
                val binds = rev binds
              in
                (binds, ctx)
              end
          val (binds, ictx) = is_wf_sorts ictx binds
          (* val () = println "before tc()/EAbsI/is_value()" *)
          val () = assert_b "EAbsI: is_value e" (is_value e)
          (* val () = println "before tc()/EAbsI/add_sortings_full()" *)
          (* val () = println $ sprintf "#ictx=$  #ectx=$" [str_int $ length ictx, str_int $ length ectx] *)
          val len_binds = length binds
          val ectx = map (mapSnd (lazy_shift_i_t len_binds (* o trace_noln "." *))) ectx
          (* val () = println "" *)
          val ctx = (ictx, tctx, ectx)
          (* val () = println "before tc()/EAbsI/tc_against_time()" *)
          val (e, t) = tc_against_time ctx (e, T0)
          (* val () = println "before tc()/EAbsI/making result" *)
          val binds = ListPair.mapEq (fn ((name, anno), r) => ((name, r), anno)) (binds, regions)
          val result = (EAbsIs (binds, e), TForallIs (binds, t), T0)
          (* val () = println "after tc()/EAbsI/making result" *)
        in
          result
        end
      (* | EAbsI data => *)
      (*   let *)
      (*     val () = println "tc() on EAbsI" *)
      (*     val (s, (name, e)) = unEAbsI data *)
      (*     val () = println "before is_wf_sort()" *)
      (*     val s = is_wf_sort ictx s *)
      (*     val () = println "before is_value()" *)
      (*     val () = assert_b "EAbsI: is_value e" (is_value e) *)
      (*     val () = println "before add_sorting_full()" *)
      (*     val () = println $ sprintf "#ictx=$  #ectx=$" [str_int $ length ictx, str_int $ length ectx] *)
      (*     val ctx = add_sorting_full (fst name, s) ctx *)
      (*     val () = println "before tc_against_time()" *)
      (*     val (e, t) = tc_against_time ctx (e, T0) *)
      (*     val () = println "before making result" *)
      (*     val result = (MakeEAbsI (name, s, e), MakeTForallI (s, name, t), T0) *)
      (*     val () = println "after making result" *)
      (*   in *)
      (*     result *)
      (*   end *)
      | EAppT (e, t1) =>
        let
          val (e, t_e, i) = tc ctx e
          val t_e = whnf itctx t_e
          val (_, (_, t)) = case t_e of
                                TQuan (Forall, data) => unTQuan data
                              | _ => raise MTCError "EAppT"
          val t1 = kc_against_kind itctx (t1, KType)
          val e = if !anno_EAppT then e %: t_e else e
        in
          (EAppT (e, t1), subst0_t_t t1 t, i)
        end
      | EAppI (e, i) =>
        let
          val (e, t_e, j) = tc ctx e
          val t_e = whnf itctx t_e
          val (s, (_, t)) = case t_e of
                                TQuanI (Forall, data) => unTQuanI data
                              | _ => raise MTCError "EAppT"
          val i = sc_against_sort ictx (i, s)
          val e = if !anno_EAppI then e %: t_e else e
        in
          (EAppI (e, i), subst0_i_t i t, j)
        end
      | EPack (t', t1, e) =>
        let
          val t' = kc_against_kind itctx (t', KType)
          val t' = whnf itctx t'
          val (k, (_, t)) = case t' of
                                TQuan (Exists _, data) => unTQuan data
                              | _ => raise MTCError "EPack"
          val t1 = kc_against_kind itctx (t1, k)
          val t_e = subst0_t_t t1 t
          val (e, i) = tc_against_ty ctx (e, t_e)
          val e = if !anno_EPack then e %: t_e else e
        in
          (EPack (t', t1, e), t', i)
        end
      | EPackI (t', i, e) =>
        let
          val t' = kc_against_kind itctx (t', KType)
          val t' = whnf itctx t'
          val (s, (_, t)) = case t' of
                                TQuanI (Exists _, data) => unTQuanI data
                              | _ => raise MTCError "EPackI"
          val i = sc_against_sort ictx (i, s)
          val t_e = subst0_i_t i t
          val (e, j) = tc_against_ty ctx (e, t_e)
          val e = if !anno_EPackI then e %: t_e else e
        in
          (EPackI (t', i, e), t', j)
        end
      | EUnpack data =>
        let
          val (e1, (tname, ename, e2)) = unEUnpack data
          val (e1, t_e1, i1) = tc ctx e1
          val t_e1 = whnf itctx t_e1
          val (k, (_, t)) = case t_e1 of
                                TQuan (Exists _, data) => unTQuan data
                              | _ => raise MTCError "EUnpack"
          val (e2, t2, i2) = tc (add_typing_full (fst ename, t) $ add_kinding_full (fst tname, k) ctx) e2
          (* val () = println $ "trying to forget: " ^ (ExportPP.pp_t_to_string $ ExportPP.export_t (itctx_names $ add_kinding_it (tname, k) itctx) t2) *)
          val t2 = forget01_t_t t2
          (* val () = println "forget finished" *)
          val e1 = if !anno_EUnpack then e1 %: t_e1 else e1
        in
          (MakeEUnpack (e1, tname, ename, e2), t2, i1 %+ i2)
        end
      | EUnpackI data =>
        let
          val (e1, (iname, ename, e2)) = unEUnpack data
          val (e1, t_e1, i1) = tc ctx e1
          fun mismatch header got expect =
            sprintf "Mismatch when checking %:\n  got:    $\n  expect: $\n" [header, got, expect]
          val t_e1 = whnf itctx t_e1
          val (s, (_, t)) = case t_e1 of
                                TQuanI (Exists _, data) => unTQuanI data
                              | _ => raise MTCError $ mismatch "EUnpackI" (ExportPP.pp_t_to_string NONE $ ExportPP.export_t NONE (itctx_names itctx) t_e1) "TQuanI (Exists, _)"
          val (e2, t2, i2) = tc (add_typing_full (fst ename, t) $ add_sorting_full (fst iname, s) ctx) e2
          val t2 = forget01_i_t t2
                   handle ForgetError (r, m) => raise ForgetError (r, m ^ " when forgetting type: " ^ (ExportPP.pp_t_to_string NONE $ ExportPP.export_t NONE (itctx_names $ add_sorting_it (fst iname, s) itctx) t2))
          val i2 = forget01_i_i i2
                   handle ForgetError (r, m) => raise ForgetError (r, m ^ " when forgetting time: " ^ (ToString.SN.strn_i $ ExportPP.export_i (fst iname :: map fst ictx) i2))
          val e1 = if !anno_EUnpackI then e1 %: t_e1 else e1
        in
          (MakeEUnpackI (e1, iname, ename, e2), t2, i1 %+ i2)
        end
      | EPackIs (t, is, e) =>
        let
          val t = kc_against_kind itctx (t, KType)
        in
          case is of
              [] =>
              let
                val (e, i) = tc_against_ty ctx (e, t)
              in
                (e, t, i)
              end
            | i :: is =>
              let
                val (_, (_, t')) = case whnf itctx t of
                                      TQuanI (Exists _, data) => unTQuanI data
                                    | _ => raise MTCError "EPackIs"
              in
                tc ctx $ EPackI (t, i, EPackIs (subst0_i_t i t', is, e))
              end
        end
      | EAscTime (e, i) =>
        let
          val (e, ts) = collect_EAscType e
          val i = sc_against_sort ictx (i, STime)
        in
          (* propagate time annotations *)
          case e of
              ELet data =>
              let
                val (e1, (name, e2)) = unELet data
                val (e1, t1, i1) = tc ctx e1
                val e2 = EAscTypes (e2, ts)
                val e2 = EAscTime (e2, BinOpI (MinusI, i, i1))
                val (e2, t2, _) = tc (add_typing_full (fst name, t1) ctx) e2
                val e1 = if !anno_ELet then e1 %: t1 else e1
                val e = MakeELet (e1, name, e2)
              in
                (e |> i, t2, i)
              end
            | _ =>
              let
                val e = case e of
                            EUnpackI data =>
                            let
                              val (e1, (iname, ename, e2)) = unEUnpack data
                              val e2 = if is_value e1 then EAscTime (e2, shift_i_i i) else e2
                            in
                              MakeEUnpackI (e1, iname, ename, e2)
                            end
                          | _ => e
                val e = EAscTypes (e, ts)
                val (e, t, i1) = tc ctx e
                val i = sc_against_sort ictx (i, STime)
                fun check_le_with_subtractions ictx (i, i') =
                  let
                    val collect_MinusI_left = collect_BinOpI_left MinusI
                    val (i', is) = assert_cons $ collect_MinusI_left i'
                    val i = combine_AddI_nonempty i is
                    val () = check_prop ictx (i %<= i')
                  in
                    ()
                  end
                val () = check_le_with_subtractions ictx (i1, i)
              in
                (e |> i, t, i)
              end
        end
      | EAscType (e, t2) =>
        let
          (* val () = println "tc() on EAscType" *)
          val (e, t1, i) = tc ctx e
          val t2 = kc_against_kind itctx (t2, KType)
          (* val () = println "before tc()/EAscType/is_eq_ty()" *)
          val () = is_eq_ty itctx (t1, t2)
          (* val () = println "after tc()/EAscType/is_eq_ty()" *)
        in
          (e %: t2, t2, i)
        end
      | ENever t =>
        let
          val t = kc_against_kind itctx (t, KType)
          val () = check_prop ictx (False dummy)
        in
          (ENever t, t, T0)
        end
      | EBuiltin t =>
        let
          val t = kc_against_kind itctx (t, KType)
        in
          (EBuiltin t, t, T0)
        end
      (* | ELet data => *)
      (*   let *)
      (*     val (e1, (name, e2)) = unELet data *)
      (*     val (e1, t1, i1) = tc ctx e1 *)
      (*     val (e2, t2, i2) = tc (add_typing_full (fst name, t1) ctx) e2 *)
      (*   in *)
      (*     (MakeELet (e1 %: t1, name, e2), t2, i1 %+ i2) *)
      (*   end *)
      | ELet _ =>
        let
          val (decls, e) = collect_ELet e_input
          fun foo ((name, e), (decls, ctx)) =
              let
                val (e, t, i) = tc ctx e
                val e = if !anno_ELet then e %: t else e
                val decl = ((name, e), i)
                val decls = decl :: decls
                val ctx = add_typing_full (fst name, t) ctx
              in
                (decls, ctx)
              end
          val (decls, ctx) = foldl foo ([], ctx) decls
          val decls = rev decls
          val (decls, is) = unzip decls 
          val (e, t, i) = tc ctx e
          val e = ELets (decls, e)
          val is = uncurry combine_AddI_nonempty $ assert_cons is
        in
          (e, t, is %+ i)
        end
      | ELetType data =>
        let
          val (t, (name, e)) = unELetType data
          val _ = kc itctx t
        in
          tc ctx $ subst0_t_e t e (* todo: record type aliasing in ctx *)
        end
      | ELetIdx data =>
        let
          val (i, (name, e)) = unELetIdx data
          val (i, _) = sc ictx i
        in
          tc ctx $ subst0_i_e i e (* todo: record index aliasing in ctx *)
        end
      | ELetConstr data =>
        let
          val (e1, (name, e2)) = unELetConstr data
          val e = subst0_c_e e1 e2
          (* val () = println "After subst0_c_e:" *)
          (* val () = println $ ExportPP.pp_e_to_string $ ExportPP.export (ctx_names ctx) e *)
          val e = eval_constr e
        in
          tc ctx e
        end
      | EMallocPair (a, b) =>
        let
          val () = assert_b "EMallocPair: is_value a" (is_value a)
          val () = assert_b "EMallocPair: is_value b" (is_value b)
          val (a, t1, _) = tc ctx a
          val (b, t2, _) = tc ctx b
        in
          (EMallocPair (a, b), TProdEx ((t1, false), (t2, false)), T0)
        end
      | EPairAssign (e1, proj, e2) =>
        let
          val (e1, t_e1, i_e1) = tc ctx e1
          val ((t1, b1), (t2, b2)) =
              case t_e1 of
                  TProdEx a => a
                | _ => raise MTCError "EPairAssign/assert-TProdEx"
          val t_e2 = choose (t1, t2) proj
          val (e2, i_e2) = tc_against_ty ctx (e2, t_e2)
          val (b1, b2) = case proj of
                             ProjFst => (true, b2)
                           | ProjSnd => (b1, true)
        in
          (EPairAssign (e1, proj, e2), TProdEx ((t1, b1), (t2, b2)), i_e1 %+ i_e2)
        end
      | EProjProtected (proj, e) =>
        let
          val (e, t_e, i_e) = tc ctx e
          val ts =
              case t_e of
                  TProdEx a => a
                | _ => raise MTCError "EProjProtected/assert-TProdEx"
          val (t, b) = choose ts proj
          val () = if b then ()
                   else raise MTCError "EProjProtected/check-permission"
        in
          (EProjProtected (proj, e), t, i_e)
        end
      | EHalt e =>
        let
          val (e, t_e, i_e) = tc ctx e
        in
          (EHalt e, TUnit, i_e)
        end
      | _ => raise Impossible $ "unknown case in tc: " ^ (ExportPP.pp_e_to_string (NONE, NONE) $ ExportPP.export (NONE, NONE) (ctx_names ctx) e_input)
    fun extra_msg () = "\nwhen typechecking\n" ^ ((* substr 0 300 $  *)ExportPP.pp_e_to_string (NONE, NONE) $ ExportPP.export (SOME 2, SOME 5) (ctx_names ctx) e_input)
    val (e_output, t, i) = main ()
                 handle ForgetError (r, m) => raise MTCError ("Forgetting error: " ^ m ^ extra_msg ())
                      | MSCError (r, m) => raise MTCError ("Sortcheck error:\n" ^ join_lines m ^ extra_msg ())
                      | MUnifyError (r, m) => raise MTCError ("Unification error:\n" ^ join_lines m ^ extra_msg ())
                      | MTCError m => raise MTCError (m ^ extra_msg ())
                      | Impossible m => raise Impossible (m ^ extra_msg ())
    (* val () = println "tc() finished:" *)
    (* val () = println $ e_input_str *)
    (* val () = println "of type:" *)
    (* val () = println $ (* substr 0 100 $  *)ExportPP.pp_t_to_string $ ExportPP.export_t (itctx_names (ictx, tctx)) t *)
    (* val () = println "of time:" *)
    (* val () = println $ (* substr 0 100 $  *)ExportPP.str_i $ ExportPP.export_i (ictx_names ictx) i *)
  in
    (e_output, t, i)
  end

and tc_against_ty (ctx as (ictx, tctx, _(* , _ *))) (e, t) =
    let
      (* val () = print "tc_against_ty() start:\n" *)
      (* val e_str = substr 0 100 $ ExportPP.pp_e_to_string $ ExportPP.export (ctx_names ctx) e *)
      (* val t_str = substr 0 100 $ ExportPP.pp_t_to_string $ ExportPP.export_t (itctx_names (ictx, tctx)) t *)
      (* val () = println $ sprintf "  $\n  $\n" [ *)
      (*       e_str, *)
      (*       t_str *)
      (*     ] *)
      val (e, t', i) = tc ctx e
      (* val () = print "tc_against_ty() to compare types:\n" *)
      (* val () = println $ sprintf "  $\n  $\n" [ *)
      (*       substr 0 100 $ ExportPP.pp_t_to_string $ ExportPP.export_t (itctx_names (ictx, tctx)) t', *)
      (*       t_str *)
      (*     ] *)
      (* val () = println "before tc_against_ty()/is_eq_ty()" *)
      val () = is_eq_ty (ictx, tctx) (t', t)
      (* val () = println "tc_against_ty() finished:" *)
      (* val () = println e_str *)
    in
      (e, i)
    end
    
and tc_against_time (ctx as (ictx, tctx, _(* , _ *))) (e, i) =
    let
      (* val () = print "tc_against_time() start:\n" *)
      (* val e_str = substr 0 100 $ ExportPP.pp_e_to_string $ ExportPP.export (ctx_names ctx) e *)
      (* val () = println e_str *)
      val (e, t, i') = tc ctx e
      (* val () = println "before tc_against_time()/check_prop()" *)
      val () = check_prop ictx (i' %<= i)
      (* val () = println "tc_against_time() finished:" *)
      (* val () = println e_str *)
    in
      (e, t)
    end
    
and tc_against_ty_time (ctx as (ictx, tctx, _)) (e, t, i) =
    let
      (* val () = print "tc_against_ty_time() start:\n" *)
      (* val e_str = substr 0 100 $ ExportPP.pp_e_to_string $ ExportPP.export (ctx_names ctx) e *)
      (* val () = println e_str *)
      val (e, t') = tc_against_time ctx (e, i)
      (* val () = print "tc_against_ty_time() to compare types:\n" *)
      (* val t_str = substr 0 100 $ ExportPP.pp_t_to_string $ ExportPP.export_t (itctx_names (ictx, tctx)) t *)
      (* val () = println $ sprintf "  $\n  $\n" [ *)
      (*       substr 0 100 $ ExportPP.pp_t_to_string $ ExportPP.export_t (itctx_names (ictx, tctx)) t', *)
      (*       t_str *)
      (*     ] *)
      (* val () = println "before tc_against_ty_time()/is_eq_ty()" *)
      val () = is_eq_ty (ictx, tctx) (t', t)
      (* val () = println "tc_against_ty_time() finished:" *)
      (* val () = println e_str *)
    in
      e
    end

fun sort_to_hyps (name, s) =
  case s of
      Basic (b, r) => [VarH (name, b)]
    | Subset ((b, _), Bind.Bind (_, p), _) => [PropH p, VarH (name, b)]
    | _ => raise Impossible "sort_to_hyps"
      
fun to_vc (ctx, p) = (concatMap sort_to_hyps ctx, p)
  
fun runWriter m () =
  let 
    val () = vcs := []
    val () = admits := []
    val r = m ()
    (* val () = println "after m ()" *)
    val vcs = !vcs
    val admits = !admits
    val vcs = map to_vc vcs
    (* val () = println "after to_vc; calling simp_vc_vcs" *)
    (* val () = app println $ concatMap (fn ls => ls @ [""]) $ map (str_vc false "") vcs *)
    val vcs_len = length vcs
    (* val () = println $ "#VCs: " ^ str_int vcs_len *)
    (* val vcs = concatMapi (fn (i, vc) => (println (sprintf "vc $ @ $" [str_int vcs_len, str_int i]); simp_vc_vcs vc)) vcs *)
    (* val () = println "before simp vcs" *)
    (* val vcs = map VC.simp_vc vcs *)
    (* val () = println "after simp vcs" *)
    (* val vcs = TrivialSolver.simp_and_solve_vcs vcs *)
    val admits = map to_vc admits
  in 
    (r, vcs, admits) 
  end
    
datatype tc_flags =
         AnnoEVar
       | AnnoEProj
       | AnnoEFold
       | AnnoEUnfold
       | AnnoEApp
       | AnnoEPair
       | AnnoEBPrim
       | AnnoENew
       | AnnoERead
       | AnnoENatAdd
       | AnnoEWrite
       | AnnoECase
       | AnnoEAbs
       | AnnoEAppT
       | AnnoEAppI
       | AnnoEPack
       | AnnoEPackI
       | AnnoEUnpack
       | AnnoEUnpackI
       | AnnoELet

fun typecheck flags ctx e =
  let
    val mem = fn (a : tc_flags) => mem op= a
    val () = anno_EVar := mem AnnoEVar flags
    val () = anno_EProj := mem AnnoEProj flags
    val () = anno_EFold := mem AnnoEFold flags
    val () = anno_EUnfold := mem AnnoEUnfold flags
    val () = anno_EApp := mem AnnoEApp flags
    val () = anno_EPair := mem AnnoEPair flags
    val () = anno_EBPrim := mem AnnoEBPrim flags
    val () = anno_ENew := mem AnnoENew flags
    val () = anno_ERead := mem AnnoERead flags
    val () = anno_ENatAdd := mem AnnoENatAdd flags
    val () = anno_EWrite := mem AnnoEWrite flags
    val () = anno_ECase := mem AnnoECase flags
    val () = anno_EAbs := mem AnnoEAbs flags
    val () = anno_EAppT := mem AnnoEAppT flags
    val () = anno_EAppI := mem AnnoEAppI flags
    val () = anno_EPack := mem AnnoEPack flags
    val () = anno_EPackI := mem AnnoEPackI flags
    val () = anno_EUnpack := mem AnnoEUnpack flags
    val () = anno_EUnpackI := mem AnnoEUnpackI flags
    val () = anno_ELet := mem AnnoELet flags
    val ret = runWriter (fn () => tc ctx e) ()
  in
    ret
  end

structure UnitTest = struct

structure TestUtil = struct

open LongId
open Util
open MicroTiML
open MicroTiMLVisitor
open MicroTiMLExLongId
open MicroTiMLEx
       
fun fail () = OS.Process.exit OS.Process.failure
                   
end

open TestUtil

infixr 0 $
infixr 0 !!
         
fun test1 dirname =
  let
    val () = println "MicroTiMLTypecheck.UnitTest started"
    val filename = join_dir_file (dirname, "micro-timl-tc-test1.pkg")
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
    open ExportPP
    val () = pp_e (NONE, NONE) $ export (NONE, NONE) ToStringUtil.empty_ctx e
    val () = println ""
    open TestUtil
    open ExportPP
    val () = println "Started MicroTiML typechecking ..."
    val ((_, t, i), vcs, admits) = typecheck [] ([], [], [](* , HeapMap.empty *)) e
    val () = println "Finished MicroTiML typechecking"
    val () = println "Type:"
    val () = pp_t NONE $ export_t NONE ([], []) t
    val () = println "Time:"
    val i = simp_i i
    val () = println $ ToString.str_i Gctx.empty [] i
    val () = println $ "#VCs: " ^ str_int (length vcs)
    (* val () = println "VCs:" *)
    (* val () = app println $ concatMap (fn ls => ls @ [""]) $ map (str_vc false "") vcs *)
    val () = println "MicroTiMLTypecheck.UnitTest passed"
  in
    ((* t, e *))
  end
  handle MTCError msg => (println $ "MTiMLTC.MTCError: " ^ substr 0 1000 msg; fail ())
       | TypeCheck.Error (_, msgs) => (app println $ "TC.Error: " :: msgs; fail ())
       | NameResolve.Error (_, msg) => (println $ "NR.Error: " ^ msg; fail ())
    
val test_suites = [
      test1
]
                            
end
                                 
end
