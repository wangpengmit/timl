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
                 
fun check_prop ctx p = push_ref vcs (ctx, p)
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
fun sc_against_sort ctx (i, s) = ignore $ check_sort Gctx.empty (ctx, i, s)

fun is_wf_sort ctx s = ignore $ Sortcheck.is_wf_sort Gctx.empty (ctx, s)

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

fun kc (ctx as (ictx, tctx) : icontext * tcontext) t : bsort kind =
  case t of
      TVar x =>
      (case nth_error_local tctx x of
           SOME (_, k) => k
         | NONE => raise MTCError "unbound type variable"
      )
    | TConst c => get_ty_const_kind c
    | TBinOp (opr, t1, t2) =>
      let
        val () = kc_against_kind ctx (t1, get_ty_bin_op_arg1_kind opr)
        val () = kc_against_kind ctx (t2, get_ty_bin_op_arg2_kind opr)
      in
        get_ty_bin_op_res_kind opr
      end
    | TArrow (t1, i, t2) =>
      let
        val () = kc_against_kind ctx (t1, KType)
        val () = sc_against_sort ictx (i, STime)
        val () = kc_against_kind ctx (t2, KType)
      in
        KType
      end
    | TAbsI data =>
      let
        val (b, (name, t)) = unTAbsI data
        val k = kc (add_sorting_it (fst name, BasicSort b) ctx) t
      in
        KArrow (b, k)
      end
    | TAppI (t, i) =>
      let
        val k' = kc ctx t
        val (b, k) = case k' of
                         KArrow data => data
                       | _ => raise MTCError "TAppI"
        val () = sc_against_sort ictx (i, BasicSort b)
      in
        k
      end
    | TAbsT data =>
      let
        val (k1, (name, t)) = unTAbsT data
        val k2 = kc (add_kinding_it (fst name, k1) ctx) t
      in
        KArrowT (k1, k2)
      end
    | TAppT (t1, t2) =>
      let
        val k' = kc ctx t1
        val (k1, k2) = case k' of
                         KArrowT data => data
                       | _ => raise MTCError "TAppT"
        val () = kc_against_kind ctx (t2, k1)
      in
        k2
      end
    | TQuanI (_, data) =>
      let
        val (s, (name, t)) = unTQuanI data
        val () = is_wf_sort ictx s
        val () = kc_against_kind (add_sorting_it (fst name, s) ctx) (t, KType)
      in
        KType
      end
    | TQuan (_, data) =>
      let
        val (k, (name, t)) = unTQuan data
        val () = kc_against_kind (add_kinding_it (fst name, k) ctx) (t, KType)
      in
        KType
      end
    | TRec data =>
      let
        val (k, (name, t)) = unBindAnnoName data
        val () = kc_against_kind (add_kinding_it (fst name, k) ctx) (t, k)
      in
        k
      end
    | TNat i =>
      let
        val () = sc_against_sort ictx (i, SNat)
      in
        KType
      end
    | TArr (t, i) =>
      let
        val () = kc_against_kind ctx (t, KType)
        val () = sc_against_sort ictx (i, SNat)
      in
        KType
      end

and kc_against_kind ctx (t, k) =
  let
    val k' = kc ctx t
    val () = is_eq_kind (k', k)
  in
    ()
  end

(***************** the "subst_i_t" visitor  **********************)    

fun subst_i_ty_visitor_vtable cast ((subst_i_i, subst_i_s), d, x, v) : ('this, int, 'var, 'bsort, 'idx, 'sort, 'var, 'bsort, 'idx2, 'sort2) ty_visitor_vtable =
  let
    fun extend_i this env _ = env + 1
    fun visit_idx this env b = subst_i_i (d + env) (x + env) v b
    fun visit_sort this env b = subst_i_s (d + env) (x + env) v b
  in
    default_ty_visitor_vtable
      cast
      extend_i
      extend_noop
      visit_noop
      visit_noop
      visit_idx
      visit_sort
  end

fun new_subst_i_ty_visitor params = new_ty_visitor subst_i_ty_visitor_vtable params
    
fun subst_i_t_fn substs d x v b =
  let
    val visitor as (TyVisitor vtable) = new_subst_i_ty_visitor (substs, d, x, v)
  in
    #visit_ty vtable visitor 0 b
  end

structure ExportPP = struct

open LongId
open Util
open MicroTiML
open MicroTiMLVisitor
open MicroTiMLExLongId
open MicroTiMLEx
       
infixr 0 $
infixr 0 !!
         
fun short_to_long_id x = ID (x, dummy)
fun export_var sel ctx id =
  let
    fun unbound s = "__unbound_" ^ s
    (* fun unbound s = raise Impossible $ "Unbound identifier: " ^ s *)
  in
    case id of
        ID (x, _) =>
        short_to_long_id $ nth_error (sel ctx) x !! (fn () => unbound $ str_int x)
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
fun pp_t_to_string b = MicroTiMLPP.pp_t_to_string_fn (str_var, str_bs, str_i, str_s, const_fun "<kind>") b
fun pp_e_to_string a = MicroTiMLExPP.pp_e_to_string_fn (
    str_var,
    str_i,
    str_s,
    const_fun "<kind>",
    pp_t_to
  ) a

end

fun itctx_names (ictx, tctx) = (map fst ictx, map fst tctx)
fun ctx_names (ictx, tctx, ectx, _) = (map fst ictx, map fst tctx, [], map fst ectx)
                                   
fun is_eq_ty (ctx as (ictx, tctx)) (t, t') =
    let
      val assert_b = fn b => assert_b "Can't unify types" b
      val t = whnf ctx t
      val t' = whnf ctx t'
      (* val () = println $ sprintf "comparing types:\n  $  $" [ *)
      (*       ExportPP.pp_t_to_string $ ExportPP.export_t (itctx_names ctx) t, *)
      (*       ExportPP.pp_t_to_string $ ExportPP.export_t (itctx_names ctx) t' *)
      (*     ] *)
    in
      case (t, t') of
          (TVar x, TVar x') => assert_b (eq_var (x, x'))
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
        | _ => raise MTCError $ sprintf "unknown case in is_eq_ty:\n  $  $"
                     [
                       ExportPP.pp_t_to_string $ ExportPP.export_t (itctx_names ctx) t,
                       ExportPP.pp_t_to_string $ ExportPP.export_t (itctx_names ctx) t'
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
  
structure IntMap = IntBinaryMap
structure HeapMap = IntMap

type mtiml_ty = (Expr.var, bsort, idx, sort) ty
type econtext = (string * mtiml_ty) list
                                                      
fun add_sorting_full new (ictx, tctx, ectx, hctx) = (new :: ictx, tctx, map (mapSnd shift01_i_t) ectx, HeapMap.map (mapPair (shift01_i_t, shift01_i_i)) hctx)
fun add_kinding_full new (ictx, tctx, ectx, hctx) = (ictx, new :: tctx, map (mapSnd shift01_t_t) ectx, HeapMap.map (mapFst shift01_t_t) hctx)
fun add_typing_full new (ictx, tctx, ectx, hctx) = (ictx, tctx, new :: ectx, hctx)

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

infixr 0 %:
fun a %: b = EAscType (a, b)

fun tc (ctx as (ictx, tctx, ectx : econtext, hctx)) e_input =
  let
    (* val () = print "typechecking: " *)
    (* val () = println $ (* substr 0 100 $  *)ExportPP.pp_e_to_string $ ExportPP.export (ctx_names ctx) e *)
    val itctx = (ictx, tctx)
    fun main () =
        case e_input of
        EVar x =>
        (case nth_error_local ectx x of
             SOME (_, t) => (e_input, t, T0)
           | NONE => raise MTCError "Unbound term variable"
        )
      | EConst c => (e_input, get_expr_const_type c, T0)
      | ELoc l =>
        (case HeapMap.find (hctx, l) of
             SOME (t, i) => (e_input, TArr (t, i), T0)
           | NONE => raise MTCError "Unbound location"
        )
      | EUnOp (EUProj proj, e) =>
        let
          val (e, t_e, i) = tc ctx e
          val t_e = whnf itctx t_e
          val (t1, t2) = case t_e of
                             TBinOp (TBProd, t1, t2) => (t1, t2)
                           | _ => raise MTCError "EProj"
        in
          (EProj (proj, e %: t_e), choose (t1, t2) proj, i)
        end
      | EUnOp (EUInj (inj, t'), e) =>
        let
          val () = kc_against_kind itctx (t', KType)
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
          val () = kc_against_kind itctx (t', KType)
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
        in
          (EFold (t', e %: t), t', i)
        end
      | EUnOp (EUUnfold, e) =>
        let
          val (e, t_e, i) = tc ctx e
          val t_e = whnf itctx t_e
          val (t, args) = collect_TAppIT t_e
          val (k, (_, t1)) = case t of
                                 TRec data => unBindAnnoName data
                               | _ => raise MTCError "EUnfold"
        in
          (EUnfold (e %: t_e), TAppITs (subst0_t_t t t1) args, i)
        end
      | EBinOp (EBApp, e1, e2) =>
        let
          val (e1, t_e1, i1) = tc ctx e1
          val t_e1 = whnf itctx t_e1
          val (t1, i, t2) = case t_e1 of
                                TArrow data => data
                              | _ => raise MTCError "EApp"
          val (e2, i2) = tc_against_ty ctx (e2, t1)
        in
          (EApp (e1 %: t_e1, e2), t2, i1 %+ i2 %+ T1 %+ i)
        end
      | EBinOp (EBPair, e1, e2) =>
        let
          val (e1, t1, i1) = tc ctx e1
          val (e2, t2, i2) = tc ctx e2
        in
          (EPair (e1, e2), TProd (t1, t2), i1 %+ i2)
        end
      | EBinOp (EBPrim opr, e1, e2) =>
        let
          val (e1, t1, i1) = tc ctx e1
          val () = is_eq_ty itctx (t1, get_prim_expr_bin_op_arg1_ty opr)
          val (e2, t2, i2) = tc ctx e2
          val () = is_eq_ty itctx (t2, get_prim_expr_bin_op_arg2_ty opr)
        in
          (EBinOpPrim (opr, e1 %: t1, e2 %: t2), get_prim_expr_bin_op_res_ty opr, i1 %+ i2)
        end
      | EBinOp (EBNew, e1, e2) =>
        let
          val (e1, t1, j1) = tc ctx e1
          val t1 = whnf itctx t1
          val i = case t1 of
                      TNat i => i
                    | _ => raise MTCError "ENew"
          val (e2, t2, j2) = tc ctx e2
        in
          (ENew (e1 %: t1, e2 %: t2), TArr (t2, i), j1 %+ j2)
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
        in
          (ERead (e1 %: t1, e2 %: t2), t, j1 %+ j2)
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
        in
          (ENatAdd (e1 %: t1, e2 %: t2), TNat (i1 %+ i2), j1 %+ j2)
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
        in
          (EWrite (e1 %: t1, e2 %: t2, e3 %: t), TUnit, j1 %+ j2 %+ j3)
        end
      | ECase data =>
        let
          val (e, (name1, e1), (name2, e2)) = unECase data
          val (e, t_e, i) = tc ctx e
          val t_e = whnf itctx t_e
          val (t1, t2) = case t_e of
                             TBinOp (TBSum, t1, t2) => (t1, t2)
                           | _ => raise MTCError $ "ECase: " ^ (ExportPP.pp_t_to_string $ ExportPP.export_t (map fst ictx, map fst tctx) t_e)
          val (e1, t1, i1) = tc (add_typing_full (fst name1, t1) ctx) e1
          val (e2, t2, i2) = tc (add_typing_full (fst name2, t2) ctx) e2
          val () = is_eq_ty itctx (t1, t2)
        in
          (MakeECase (e %: t_e, (name1, e1), (name2, e2)), t1, i %+ IMax (i1, i2))
        end
      | EAbs data =>
        let
          val (t1 : mtiml_ty, (name, e)) = unEAbs data
          val () = kc_against_kind itctx (t1, KType)
          val (e, t2, i) = tc (add_typing_full (fst name, t1) ctx) e
        in
          (MakeEAbs (name, t1, e), TArrow (t1, i, t2), T0)
        end
      | ERec data =>
        let
          val (t, (name, e)) = unBindAnnoName data
          val () = case snd $ collect_EAbsIT e of
                       EAbs _ => ()
                     | _ => raise MTCError "ERec: body should be EAbsITMany (EAbs (...))"
          val () = kc_against_kind itctx (t, KType)
          val e = tc_against_ty_time (add_typing_full (fst name, t) ctx) (e, t, T0)
        in
          (MakeERec (name, t, e), t, T0)
        end
      | EAbsT data =>
        let
          val (k, (name, e)) = unEAbsT data
          val () = assert_b "EAbsT: is_value e" $ is_value e
          val (e, t) = tc_against_time (add_kinding_full (fst name, k) ctx) (e, T0)
        in
          (MakeEAbsT (name, k, e), MakeTForall (k, name, t), T0)
        end
      | EAbsI data =>
        let
          val (s, (name, e)) = unEAbsI data
          val () = is_wf_sort ictx s
          val () = assert_b "EAbsI" $ is_value e
          val (e, t) = tc_against_time (add_sorting_full (fst name, s) ctx) (e, T0)
        in
          (MakeEAbsI (name, s, e), MakeTForallI (s, name, t), T0)
        end
      | EAppT (e, t1) =>
        let
          val (e, t_e, i) = tc ctx e
          val t_e = whnf itctx t_e
          val (_, (_, t)) = case t_e of
                                TQuan (Forall, data) => unTQuan data
                              | _ => raise MTCError "EAppT"
          val () = kc_against_kind itctx (t1, KType)
        in
          (EAppT (e %: t_e, t1), subst0_t_t t1 t, i)
        end
      | EAppI (e, i) =>
        let
          val (e, t_e, j) = tc ctx e
          val t_e = whnf itctx t_e
          val (s, (_, t)) = case t_e of
                                TQuanI (Forall, data) => unTQuanI data
                              | _ => raise MTCError "EAppT"
          val () = sc_against_sort ictx (i, s)
        in
          (EAppI (e %: t_e, i), subst0_i_t i t, j)
        end
      | EPack (t', t1, e) =>
        let
          val () = kc_against_kind itctx (t', KType)
          val t' = whnf itctx t'
          val (k, (_, t)) = case t' of
                                TQuan (Exists _, data) => unTQuan data
                              | _ => raise MTCError "EPack"
          val () = kc_against_kind itctx (t1, k)
          val t_e = subst0_t_t t1 t
          val (e, i) = tc_against_ty ctx (e, t_e)
        in
          (EPack (t', t1, e %: t_e), t', i)
        end
      | EPackI (t', i, e) =>
        let
          val () = kc_against_kind itctx (t', KType)
          val t' = whnf itctx t'
          val (s, (_, t)) = case t' of
                                TQuanI (Exists _, data) => unTQuanI data
                              | _ => raise MTCError "EPackI"
          val () = sc_against_sort ictx (i, s)
          val t_e = subst0_i_t i t
          val (e, j) = tc_against_ty ctx (e, t_e)
        in
          (EPackI (t', i, e %: t_e), t', j)
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
        in
          (MakeEUnpack (e1 %: t_e1, tname, ename, e2), t2, i1 %+ i2)
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
                              | _ => raise MTCError $ mismatch "EUnpackI" (ExportPP.pp_t_to_string $ ExportPP.export_t (itctx_names itctx) t_e1) "TQuanI (Exists, _)"
          val (e2, t2, i2) = tc (add_typing_full (fst ename, t) $ add_sorting_full (fst iname, s) ctx) e2
          val t2 = forget01_i_t t2
                   handle ForgetError (r, m) => raise ForgetError (r, m ^ " when forgetting type: " ^ (ExportPP.pp_t_to_string $ ExportPP.export_t (itctx_names $ add_sorting_it (fst iname, s) itctx) t2))
          val i2 = forget01_i_i i2
                   handle ForgetError (r, m) => raise ForgetError (r, m ^ " when forgetting time: " ^ (ToString.SN.strn_i $ ExportPP.export_i (fst iname :: map fst ictx) i2))
        in
          (MakeEUnpackI (e1 %: t_e1, iname, ename, e2), t2, i1 %+ i2)
        end
      | EPackIs (t, is, e) =>
        let
          val () = kc_against_kind itctx (t, KType)
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
              in
                (MakeELet (e1 %: t1, name, e2), t2, i)
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
                val () = sc_against_sort ictx (i, STime)
                fun assert_cons ls =
                  case ls of
                      x :: xs => (x, xs)
                    | [] => raise Impossible "assert_cons fails"
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
                (e, t, i)
              end
        end
      | EAscType (e, t2) =>
        let
          val (e, t1, i) = tc ctx e
          val () = kc_against_kind itctx (t2, KType)
          val () = is_eq_ty itctx (t1, t2)
        in
          (e %: t2, t2, i)
        end
      | ENever t =>
        let
          val () = kc_against_kind itctx (t, KType)
        in
          (e_input, t, T0)
        end
      | EBuiltin t =>
        let
          val () = kc_against_kind itctx (t, KType)
        in
          (e_input, t, T0)
        end
      | ELet data =>
        let
          val (e1, (name, e2)) = unELet data
          val (e1, t1, i1) = tc ctx e1
          val (e2, t2, i2) = tc (add_typing_full (fst name, t1) ctx) e2
        in
          (MakeELet (e1 %: t1, name, e2), t2, i1 %+ i2)
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
          val _ = sc ictx i
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
      | _ => raise Impossible $ "unknown case in tc: " ^ (ExportPP.pp_e_to_string $ ExportPP.export (ctx_names ctx) e_input)
    fun extra_msg () = "\nwhen typechecking " ^ ((* substr 0 300 $  *)ExportPP.pp_e_to_string $ ExportPP.export (ctx_names ctx) e_input)
    val (e_output, t, i) = main ()
                 handle ForgetError (r, m) => raise MTCError ("Forgetting error: " ^ m ^ extra_msg ())
                      | MSCError (r, m) => raise MTCError ("Sortcheck error:\n" ^ join_lines m ^ extra_msg ())
                      | MUnifyError (r, m) => raise MTCError ("Unification error:\n" ^ join_lines m ^ extra_msg ())
                      | MTCError m => raise MTCError (m ^ extra_msg ())
                      | Impossible m => raise Impossible (m ^ extra_msg ())
    (* val () = print "tc-done: " *)
    (* val () = println $ substr 0 100 $ ExportPP.pp_e_to_string $ ExportPP.export (ctx_names ctx) e *)
  in
    (e_output, t, i)
  end

and tc_against_ty (ctx as (ictx, tctx, _, _)) (e, t) =
    let
      (* val () = println $ sprintf "typechecking against type:\n  $\n  $" [ *)
      (*       substr 0 10000 $ ExportPP.pp_e_to_string $ ExportPP.export (ctx_names ctx) e, *)
      (*       ExportPP.pp_t_to_string $ ExportPP.export_t (itctx_names (ictx, tctx)) t *)
      (*     ] *)
      val (e, t', i) = tc ctx e
      (* val () = println $ sprintf "tc_against_ty() to cmp types:\n  $  $" [ *)
      (*       ExportPP.pp_t_to_string $ ExportPP.export_t (itctx_names (ictx, tctx)) t', *)
      (*       ExportPP.pp_t_to_string $ ExportPP.export_t (itctx_names (ictx, tctx)) t *)
      (*     ] *)
      val () = is_eq_ty (ictx, tctx) (t', t)
      (* val () = println "tc_against_ty() finished" *)
    in
      (e, i)
    end
    
and tc_against_time (ctx as (ictx, tctx, _, _)) (e, i) =
    let
      val (e, t, i') = tc ctx e
      val () = check_prop ictx (i' %<= i)
    in
      (e, t)
    end
    
and tc_against_ty_time (ctx as (ictx, tctx, _, _)) (e, t, i) =
    let
      val (e, t') = tc_against_time ctx (e, i)
      val () = is_eq_ty (ictx, tctx) (t', t)
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
    val () = println "after m ()"
    val vcs = !vcs
    val admits = !admits
    val vcs = map to_vc vcs
    val () = println "after to_vc; calling simp_vc_vcs"
    (* val () = app println $ concatMap (fn ls => ls @ [""]) $ map (str_vc false "") vcs *)
    val vcs_len = length vcs
    val () = println $ "#VCs: " ^ str_int vcs_len
    (* val vcs = concatMapi (fn (i, vc) => (println (sprintf "vc $ @ $" [str_int vcs_len, str_int i]); simp_vc_vcs vc)) vcs *)
    (* val () = println "before simp vcs" *)
    (* val vcs = map VC.simp_vc vcs *)
    (* val () = println "after simp vcs" *)
    (* val vcs = TrivialSolver.simp_and_solve_vcs vcs *)
    val admits = map to_vc admits
  in 
    (r, vcs, admits) 
  end

fun typecheck ctx e =
  let
  in
    runWriter (fn () => tc ctx e) ()
  end

end

structure MicroTiMLTypecheckUnitTest = struct

structure TestUtil = struct

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

infixr 0 $
infixr 0 !!
         
fun test1 dirname =
  let
    val filename = join_dir_file (dirname, "micro-timl-tc-test1.pkg")
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
    val () = pp_e $ export ToStringUtil.empty_ctx e
    val () = println ""
    open MicroTiMLTypecheck
    open TestUtil
    val () = println "Started MicroTiML typechecking ..."
    val ((_, t, i), vcs, admits) = typecheck ([], [], [], HeapMap.empty) e
    val () = println "Finished MicroTiML typechecking"
    val () = println "Type:"
    val () = pp_t $ export_t ([], []) t
    val () = println "Time:"
    val i = simp_i i
    val () = println $ ToString.str_i Gctx.empty [] i
    val () = println $ "#VCs: " ^ str_int (length vcs)
    (* val () = println "VCs:" *)
    (* val () = app println $ concatMap (fn ls => ls @ [""]) $ map (str_vc false "") vcs *)
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
                       
                                 
