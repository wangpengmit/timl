structure MicroTiMLTypecheck = struct

open UVar
open TypecheckUtil
open Unify
open FreshUVar
open Expr

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
    val (_, _, bs) = get_uvar_info x !! (fn () => raise Impossible "get_bsort_UVarI")
  in
    (UVarI data, bs)
  end

fun match_BSArrow gctx ctx r bs1 =
  case bs1 of
      BSArrow data => data
    | _ => raise Impossible "match_BSArrow"

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
                                   exception Error = Error
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

fun sc_against_sort ctx (i, s) = ignore $ check_sort Gctx.empty (ctx, i, s)

fun is_wf_sort ctx s = ignore $ Sortcheck.is_wf_sort Gctx.empty (ctx, s)

exception Error of string

fun INat n = ConstIN (n, dummy)
fun IMax (i1, i2) = BinOpI (MaxI, i1, i2)
val TInt = TConst TCInt
fun unTRec data =
  let
    val ((name, anno), t) = unBindAnno data
    val name = Name2str name
  in
    (anno, (name, t))
  end
val unTQuan = unTRec
val unTQuanI = unTRec
val unTAbsT = unTRec
val unTAbsI = unTRec
fun unBindSimp t =
  let
    val (Binder name, t) = unBind t
  in
    (name, t)
  end
fun unELetIdx (def, bind) =
  let
    val (name, e) = unBindSimp bind
  in
    (def, (Name2str name, e))
  end
val unELetType = unELetIdx
val unELet = unELetIdx
fun unEUnpack (def, bind) =
  let
    val (name1, bind) = unBindSimp bind
    val (name2, e) = unBindSimp bind
  in
    (def, (Name2str name1, Name2str name2, e))
  end
val unEAbsI = unTRec
val unEAbsT = unTRec
val unEAbs = unTRec
val unERec = unTRec
fun unECase (e, bind1, bind2) =
  let
    val (name1, e1) = unBindSimp bind1
    val (name2, e2) = unBindSimp bind2
  in
    (e, (Name2str name1, e1), (Name2str name2, e2))
  end
               
fun MakeTQuanI (q, s, name, t) = TQuanI (q, BindAnno ((IName (name, dummy), s), t))
fun MakeTQuan (q, k, name, t) = TQuan (q, BindAnno ((TName (name, dummy), k), t))
fun MakeTForallI (s, name, t) = MakeTQuanI (Forall, s, name, t)
fun MakeTForall (s, name, t) = MakeTQuan (Forall, s, name, t)

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
    | _ => raise Error "is_eq_sort"
                                       
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
    | _ => raise Error "can't unify kinds" 
       
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
    | QID _ => raise Error "nth_error QID"
                      
type icontext = (string * sort) list
type tcontext = (string * bsort kind) list
                            
fun add_sorting_it new (ictx, tctx) = (new :: ictx, tctx)
fun add_kinding_it new (ictx, tctx) = (ictx, new :: tctx)

fun kc (ctx as (ictx, tctx) : icontext * tcontext) t : bsort kind =
  case t of
      TVar x =>
      (case nth_error_local tctx x of
           SOME (_, k) => k
         | NONE => raise Error "unbound type variable"
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
        val k = kc (add_sorting_it (name, BasicSort b) ctx) t
      in
        KArrow (b, k)
      end
    | TAppI (t, i) =>
      let
        val k' = kc ctx t
        val (b, k) = case k' of
                         KArrow data => data
                       | _ => raise Error "TAppI"
        val () = sc_against_sort ictx (i, BasicSort b)
      in
        k
      end
    | TAbsT data =>
      let
        val (k1, (name, t)) = unTAbsT data
        val k2 = kc (add_kinding_it (name, k1) ctx) t
      in
        KArrowT (k1, k2)
      end
    | TAppT (t1, t2) =>
      let
        val k' = kc ctx t1
        val (k1, k2) = case k' of
                         KArrowT data => data
                       | _ => raise Error "TAppT"
        val () = kc_against_kind ctx (t2, k1)
      in
        k2
      end
    | TQuanI (_, data) =>
      let
        val (s, (name, t)) = unTQuanI data
        val () = kc_against_kind (add_sorting_it (name, s) ctx) (t, KType)
      in
        KType
      end
    | TQuan (_, data) =>
      let
        val (k, (name, t)) = unTQuan data
        val () = kc_against_kind (add_kinding_it (name, k) ctx) (t, KType)
      in
        KType
      end
    | TRec data =>
      let
        val (k, (name, t)) = unTRec data
        val () = kc_against_kind (add_kinding_it (name, k) ctx) (t, k)
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

fun whnf ctx t =
    case t of
        TAppT (t1, t2) =>
        let
          val t1 = whnf ctx t1
        in
          case t1 of
              TAbsT data =>
              let
                val (_, (_, t1)) = unTAbsT data
              in
                whnf ctx $ subst0_t_t t2 t1
              end
            | _ => TAppT (t1, t2)
        end
      | TAppI (t, i) =>
        let
          val t = whnf ctx t
        in
          case t of
              TAbsI data =>
              let
                val (_, (_, t)) = unTAbsT data
              in
                whnf ctx $ subst0_i_t i t
              end
            | _ => TAppI (t, i)
        end
      | TVar x => TVar x (* todo: look up type aliasing in ctx *)
      | _ => t

fun assert msg b = Util.assert (fn () => b) msg
    
fun is_eq_ty (ctx as (ictx, tctx)) (t, t') =
    let
      val assert = fn b => assert "Can't unify types" b
      val t = whnf ctx t
      val t' = whnf ctx t'
    in
      case (t, t') of
          (TVar x, TVar x') => assert (x = x')
        | (TConst c, TConst c') => assert (c = c')
        | (TBinOp (opr, t1, t2), TBinOp (opr', t1', t2')) =>
          let
            val () = assert (opr = opr')
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
            val () = assert (q = q')
            val (s, (name, t)) = unTQuanI data
            val (s', (_, t')) = unTQuanI data'
            val () = is_eq_sort ictx (s, s')
            val () = is_eq_ty (add_sorting_it (name, s) ctx) (t, t')
          in
            ()
          end
        | (TQuan (q, data), TQuan (q', data')) =>
          let
            val () = assert (q = q')
            val (k, (name, t)) = unTQuan data
            val (k', (_, t')) = unTQuan data'
            val () = is_eq_kind (k, k')
            val () = is_eq_ty (add_kinding_it (name, k) ctx) (t, t')
          in
            ()
          end
        | (TRec data, TRec data') =>
          let
            val (k, (name, t)) = unTQuan data
            val (k', (_, t')) = unTQuan data'
            val () = is_eq_kind (k, k')
            val () = is_eq_ty (add_kinding_it (name, k) ctx) (t, t')
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
            val () = is_eq_ty (add_kinding_it (name, k) ctx) (t, t')
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
            val () = is_eq_ty (add_sorting_it (name, BasicSort b) ctx) (t, t')
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
        | _ => raise Error "is_eq_ty"
    end      

(***************** the "subst_t_e" visitor  **********************)    

fun subst_t_expr_visitor_vtable cast visit_ty =
  let
    fun extend_i this env _ = mapFst idepth_inc env
    fun extend_t this env _ = mapSnd tdepth_inc env
  in
    default_expr_visitor_vtable
      cast
      extend_i
      extend_t
      extend_noop
      extend_noop
      visit_noop
      visit_noop
      visit_noop
      visit_noop
      (ignore_this visit_ty)
  end

fun new_subst_t_expr_visitor params = new_expr_visitor subst_t_expr_visitor_vtable params
    
fun subst_t_e_fn params b =
  let
    val visitor as (ExprVisitor vtable) = new_subst_t_expr_visitor params
  in
    #visit_expr vtable visitor (IDepth 0, TDepth 0) b
  end

fun adapt f d x v env b =
  let
    fun add_depth (di, dt) (di', dt') = (idepth_add (di, di'), tdepth_add (dt, dt'))
  in
    f (add_depth d env) (x + unTDepth (snd env)) v b
  end
    
fun subst_t_e d x v = subst_t_e_fn (adapt subst_t_t d x v)
fun subst0_t_e a = subst_t_e (IDepth 0, TDepth 0) 0 a

fun forget_i_t a = shift_i_t_fn (forget_i_i, forget_i_s) a
fun forget_t_t a = shift_t_t_fn forget_var a
                               
fun forget01_i_i x = forget_i_i 0 1 x
fun forget01_i_t x = forget_i_t 0 1 x
fun forget01_t_t x = forget_t_t 0 1 x

fun collect_TAppI_TAppT_rev t =
  let
    val self = collect_TAppI_TAppT_rev
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
fun collect_TAppI_TAppT t = mapSnd rev $ collect_TAppI_TAppT_rev t

fun TAppITs t args = foldl (fn (arg, t) => case arg of inl i => TAppI (t, i) | inr t' => TAppT (t, t')) t args

fun collect_EAbsI_EAbsT e =
  case e of
      EAbsI data =>
      let
        val (s, (name, e)) = unEAbsI data
        val (binds, e) = collect_EAbsI_EAbsT e
      in
        (inl (name, s) :: binds, e)
      end
    | EAbsT data =>
      let
        val (k, (name, e)) = unEAbsT data
        val (binds, e) = collect_EAbsI_EAbsT e
      in
        (inr (name, k) :: binds, e)
      end
    | _ => ([], e)

fun is_value e =
  case e of
      EConst _ => true
    | EBinOp (EBPair, e1, e2) => is_value e1 andalso is_value e2
    | EUnOp (EUInj _, e) => is_value e
    | EAbs _ =>  true
    | EAbsT _ => true
    | EAbsI _ => true
    | EPack (_, _, e) => is_value e
    | EPackI (_, _, e) => is_value e
    | EUnOp (EUFold _, e) => is_value e
    | ELoc _ => true
    | _ => false

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

fun tc (ctx as (ictx, tctx, ectx : econtext, hctx)) e : mtiml_ty * idx =
  let
    val itctx = (ictx, tctx)
  in
    case e of
        EVar x =>
        (case nth_error_local ectx x of
             SOME (_, t) => (t, T0)
           | NONE => raise Error "Unbound term variable"
        )
      | EConst c => (get_expr_const_type c, T0)
      | ELoc l =>
        (case HeapMap.find (hctx, l) of
             SOME (t, i) => (TArr (t, i), T0)
           | NONE => raise Error "Unbound location"
        )
      | EUnOp (EUProj proj, e) =>
        let
          val (t, i) = tc ctx e
          val (t1, t2) = case t of
                             TBinOp (TBProd, t1, t2) => (t1, t2)
                           | _ => raise Error "EProj"
          fun choose (t1, t2) proj =
            case proj of
                ProjFst => t1
              | ProjSnd => t2
        in
          (choose (t1, t2) proj, i)
        end
      | EUnOp (EUInj (inj, t'), e) =>
        let
          val (t, i) = tc ctx e
          fun inject (t, t') inj =
            case inj of
                InjInl => (t, t')
              | InjInr => (t', t)
        in
          (TSum $ inject (t, t') inj, i)
        end
      | EUnOp (EUFold t', e) =>
        let
          val (t, args) = collect_TAppI_TAppT t'
          val (k, (_, t1)) = case t of
                                 TRec data => unTRec data
                               | _ => raise Error "EFold"
          val i = tc_against_ty ctx (e, TAppITs (subst0_t_t t t1) args) 
        in
          (t', i)
        end
      | EUnOp (EUUnfold, e) =>
        let
          val (t', i) = tc ctx e
          val (t, args) = collect_TAppI_TAppT t'
          val (k, (_, t1)) = case t of
                                 TRec data => unTRec data
                               | _ => raise Error "EUnfold"
        in
          (TAppITs (subst0_t_t t t1) args, i)
        end
      | EBinOp (EBPrim opr, e1, e2) =>
        let
          val (t1, i1 : idx) = tc ctx e1
          val () = is_eq_ty itctx (t1, get_prim_expr_bin_op_arg1_ty opr)
          val (t2, i2) = tc ctx e2
          val () = is_eq_ty itctx (t2, get_prim_expr_bin_op_arg2_ty opr)
        in
          (get_prim_expr_bin_op_res_ty opr, i1 %+ i2)
        end
      | EBinOp (EBApp, e1, e2) =>
        let
          val (t, i1) = tc ctx e1
          val (t1, i, t2) = case t of
                                TArrow data => data
                              | _ => raise Error "EApp"
          val i2 = tc_against_ty ctx (e2, t1)
        in
          (t2, i1 %+ i2 %+ T1 %+ i)
        end
      | EBinOp (EBPair, e1, e2) =>
        let
          val (t1, i1) = tc ctx e1
          val (t2, i2) = tc ctx e2
        in
          (TProd (t1, t2), i1 %+ i2)
        end
      | EBinOp (EBNew, e1, e2) =>
        let
          val (t1, j1) = tc ctx e1
          val i = case t1 of
                      TNat i => i
                    | _ => raise Error "ENew"
          val (t, j2) = tc ctx e2
        in
          (TArr (t, i), j1 %+ j2)
        end
      | EBinOp (EBRead, e1, e2) =>
        let
          val (t1, j1) = tc ctx e1
          val (t, i1) = case t1 of
                            TArr data => data
                          | _ => raise Error "ERead 1"
          val (t2, j2) = tc ctx e2
          val i2 = case t2 of
                       TNat i => i
                     | _ => raise Error "ERead 2"
          val () = check_prop ictx (i2 %< i1)
        in
          (t, j1 %+ j2)
        end
      | EBinOp (EBNatAdd, e1, e2) =>
        let
          val (t1, j1) = tc ctx e1
          val i1 = case t1 of
                       TNat i => i
                     | _ => raise Error "ENatAdd 1"
          val (t2, j2) = tc ctx e2
          val i2 = case t2 of
                       TNat i => i
                     | _ => raise Error "ENatAdd 2"
        in
          (TNat (i1 %+ i2), j1 %+ j2)
        end
      | EWrite (e1, e2, e3) =>
        let
          val (t1, j1) = tc ctx e1
          val (t, i1) = case t1 of
                            TArr data => data
                          | _ => raise Error "ERead 1"
          val (t2, j2) = tc ctx e2
          val i2 = case t2 of
                       TNat i => i
                     | _ => raise Error "ERead 2"
          val () = check_prop ictx (i2 %< i1)
          val j3 = tc_against_ty ctx (e3, t)
        in
          (TUnit, j1 %+ j2 %+ j3)
        end
      | ECase data =>
        let
          val (e, (name1, e1), (name2, e2)) = unECase data
          val (t, i) = tc ctx e
          val (t1, t2) = case t of
                             TBinOp (TBSum, t1, t2) => (t1, t2)
                           | _ => raise Error "ECase"
          val (t1, i1) = tc (add_typing_full (name1, t1) ctx) e1
          val (t2, i2) = tc (add_typing_full (name2, t2) ctx) e2
          val () = is_eq_ty itctx (t1, t2)
        in
          (t1, i %+ IMax (i1, i2))
        end
      | EAbs data =>
        let
          val (t1 : mtiml_ty, (name, e)) = unEAbs data
          val () = kc_against_kind itctx (t1, KType)
          val (t2, i) = tc (add_typing_full (name, t1) ctx) e
        in
          (TArrow (t1, i, t2), T0)
        end
      | ERec data =>
        let
          val (t, (name, e)) = unERec data
          val (_, e') = collect_EAbsI_EAbsT e
          val () = case e' of
                       EAbs _ => ()
                     | _ => raise Error "ERec"
          val () = kc_against_kind itctx (t, KType)
          val () = tc_against_ty_time (add_typing_full (name, t) ctx) (e, t, T0)
        in
          (t, T0)
        end
      | EAbsT data =>
        let
          val (k, (name, e)) = unEAbsT data
          val () = assert "EAbsT" $ is_value e
          val t = tc_against_time (add_kinding_full (name, k) ctx) (e, T0)
        in
          (MakeTForall (k, name, t), T0)
        end
      | EAppT (e, t1) =>
        let
          val (t', i) = tc ctx e
          val (_, (_, t)) = case t' of
                                TQuan (Forall, data) => unTQuan data
                              | _ => raise Error "EAppT"
          val () = kc_against_kind itctx (t1, KType)
        in
          (subst0_t_t t1 t, i)
        end
      | EAbsI data =>
        let
          val (s, (name, e)) = unEAbsI data
          val () = is_wf_sort ictx s
          val () = assert "EAbsI" $ is_value e
          val t = tc_against_time (add_sorting_full (name, s) ctx) (e, T0)
        in
          (MakeTForallI (s, name, t), T0)
        end
      | EAppI (e, i) =>
        let
          val (t', j) = tc ctx e
          val (s, (_, t)) = case t' of
                                TQuanI (Forall, data) => unTQuanI data
                              | _ => raise Error "EAppT"
          val () = sc_against_sort ictx (i, s)
        in
          (subst0_i_t i t, j)
        end
      | EPack (t', t1, e) =>
        let
          val () = kc_against_kind itctx (t', KType)
          val (k, (_, t)) = case t' of
                                TQuan (Exists _, data) => unTQuan data
                              | _ => raise Error "EPack"
          val () = kc_against_kind itctx (t1, k)
          val i = tc_against_ty ctx (e, subst0_t_t t1 t)
        in
          (t', i)
        end
      | EUnpack data =>
        let
          val (e1, (tname, ename, e2)) = unEUnpack data
          val (t', i1) = tc ctx e1
          val (k, (_, t)) = case t' of
                                TQuan (Exists _, data) => unTQuan data
                              | _ => raise Error "EUnpack"
          val (t2, i2) = tc (add_typing_full (ename, t) $ add_kinding_full (tname, k) ctx) e2
          val t2 = forget01_t_t t2
        in
          (t2, i1 %+ i2)
        end
      | EPackI (t', i, e) =>
        let
          val () = kc_against_kind itctx (t', KType)
          val (s, (_, t)) = case t' of
                                TQuanI (Exists _, data) => unTQuanI data
                              | _ => raise Error "EPackI"
          val () = sc_against_sort ictx (i, s)
          val j = tc_against_ty ctx (e, subst0_i_t i t)
        in
          (t', j)
        end
      | EUnpackI data =>
        let
          val (e1, (iname, ename, e2)) = unEUnpack data
          val (t', i1) = tc ctx e1
          val (s, (_, t)) = case t' of
                                TQuanI (Exists _, data) => unTQuanI data
                              | _ => raise Error "EUnpackI"
          val (t2, i2) = tc (add_typing_full (ename, t) $ add_sorting_full (iname, s) ctx) e2
          val t2 = forget01_i_t t2
          val i2 = forget01_i_i i2
        in
          (t2, i1 %+ i2)
        end
      | EAscTime (e, i2) =>
        let
          val (t, i1) = tc ctx e
          val () = sc_against_sort ictx (i2, STime)
          val () = check_prop ictx (i1 %<= i2)
        in
          (t, i2)
        end
      | EAscType (e, t2) =>
        let
          val (t1, i) = tc ctx e
          val () = kc_against_kind itctx (t2, KType)
          val () = is_eq_ty itctx (t1, t2)
        in
          (t2, i)
        end
      | ENever t => (t, T0)
      | EBuiltin t => (t, T0)
      | ELet data =>
        let
          val (e1, (name, e2)) = unELet data
          val (t1, i1) = tc ctx e1
          val (t2, i2) = tc (add_typing_full (name, t1) ctx) e2
        in
          (t2, i1 %+ i2)
        end
      | ELetType data =>
        let
          val (t, (name, e)) = unELetType data
        in
          tc ctx $ subst0_t_e t e (* todo: record type aliasing in ctx *)
        end
      | ELetIdx data =>
        let
          val (i, (name, e)) = unELetIdx data
        in
          tc ctx $ subst0_i_e i e (* todo: record index aliasing in ctx *)
        end
      | _ => raise Impossible "tc"
  end

and tc_against_ty (ctx as (ictx, tctx, _, _)) (e, t) =
    let
      val (t', i) = tc ctx e
      val () = is_eq_ty (ictx, tctx) (t', t)
    in
      i
    end
    
and tc_against_time (ctx as (ictx, tctx, _, _)) (e, i) =
    let
      val (t, i') = tc ctx e
      val () = check_prop ictx (i' %<= i)
    in
      t
    end
    
and tc_against_ty_time (ctx as (ictx, tctx, _, _)) (e, t, i) =
    let
      val t' = tc_against_time ctx (e, i)
      val () = is_eq_ty (ictx, tctx) (t', t)
    in
      ()
    end
    
end
