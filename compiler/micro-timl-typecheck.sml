structure MicroTiMLTypecheck = struct

open MicroTiMLCosts
open MicroTiMLFreeEVars
open MicroTiMLVisitor2
open EvalConstr
open UVar
open UVarExprUtil
open PostTypecheck
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
        
infix  9 @!
fun m @! k = StMap.find (m, k)
infix  6 @+
fun m @+ a = StMap.insert' (a, m)
                           
infix 6 @--
fun m @-- m' = StMapU.sub m m'
                          
infix 6 @++
infix 9 @!!
         
infix 6 @%++
        
infix 6 @%!!
infix 6 @%+

infix 6 @%--
        
fun is_wf_basic_sort_BSUVar data = BSUVar data
    
fun get_basic_sort_IUVar gctx ctx (data as (x, r)) =
  let
    val (_, ctx, bs_ret) = get_uvar_info x !! (fn () => raise Impossible "get_basic_sort_IUVar")
  in
    (IUVar data, foldl (fn ((_, bs_arg), acc) => BSArrow (bs_arg, acc)) bs_ret ctx)
  end

fun match_BSArrow gctx ctx r bs =
  case update_bs bs of
      BSArrow data => data
    | _ => raise Impossible $ "match_BSArrow: " ^ str_bs bs

fun get_sort_type_SUVar gctx ctx data = SUVar data

(* type state = (scontext * prop) list *)
(* val vcs : state ref = ref [] *)
(* val admits : state ref = ref [] *)
                             
(* fun check_prop ctx p = push_ref vcs (ctx, p) *)
(* fun add_admit p = push_ref admits (ctx, p)                *)
fun check_prop p =
  (println $ "write_prop: " ^ (ToString.str_p Gctx.empty [] $ Simp.simp_p p);
  write_prop (p, get_region_p p))
fun add_admit p = write_admit (p, get_region_p p)
                         
structure Sortcheck = SortcheckFn (structure U = Expr
                                   structure T = Expr
                                   type sigcontext = sigcontext
                                   val str_bs = str_bs
                                   val str_i = str_i
                                   val str_s = str_s
                                   val U_str_i = str_i
                                   val fetch_sort = fetch_sort
                                   val is_wf_basic_sort_BSUVar = is_wf_basic_sort_BSUVar
                                   val get_basic_sort_IUVar = get_basic_sort_IUVar
                                   val match_BSArrow = match_BSArrow
                                   val get_sort_type_SUVar = get_sort_type_SUVar
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
                                   val write_admit = fn _ => fn a => write_admit a
                                   val write_prop = fn _ => fn a => write_prop a
                                   val get_uvar_info = get_uvar_info
                                   val refine = refine
                                  )
open Sortcheck

open MicroTiMLLongId
open MicroTiMLUtilTiML
open MicroTiMLUtil
open MicroTiML

fun sc ctx i = get_basic_sort Gctx.empty (ctx, i)
fun sc_against_sort ctx (i, s) = check_sort Gctx.empty (ctx, i, s)

fun is_wf_sort ctx s = Sortcheck.is_wf_sort Gctx.empty (ctx, s)

val STime = STime dummy
val SNat = SNat dummy
val SBool = SBool dummy
val SUnit = SUnit dummy

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

fun sc_against_Time_Nat ictx (i, j) =
  (sc_against_sort ictx (i, STime),
   sc_against_sort ictx (j, SNat))

fun is_eq_basic_sort x = unify_bs dummy x
  
fun BasicSort b = SBasic (b, dummy)

fun is_state i =
    case i of
        IBinOp (IBUnion (), _, _) => true
      | IState _ => true
      | _ => false
               
fun check_same_domain pre_st st =
    let
      val (pre_vars, _, pre_map) = decompose_state pre_st
      val (st_vars, _, st_map) = decompose_state st
      val () = assert_b "ISet.equal" $ ISet.equal (pre_vars, st_vars)
      val () = assert_b "SMapU.is_same_domain" $ SMapU.is_same_domain pre_map st_map
    in
      (pre_map, st_map)
    end
fun check_sub_map (pre_st, st) =
  StMap.appi (fn (k, v) => check_prop $ v %= st @!! k) pre_st
             
fun is_eq_idx (i, i') =
    if is_state i orelse is_state i' then
      let
        val (m, m') = check_same_domain i i'
      in
        check_sub_map (m, m')
      end
    else
      check_prop (i %= i')

open Bind
       
val open_s = open_sorting
               
fun is_eq_sort (s, s') =
  case (s, s') of
      (SBasic (bs, _), SBasic (bs', _)) =>
      is_eq_basic_sort (bs, bs')
    | (SSubset ((bs, r1), Bind ((name, _), p), _), SSubset ((bs', _), Bind (_, p'), _)) =>
      let
	val () = is_eq_basic_sort (bs, bs')
        val () = open_s (name, BasicSort bs)
	val () = check_prop (p --> p')
        val () = close ()
      in
        ()
      end
    | (SSubset ((bs, r1), Bind ((name, _), p), _), SBasic (bs', _)) =>
      let
	val () = is_eq_basic_sort (bs, bs')
      in
        ()
      end
    | (SBasic (bs, r1), SSubset ((bs', _), Bind ((name, _), p), _)) =>
      let
	val () = is_eq_basic_sort (bs, bs')
        val () = open_s (name, BasicSort bs)
	val () = check_prop p
        val () = close ()
      in
        ()
      end
    | _ => raise MTCError "is_eq_sort"
                                       
fun get_ty_const_kind c = KType ()
  (* case c of *)
  (*     TCUnit => KType *)
  (*   | TCEmpty => KType *)
  (*   | TCInt => KType *)
  (*   | TCString => KType *)

fun get_ty_bin_op_arg1_kind opr =
  case opr of
      TBProd () => KType ()
    | TBSum () => KType ()
                 
fun get_ty_bin_op_arg2_kind opr =
  case opr of
      TBProd () => KType ()
    | TBSum () => KType ()
                 
fun get_ty_bin_op_res_kind opr =
  case opr of
      TBProd () => KType ()
    | TBSum () => KType ()

fun nth_error_local ls x =
  case x of
      ID (n, _) => nth_error ls n
    | QID _ => raise MTCError "nth_error QID"
                      
type icontext = (string * sort) list
type tcontext = (string * basic_sort kind) list
                            
fun add_sorting_it new (ictx, tctx) = (new :: ictx, tctx)
fun add_kinding_it new (ictx, tctx) = (ictx, new :: tctx)

fun ictx_names ictx = map fst ictx
fun itctx_names (ictx, tctx) = (map fst ictx, map fst tctx)
                                 
(* (***************** the "subst_i_t" visitor  **********************)     *)

(* fun subst_i_ty_visitor_vtable cast ((subst_i_i, subst_i_s), d, x, v) : ('this, int, 'var, 'basic_sort, 'idx, 'sort, 'var, 'basic_sort, 'idx2, 'sort2) ty_visitor_vtable = *)
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

fun ctx_names (ictx, tctx, ectx(* , _ *)) = (map fst ictx, map fst tctx, [], map fst ectx)
                                   
fun is_sub_map_k eq (m, m') return =
  (Rctx.appi (fn (k, v) =>
                 case Rctx.find (m', k) of
                     SOME v' => if eq (v, v') then () else return false
                   | NONE => return false
             ) m;
   true)
fun is_sub_map eq (m, m') = ContUtil.callret $ is_sub_map_k eq (m, m')
                                             
fun assert_sub_map err eq (m, m') =
  Rctx.appi (fn (k, v) =>
                case Rctx.find (m', k) of
                    SOME v' => eq (v, v')
                  | NONE => raise err ()
            ) m

fun is_eq_list msg f a = ListPair.appEq f a handle ListPair.UnequalLengths => raise Impossible msg

fun is_eq_ty_visitor2_vtable cast () =
    let
      fun adapt f this env a a' = (f (a, a'); a)
      val vtable =
          default_ty_visitor2_vtable
            cast
            extend_noop
            extend_noop
            (adapt eq_var)
            (adapt is_eq_basic_sort)
            (adapt is_eq_idx)
            (adapt is_eq_sort)
      fun visit2_ibind_anno get_sort this visit_anno visit_body env bind bind' =
          let
            val (a, (name, t)) = unBindAnnoName bind
            val (a', (name', t')) = unBindAnnoName bind'
            val a = visit_anno env a a'
            val () = open_sorting (fst name, get_sort a)
            val t = visit_body env t t'
            val () = close ()
          in
            IBindAnno ((name, a), t)
          end
      val vtable = override_visit2_ibind_anno_sort vtable $ visit2_ibind_anno id
      val vtable = override_visit2_ibind_anno_bsort vtable $ visit2_ibind_anno (fn bs => SBasic (bs, dummy))
    in
      vtable
    end

fun new_is_eq_ty_visitor2 a = new_ty_visitor2 is_eq_ty_visitor2_vtable a

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
    fun err msg =
        raise MTCError $ sprintf "Error: $\nin is_eq_ty() with\n  $  $"
              [
                msg,
                ExportPP.pp_t_to_string NONE $ ExportPP.export_t NONE (itctx_names ctx) t,
                ExportPP.pp_t_to_string NONE $ ExportPP.export_t NONE (itctx_names ctx) t'
              ]
    val visitor2 as (TyVisitor2 vtable) = new_is_eq_ty_visitor2 ()
  in
    ignore $ #visit2_ty vtable visitor2 () t t'
    handle Visitor2Error msg => err msg
  end

fun is_eq_kind (k, k') =
    let
      val visitor2 as (TyVisitor2 vtable) = new_is_eq_ty_visitor2 ()
    in
      ignore $ #visit2_kind vtable visitor2 () k k'
      handle Visitor2Error msg => raise MTCError $ "Can't unify kinds because: " ^ msg
    end
    
fun is_sub_rctx ctx (rctx, rctx_abs) =
  assert_sub_map (fn () => Impossible "is_sub_rctx()") (fn (t_abs, t) => is_eq_ty ctx (t, t_abs)) (rctx_abs, rctx)
  
fun is_eq_tys ctx a = is_eq_list "is_eq_tys()/unequal-lengths" (is_eq_ty ctx) a

fun kc (* st_types *) (ctx as (ictx, tctx) : icontext * tcontext) t_input =
  let
    (* val kc = kc st_types *)
    (* fun check_state_field x = *)
    (*   if Option.isSome $ st_types @! x then () *)
    (*   else raise Impossible $ sprintf "state field $ not found" [x] *)
    fun main () =
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
    | TArrow ((i1, t1), i, (i2, t2)) =>
      let
        val i1 = sc_against_sort ictx (i1, SState)
        val t1 = kc_against_kind ctx (t1, KType ())
        val i = sc_against_Time_Nat ictx i
        val i2 = sc_against_sort ictx (i2, SState)
        val t2 = kc_against_kind ctx (t2, KType ())
      in
        (TArrow ((i1, t1), i, (i2, t2)), KType ())
      end
    | TAbsI data =>
      let
        val (b, (name, t)) = unTAbsI data
        val (t, k) = open_close add_sorting_it (fst name, BasicSort b) ctx (fn ctx => kc ctx t)
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
        val (s, (name, (i, t))) = unTQuanI data
        val s = is_wf_sort ictx s
        val t = open_close add_sorting_it (fst name, s) ctx
                           (fn ctx as (ictx, _) =>
                               (sc_against_Time_Nat ictx i,
                                kc_against_kind ctx (t, KType ())))
      in
        (TQuanI (q, IBindAnno ((name, s), t)), KType ())
      end
    | TQuan (q, i, data) =>
      let
        val i = sc_against_Time_Nat ictx i
        val (k, (name, t)) = unTQuan data
        val t = kc_against_kind (add_kinding_it (fst name, k) ctx) (t, KType ())
      in
        (TQuan (q, i, TBindAnno ((name, k), t)), KType ())
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
        (TNat i, KType ())
      end
    | TiBool i =>
      let
        val i = sc_against_sort ictx (i, SBool)
      in
        (TiBool i, KType ())
      end
    | TArr (t, i) =>
      let
        val t = kc_against_kind ctx (t, KType ())
        val i = sc_against_sort ictx (i, SNat)
      in
        (TArr (t, i), KType ())
      end
    | TPreArray (t, len, i, b) =>
      let
        val t = kc_against_kind ctx (t, KType ())
        val len = sc_against_sort ictx (len, SNat)
        val i = sc_against_sort ictx (i, SNat)
      in
        (TPreArray (t, len, i, b), KType ())
      end
    | TArrayPtr (t, len, i) =>
      let
        val t = kc_against_kind ctx (t, KType ())
        val len = sc_against_sort ictx (len, SNat)
        val i = sc_against_sort ictx (i, SNat)
      in
        (TArrayPtr (t, len, i), KType ())
      end
    | TTuplePtr (ts, i, b) =>
      let
        val ts = map (kc_against_KType ctx) ts
        val i = sc_against_sort ictx (i, SNat)
      in
        (TTuplePtr (ts, i, b), KType ())
      end
    | TTuple ts =>
      let
        val ts = map (kc_against_KType ctx) ts
      in
        (TTuple ts, KType ())
      end
    | TPreTuple (ts, i, i2) =>
      let
        val ts = map (kc_against_KType ctx) ts
        val i = sc_against_sort ictx (i, SNat)
        val i2 = sc_against_sort ictx (i2, SNat)
      in
        (TPreTuple (ts, i, i2), KType ())
      end
    | TProdEx ((t1, b1), (t2, b2)) =>
      let
        val t1 = kc_against_kind ctx (t1, KType ())
        val t2 = kc_against_kind ctx (t2, KType ())
      in
        (TProdEx ((t1, b1), (t2, b2)), KType ())
      end
    | TArrowTAL (ts, i) =>
      let
        val ts = Rctx.map (fn t => kc_against_kind ctx (t, KType ())) ts
        val i = sc_against_sort ictx (i, STime)
      in
        (TArrowTAL (ts, i), KType ())
      end
    | TArrowEVM (st, rctx, ts, i) =>
      let
        val st = sc_against_sort ictx (st, SState)
        val rctx = Rctx.map (fn t => kc_against_kind ctx (t, KType ())) rctx
        val ts = map (kc_against_KType ctx) ts
        val i = sc_against_Time_Nat ictx i
      in
        (TArrowEVM (st, rctx, ts, i), KType ())
      end
    | TMap t => (TMap $ kc_against_KType ctx t, KType ())
    | TState x => 
      let
        (* val () = check_state_field x *)
      in
	(TState x, KType ())
      end
    | TVectorPtr (x, i) => 
      let
        (* val () = check_state_field x *)
        val i = sc_against_sort ictx (i, SNat)
      in
	(TVectorPtr (x, i), KType ())
      end
    fun extra_msg () = "\nwhen kindchecking: " ^ (ExportPP.pp_t_to_string NONE $ ExportPP.export_t NONE (itctx_names ctx) t_input)
    val ret = main ()
              handle
              Impossible m => raise Impossible (m ^ extra_msg ())
              | MUnifyError (r, m) => raise MTCError ("Unification error:\n" ^ join_lines m ^ extra_msg ())
              (* | ForgetError (r, m) => raise MTCError ("Forgetting error: " ^ m ^ extra_msg ()) *)
              (* | MSCError (r, m) => raise MTCError ("Sortcheck error:\n" ^ join_lines m ^ extra_msg ()) *)
              (* | MTCError m => raise MTCError (m ^ extra_msg ()) *)
  in
    ret
  end

and kc_against_kind ctx (t, k) =
  let
    val (t, k') = kc ctx t
    val () = is_eq_kind (k', k)
  in
    t
  end

and kc_against_KType ctx t = kc_against_kind ctx (t, KType ())
                                             
fun forget_i_t a = shift_i_t_fn (forget_i_i, forget_i_s) a
fun forget_t_t a = shift_t_t_fn forget_var a
                               
fun forget01_i_i x = forget_i_i 0 1 x
fun forget01_i_s x = forget_i_s 0 1 x
fun forget01_i_t x = forget_i_t 0 1 x
fun forget01_t_t x = forget_t_t 0 1 x

fun forget01_i_2i a = unop_pair forget01_i_i a
                                
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
      ECTT () => TUnit
    | ECNat n => TNat $ INat n
    | ECiBool b => TiBool $ IBool b
    | ECInt _ => TInt
    | ECBool _ => TBool
    | ECByte _ => TByte
    (* | ECString _ => TString *)

fun get_prim_expr_un_op_arg_ty opr =
  case opr of
      EUPIntNeg () => TInt
    | EUPBoolNeg () => TBool
    | EUPInt2Byte () => TInt
    | EUPByte2Int () => TByte
    (* | EUPInt2Str () => TInt *)
    (* | EUPStrLen () => TString *)
               
fun get_prim_expr_un_op_res_ty opr =
  case opr of
      EUPIntNeg () => TInt
    | EUPBoolNeg () => TBool
    | EUPInt2Byte () => TByte
    | EUPByte2Int () => TInt
    (* | EUPInt2Str () => TString *)
    (* | EUPStrLen () => TInt *)
               
fun get_prim_expr_bin_op_arg1_ty opr =
  case opr of
      EBPIntAdd () => TInt
    | EBPIntMult () => TInt
    | EBPIntMinus () => TInt
    | EBPIntDiv () => TInt
    | EBPIntMod () => TInt
    | EBPIntLt () => TInt
    | EBPIntGt () => TInt
    | EBPIntLe () => TInt
    | EBPIntGe () => TInt
    | EBPIntEq () => TInt
    | EBPIntNEq () => TInt
    | EBPBoolAnd () => TBool
    | EBPBoolOr () => TBool
    (* | EBPStrConcat () => TString *)
      
fun get_prim_expr_bin_op_arg2_ty opr =
  case opr of
      EBPIntAdd () => TInt
    | EBPIntMult () => TInt
    | EBPIntMinus () => TInt
    | EBPIntDiv () => TInt
    | EBPIntMod () => TInt
    | EBPIntLt () => TInt
    | EBPIntGt () => TInt
    | EBPIntLe () => TInt
    | EBPIntGe () => TInt
    | EBPIntEq () => TInt
    | EBPIntNEq () => TInt
    | EBPBoolAnd () => TBool
    | EBPBoolOr () => TBool
    (* | EBPStrConcat () => TString *)
      
fun get_prim_expr_bin_op_res_ty opr =
  case opr of
      EBPIntAdd () => TInt
    | EBPIntMult () => TInt
    | EBPIntMinus () => TInt
    | EBPIntDiv () => TInt
    | EBPIntMod () => TInt
    | EBPIntLt () => TBool
    | EBPIntGt () => TBool
    | EBPIntLe () => TBool
    | EBPIntGe () => TBool
    | EBPIntEq () => TBool
    | EBPIntNEq () => TBool
    | EBPBoolAnd () => TBool
    | EBPBoolOr () => TBool
    (* | EBPStrConcat () => TString *)

val T0 = T0 dummy
val T1 = T1 dummy
val N0 = N0 dummy
val N1 = N1 dummy
val TN0 = TN0 dummy

(* structure IntMap = IntBinaryMap *)
(* structure HeapMap = IntMap *)

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
infix 0 |>
infix 0 |#
infix 0 %~
infix 0 |>#
        
fun assert_TMap t =
  case t of
      TMap a => a
    | _ => raise assert_fail $ "assert_TMap; got: " ^ (ExportPP.pp_t_to_string NONE $ ExportPP.export_t NONE ([], []) t)

(* fun TCell t = TTuplePtr ([t], N0) *)
fun assert_TCell t =
  let
    fun err () = raise Impossible "assert_TCell"
  in
    case t of
        TTuplePtr (ts, offset, true) =>
        (case Simp.simp_i offset of
             IConst (ICNat n, _) =>
             (* todo: [ts] may contain embeded structs, so offset calculation may be more involved than this *)
             (case nth_error ts n of
                  SOME t => t
                | NONE => err ())
           | _ => err ())
      | _ => err ()
  end

infix 6 %%+

val N : nat -> idx = INat
val T : TimeType.time -> idx = ITime
                
fun TN n = (to_real n, N0)

val anno_EVar = ref false
val anno_EProj = ref false
val anno_EFold = ref false
val anno_EUnfold = ref false
val anno_EApp = ref false
val anno_EPair = ref false
val anno_EInj = ref false
val anno_EBPrim = ref false
val anno_ENew = ref false
val anno_ERead = ref false
val anno_ENat = ref false
val anno_ENatCmp = ref false
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
val anno_EHalt = ref false
val anno_ECase_e2_time = ref false
val anno_EIte_e2_time = ref false
val anno_EIfi_e2_time = ref false
val anno_EIfi = ref false
val anno_EVectorSet = ref false
val anno_EMapPtr = ref false
val anno_EVectorGet = ref false
val anno_EVectorPushBack = ref false
val anno_EStorageSet = ref false
val anno_EUPrim = ref false
val anno_EArrayLen = ref false
val anno_ENat2Int = ref false
val anno_EStorageGet = ref false
val anno_EVectorLen = ref false
val anno_EVectorClear = ref false

val anno_EProj_state = ref false
val anno_EPrintc_state = ref false
val anno_EUPrim_state = ref false
val anno_EArrayLen_state = ref false
val anno_ENat2Int_state = ref false
val anno_EInt2Nat_state = ref false
val anno_EStorageGet_state = ref false
val anno_EInj_state = ref false
val anno_EFold_state = ref false
val anno_EUnfold_state = ref false
val anno_EApp_state = ref false
val anno_EPair_state = ref false
val anno_EBPrim_state = ref false
val anno_ENew_state = ref false
val anno_ERead_state = ref false
val anno_EMapPtr_state = ref false
val anno_EVectorGet_state = ref false
val anno_EVectorPushBack_state = ref false
val anno_EVectorSet_state = ref false
val anno_EStorageSet_state = ref false
val anno_ENat_state = ref false
val anno_ENatCmp_state = ref false
val anno_EWrite_state = ref false
val anno_ECase_state = ref false
val anno_EIte_state = ref false
val anno_EIfi_state = ref false
val anno_EAppT_state = ref false
val anno_EAppI_state = ref false
val anno_EPack_state = ref false
val anno_EPackI_state = ref false
val anno_EUnpack_state = ref false
val anno_EUnpackI_state = ref false
val anno_ELet_state = ref false
val anno_ENewArrayValues_state = ref false
val anno_EHalt_state = ref false
val anno_EAbs_state = ref false
val anno_EVectorLen_state = ref false
val anno_EVectorClear_state = ref false

val allow_substate_call = ref false

datatype phase =
         PhBeforeCPS of unit
         | PhBeforeCC of unit
         | PhBeforeCodeGen of unit

val phase = ref $ PhBeforeCPS ()

fun tc st_types (ctx as (ictx, tctx, ectx : econtext), st : idx) e_input =
  let
    val tc = tc st_types
    val tc_against_ty = tc_against_ty st_types
    val tc_against_ty_time = tc_against_ty_time st_types
    val tc_against_time = tc_against_time st_types
    val tc_against_time_space = tc_against_time_space st_types
    val tc_against_ty_time_space = tc_against_ty_time_space st_types
    val () = println "tc() start: "
    val e_input_str = ExportPP.pp_e_to_string (NONE, NONE) $ ExportPP.export (SOME 4, SOME 4) (ctx_names ctx) e_input
    val () = print $ e_input_str
    fun err () = raise Impossible $ "unknown case in tc: " ^ (ExportPP.pp_e_to_string (NONE, NONE) $ ExportPP.export (NONE, NONE) (ctx_names ctx) e_input)
    val itctx = (ictx, tctx)
    fun get_vector t1 =
      let
        val x = assert_TState t1 
        val t = assert_fst_false $ st_types @!! x 
        val len = st @%!! x
      in
        (x, t, len)
      end
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
               (e, t, TN C_EVar, st) 
             end
           | NONE => raise MTCError "Unbound term variable"
        )
      | EConst c => (e_input, get_expr_const_type c, TN C_EConst, st)
      | EUnOp (EUTiML (EUProj proj), e) =>
        let
          val (e, t_e, i, st) = tc (ctx, st) e
          val t_e = whnf itctx t_e
          val (t1, t2) = case t_e of
                             TBinOp (TBProd (), t1, t2) => (t1, t2)
                           | _ => raise MTCError "EProj"
          val e = if !anno_EProj then e %: t_e else e
          val e = if !anno_EProj_state then e %~ st else e
        in
          (EProj (proj, e), choose (t1, t2) proj, i %%+ TN C_EProj, st)
        end
      | EUnOp (EUTupleProj n, e) =>
        let
          val (e, t_e, i, st) = tc (ctx, st) e
          val t_e = whnf itctx t_e
          val ts = assert_TTuple t_e
          val t = assert_SOME $ nth_error ts n 
          val e = if !anno_EProj then e %: t_e else e
          val e = if !anno_EProj_state then e %~ st else e
        in
          (EUnOp (EUTupleProj n, e), t, i %%+ TN C_ETupleProj, st)
        end
      | EUnOp (EUTiML (EUPrintc ()), e) =>
        let
          val (e, i, st) = tc_against_ty (ctx, st) (e, TByte)
          val e = if !anno_EPrintc_state then e %~ st else e
        in
          (EUnOp (EUTiML (EUPrintc ()), e), TUnit, i %%+ TN C_EPrintc, st)
        end
      | EUnOp (EUTiML (EUPrim opr), e) =>
        let
          val t_e = get_prim_expr_un_op_arg_ty opr
          val (e, i, st) = tc_against_ty (ctx, st) (e, t_e)
          val e = if !anno_EUPrim then e %: t_e else e
          val e = if !anno_EUPrim_state then e %~ st else e
        in
          (EUnOp (EUTiML (EUPrim opr), e), get_prim_expr_un_op_res_ty opr, i %%+ TN (C_EUPrim opr), st)
        end
      | EUnOp (EUTiML (EUArrayLen ()), e) =>
        let
          val (e, t, j, st) = tc (ctx, st) e
          val t = whnf itctx t
          val (_, i) = case t of
                            TArr data => data
                          | _ => raise MTCError "EArrayLen"
          val e = if !anno_EArrayLen then e %: t else e
          val e = if !anno_EArrayLen_state then e %~ st else e
        in
          (EUnOp (EUTiML (EUArrayLen ()), e), TNat i, j %%+ TN C_EArrayLen, st)
        end
      | EUnOp (EUTiML (EUNat2Int ()), e) =>
        let
          val (e, t, j, st) = tc (ctx, st) e
          val t = whnf itctx t
          val i = case t of
                            TNat data => data
                          | _ => raise MTCError "ENat2Int"
          val e = if !anno_ENat2Int then e %: t else e
          val e = if !anno_ENat2Int_state then e %~ st else e
        in
          (EUnOp (EUTiML (EUNat2Int ()), e), TInt, j %%+ TN C_ENat2Int, st)
        end
      | EUnOp (EUTiML (EUInt2Nat ()), e) =>
        let
          val () = println "begin Int2Nat"
          val (e, j, st) = tc_against_ty (ctx, st) (e, TInt)
          val () = println "end Int2Nat"
          val e = if !anno_EInt2Nat_state then e %~ st else e
        in
          (EUnOp (EUTiML (EUInt2Nat ()), e), TSomeNat (), j %%+ TN C_EInt2Nat, st)
        end
      | EUnOp (opr as EUTiML (EUStorageGet ()), e) =>
        let
          val (e, t_e, j, st) = tc (ctx, st) e
          val t_e = whnf itctx t_e
          val t = assert_TCell t_e
          val e = if !anno_EStorageGet then e %: t_e else e
          val e = if !anno_EStorageGet_state then e %~ st else e
        in
          (EUnOp (opr, e), t, j %%+ TN C_EStorageGet, st)
        end
      | EUnOp (EUInj (inj, t'), e) =>
        let
          val t' = kc_against_kind itctx (t', KType ())
          val (e, t, i, st) = tc (ctx, st) e
          val e = if !anno_EInj then e %: t else e
          val e = if !anno_EInj_state then e %~ st else e
        in
          (EInj (inj, t', e), TSum $ choose_pair_inj (t, t') inj, i %%+ mapPair' to_real N (C_EInj, 2), st)
        end
      | EUnOp (EUFold t', e) =>
        let
          val t' = kc_against_kind itctx (t', KType ())
          val t' = whnf itctx t'
          val (t, args) = collect_TAppIT t'
          val (k, (_, t1)) = case t of
                                 TRec data => unBindAnnoName data
                               | _ => raise MTCError "EFold"
          val t = TAppITs (subst0_t_t t t1) args
          (* val () = println "EFold: before tc_against_ty" *)
          (* val () = println $ "EFold: " ^ (ExportPP.pp_t_to_string $ ExportPP.export_t (itctx_names itctx) t) *)
          val (e, i, st) = tc_against_ty (ctx, st) (e, t) 
          (* val () = println "EFold: after tc_against_ty" *)
          val e = if !anno_EFold then e %: t else e
          val e = if !anno_EFold_state then e %~ st else e
        in
          (EFold (t', e), t', i %%+ TN C_EFold, st)
        end
      | EUnOp (EUUnfold (), e) =>
        let
          val (e, t_e, i, st) = tc (ctx, st) e
          val t_e = whnf itctx t_e
          val (t, args) = collect_TAppIT t_e
          val (k, (_, t1)) = case t of
                                 TRec data => unBindAnnoName data
                               | _ => raise MTCError "EUnfold"
          val e = if !anno_EUnfold then e %: t_e else e
          val e = if !anno_EUnfold_state then e %~ st else e
        in
          (EUnfold e, TAppITs (subst0_t_t t t1) args, i %%+ TN C_EUnfold, st)
        end
      | ETriOp (ETIte (), e, e1, e2) =>
        let
          val (e, t_e, i, st) = tc (ctx, st) e
          val t_e = whnf itctx t_e
          val () = assert_TBool t_e
          val (e1, t, i1, st1) = tc (ctx, st) e1
          val (e2, i2, st2) = tc_against_ty (ctx, st) (e2, t)
          val () = is_eq_idx (st2, st1)
          val (cost, e2) =
              case !phase of
                  PhBeforeCodeGen () => ((C_Ite_BeforeCodeGen, 0), e2)
                | PhBeforeCC () => ((C_Ite_BeforeCodeGen, 0), e2)
                | PhBeforeCPS () =>
                  let
                    val (e2, n_live_vars) = assert_EAnnoLiveVars e2
                  in
                    ((C_Ite_BeforeCPS n_live_vars, M_Ite_BeforeCPS n_live_vars), e2)
                  end
          val e2 = if !anno_EIte_e2_time then e2 |># i2 else e2
          val e = if !anno_EIte_state then e %~ st else e
        in
          (ETriOp (ETIte (), e, e1, e2), t, i %%+ mapPair' to_real N cost %%+ IMaxPair (i1, TN C_JUMPDEST %%+ i2), st1)
        end
      | ECase data =>
        let
          val (e, (name1, e1), (name2, e2)) = unECase data
          val (e, t_e, i, st) = tc (ctx, st) e
          val t_e = whnf itctx t_e
          val (t1, t2) = assert_TSum t_e
          val (e1, t, i1, st1) = tc (add_typing_full (fst name1, t1) ctx, st) e1
          val (e2, i2, st2) = tc_against_ty (add_typing_full (fst name2, t2) ctx, st) (e2, t)
          val () = is_eq_idx (st2, st1)
          val (cost, e2) =
              case !phase of
                  PhBeforeCodeGen () => ((C_Case_BeforeCodeGen, 0), e2)
                | PhBeforeCC () => ((C_Case_BeforeCodeGen, 0), e2)
                | PhBeforeCPS () =>
                  let
                    val (e2, n_live_vars) = assert_EAnnoLiveVars e2
                  in
                    ((C_Case_BeforeCPS n_live_vars, M_Case_BeforeCPS n_live_vars), e2)
                  end
          val e2 = if !anno_ECase_e2_time then e2 |># i2 else e2
          val e = if !anno_ECase then e %: t_e else e
          val e = if !anno_ECase_state then e %~ st else e
        in
          (MakeECase (e, (name1, e1), (name2, e2)), t, i %%+ mapPair' to_real N cost %%+ IMaxPair (i1, TN C_JUMPDEST %%+ i2), st1)
        end
      | EBinOp (EBApp (), e1, e2) =>
        let
          val (e1, t_e1, i1, st) = tc (ctx, st) e1
          val st_e1 = st
          val (e2, t_e2, i2, st) = tc (ctx, st) e2
          val st_e2 = st
          fun check_sub_state pre_st st =
            let
              val st = shift_i_i st
              val (pre_vars, pre_vars_info, pre_map) = decompose_state pre_st
              val (st_vars, st_vars_info, st_map) = decompose_state st
              val pre_vars_minus_0 = ISetU.delete (pre_vars, 0)
              val () = assert_b "check_sub_state()/isSubset" $ ISet.isSubset (pre_vars_minus_0, st_vars)
              val diff_vars = ISet.difference (st_vars, pre_vars_minus_0)
              val () = assert_b "check_sub_state()/is_sub_domain" $ SMapU.is_sub_domain pre_map st_map
              val diff_map = st_map @-- pre_map
              val () = if not $ ISet.member(pre_vars, 0) andalso SMap.numItems diff_map + ISet.numItems diff_vars > 0 then
                         raise Impossible "callee's precondition is bigger than current state"
                       else ()
              val () = check_sub_map (pre_map, st_map)
              val diff_vars = ISet.map dec diff_vars
              val diff_map = SMap.map forget01_i_i diff_map
            in
              compose_state (diff_vars, IMapU.fromList $ map (fn (n, sorts) => (dec n, map forget01_i_s sorts)) $ IMap.listItemsi st_vars_info, diff_map)
            end
          val t_e1 = whnf itctx t_e1
          val (((pre_st, t1), i, (post_st, t2)), st, (e1, t_e1)) =
              case t_e1 of
                  TArrow (data as ((pre_st, t1), i, (post_st, t2))) =>
                  if !allow_substate_call then
                    let
                      fun check_sub_domain pre_st st =
                          let
                            val (pre_vars, _, pre_map) = decompose_state pre_st
                            val (st_vars, vars_info, st_map) = decompose_state st
                            val () = assert_b "ISet.isSubset" $ ISet.isSubset (pre_vars, st_vars)
                            val () = assert_b "SMapU.is_sub_domain" $ SMapU.is_sub_domain pre_map st_map
                          in
                            (pre_map, st_map, (ISet.difference (st_vars, pre_vars), vars_info, st_map @-- pre_map))
                          end
                      val (pre_map, st_map, diff) = check_sub_domain pre_st st
                      val () = check_sub_map (pre_map, st_map)
                      val st = IUnion_simp (compose_state diff, post_st)
                    in
                      (data, st, (e1, t_e1))
                    end
                  else
                    let
                      val () = is_eq_idx (st, pre_st)
                    in
                      (data, post_st, (e1, t_e1))
                    end
                | TQuanI (Forall (), bind) =>
                  let
                    val ((_, s), (_, t)) = unBindAnno bind
                    val () = is_eq_sort (s, SState)
                    val ((pre_st, _), _, _) = assert_TArrow t
                    val diff = check_sub_state pre_st st
                    val t = subst0_i_t diff t
                    val data as ((pre_st, t1), i, (post_st, t2)) = assert_TArrow t
                    val st = post_st
                  in
                    (data, st, (EAppI (e1, diff), t))
                  end
                | _ => raise MTCError "EApp"
          val () = is_eq_ty itctx (t_e2, t1)
          val (cost, e2) = 
              case !phase of
                  PhBeforeCodeGen () => ((C_App_BeforeCodeGen, 0), e2)
                | PhBeforeCC () => ((C_App_BeforeCC, M_App_BeforeCC), e2)
                | PhBeforeCPS () =>
                  let
                    val (e2, n_live_vars) = assert_EAnnoLiveVars e2
                  in
                    ((C_App_BeforeCPS n_live_vars, M_App_BeforeCPS n_live_vars), e2)
                  end
          val e1 = if !anno_EApp then e1 %: t_e1 else e1
          val (e1, e2) = if !anno_EApp_state then (e1 %~ st_e1, e2 %~ st_e2) else (e1, e2)
        in
          (EApp (e1, e2), t2, i1 %%+ i2 %%+ mapPair' to_real N cost %%+ i, st)
        end
      | EAppT (e, t1) =>
        let
          val (e, t_e, j, st) = tc (ctx, st) e
          val t_e = whnf itctx t_e
          val (_, k, j2, t) = assert_TForall t_e
          val t1 = kc_against_kind itctx (t1, k)
          val (cost, e) = 
              case !phase of
                  PhBeforeCodeGen () => ((0, 0), e)
                | PhBeforeCC () => ((0, 0), e)
                | PhBeforeCPS () =>
                  let
                    val (e, n_live_vars) = assert_EAnnoLiveVars e
                  in
                    ((C_AppI_BeforeCPS n_live_vars, M_AppI_BeforeCPS n_live_vars), e)
                  end
          val e = if !anno_EAppT then e %: t_e else e
          val e = if !anno_EAppT_state then e %~ st else e
        in
          (EAppT (e, t1), subst0_t_t t1 t, j %%+ mapPair' to_real N cost %%+ j2, st)
        end
      | EAppI (e, i) =>
        let
          val (e, t_e, j, st) = tc (ctx, st) e
          val t_e = whnf itctx t_e
          val (_, s, j2, t) = assert_TForallI t_e
          val i = sc_against_sort ictx (i, s)
          val (cost, e) = 
              case !phase of
                  PhBeforeCodeGen () => ((0, 0), e)
                | PhBeforeCC () => ((0, 0), e)
                | PhBeforeCPS () =>
                  let
                    val (e, n_live_vars) = assert_EAnnoLiveVars e
                  in
                    ((C_AppI_BeforeCPS n_live_vars, M_AppI_BeforeCPS n_live_vars), e)
                  end
          val e = if !anno_EAppI then e %: t_e else e
          val e = if !anno_EAppI_state then e %~ st else e
        in
          (EAppI (e, i), subst0_i_t i t, j %%+ mapPair' to_real N cost %%+ subst0_i_2i i j2, st)
        end
      | EAbsI data =>
        let
          val (s, (name, e)) = unEAbsI data
          val () = assert_b "EAbsI: is_value e" (is_value e)
          val (e, n_fvars) =
              case !phase of
                  PhBeforeCodeGen () => (e, 0)
                | _ => assert_EAnnoFreeEVars e
          val s = is_wf_sort ictx s
          val (e, t, i, _) = open_close add_sorting_full (fst name, s) ctx (fn ctx => tc (ctx, IEmptyState) e)
          val inner_cost =
              case !phase of
                  PhBeforeCodeGen () => TN0
                | PhBeforeCC () => TN0
                | PhBeforeCPS () => i %%+ mapPair' to_real N (C_AbsI_Inner_BeforeCPS n_fvars, M_AbsI_Inner_BeforeCPS n_fvars)
          val cost =
              case !phase of
                  PhBeforeCodeGen () => TN0
                | PhBeforeCC () => forget01_i_2i i
                | PhBeforeCPS () => mapPair' to_real N (C_Abs_BeforeCC n_fvars, M_Abs_BeforeCC n_fvars)
        in
          (MakeEAbsI (name, s, e), MakeTForallI (s, name, inner_cost, t), cost, st)
        end
      | EAbsT data =>
        let
          val (k, (name, e)) = unEAbsT data
          val () = assert_b "EAbsT: is_value e" (is_value e)
          val (e, n_fvars) =
              case !phase of
                  PhBeforeCodeGen () => (e, 0)
                | _ => assert_EAnnoFreeEVars e
          val (e, t, i, _) = tc (add_kinding_full (fst name, k) ctx, IEmptyState) e
          val inner_cost =
              case !phase of
                  PhBeforeCodeGen () => TN0
                | PhBeforeCC () => TN0
                | PhBeforeCPS () => i %%+ mapPair' to_real N (C_AbsI_Inner_BeforeCPS n_fvars, M_AbsI_Inner_BeforeCPS n_fvars)
          val cost =
              case !phase of
                  PhBeforeCodeGen () => TN0
                | PhBeforeCC () => i
                | PhBeforeCPS () => mapPair' to_real N (C_Abs_BeforeCC n_fvars, M_Abs_BeforeCC n_fvars)
        in 
          (MakeEAbsT (name, k, e), MakeTForall (k, name, inner_cost, t), cost, st)
        end
      | EAbs (pre_st, bind) =>
        let
          val pre_st = sc_against_sort ictx (pre_st, SState)
          val (t1 : mtiml_ty, (name, e)) = unEAbs bind
          val (e, n_fvars) =
              case !phase of
                  PhBeforeCodeGen () => (e, 0)
                | _ => assert_EAnnoFreeEVars e
          val t1 = kc_against_kind itctx (t1, KType ())
          val (e, t2, i, post_st) = tc (add_typing_full (fst name, t1) ctx, pre_st) e
          val extra_inner_cost =
              case !phase of
                  PhBeforeCodeGen () => (C_Abs_Inner_BeforeCodeGen, 0)
                | PhBeforeCC () => (C_Abs_Inner_BeforeCC n_fvars, M_Abs_Inner_BeforeCC n_fvars)
                | PhBeforeCPS () => (C_Abs_Inner_BeforeCPS n_fvars, M_Abs_Inner_BeforeCPS n_fvars)
          val () = println $ "i = " ^ (ExportPP.str_i $ ExportPP.export_i (ictx_names ictx) $ fst i)
          val () = println $ "extra = " ^ str_int (fst extra_inner_cost)
          val () = println $ "n_fvars = " ^ str_int n_fvars
          val () = println $ "C_Abs_Inner_BeforeCC n_fvars = " ^ str_int (C_Abs_Inner_BeforeCC n_fvars)
          val i = i %%+ mapPair' to_real N extra_inner_cost              
          val e = if !anno_EAbs then e %: t2 |># i else e
          val e = if !anno_EAbs_state then e %~ post_st else e
          val cost =
              case !phase of
                  PhBeforeCodeGen () => (0, 0)
                | PhBeforeCC () => (C_Abs_BeforeCC n_fvars, M_Abs_BeforeCC n_fvars)
                | PhBeforeCPS () => (C_Abs_BeforeCC n_fvars, M_Abs_BeforeCC n_fvars)
        in
          (MakeEAbs (pre_st, name, t1, e), TArrow ((pre_st, t1), i, (post_st, t2)), mapPair' to_real N cost, st)
        end
      (* | EAbsI _ => *)
      (*   let *)
      (*     val (binds, e) = collect_EAbsI e_input *)
      (*     val regions = map (snd o fst) binds *)
      (*     val binds = map (mapFst fst) binds *)
      (*     fun is_wf_sorts ctx binds = *)
      (*         let *)
      (*           fun foo ((name, s), (binds, ctx)) = *)
      (*               let *)
      (*                 val s = is_wf_sort ctx s *)
      (*                 val bind = (name, s) *)
      (*                 val () = open_s bind *)
      (*               in *)
      (*                 (bind :: binds, bind :: ctx) *)
      (*               end *)
      (*           val (binds, ctx) = foldl foo ([], ctx) binds *)
      (*           val binds = rev binds *)
      (*         in *)
      (*           (binds, ctx) *)
      (*         end *)
      (*     val (binds, ictx) = is_wf_sorts ictx binds *)
      (*     val () = assert_b "EAbsI: is_value e" (is_value e) *)
      (*     val len_binds = length binds *)
      (*     val ectx = map (mapSnd (lazy_shift_i_t len_binds (* o trace_noln "." *))) ectx *)
      (*     val ctx = (ictx, tctx, ectx) *)
      (*     val (e, t, _) = tc_against_time_space (ctx, IEmptyState) (e, TN0) *)
      (*     val () = close_n len_binds *)
      (*     val binds = ListPair.mapEq (fn ((name, anno), r) => ((name, r), anno)) (binds, regions) *)
      (*   in *)
      (*     (EAbsIs (binds, e), TForallIs (binds, t), TN0, st) *)
      (*   end *)
      | ERec data =>
        let
          val (t, (name, e)) = unBindAnnoName data
          val () = println $ "tc() on: " ^ fst name
          fun collect_EAbsIT_ignore_Anno e =
            case e of
                EAbsI data =>
                let
                  val (s, (name, e)) = unEAbsI data
                  val (binds, e) = collect_EAbsIT_ignore_Anno e
                in
                  (inl (name, s) :: binds, e)
                end
              | EAbsT data =>
                let
                  val (k, (name, e)) = unEAbsT data
                  val (binds, e) = collect_EAbsIT_ignore_Anno e
                in
                  (inr (name, k) :: binds, e)
                end
              | EUnOp (EUTiML (EUAnno _), e) => collect_EAbsIT_ignore_Anno e
              | _ => ([], e)
          val () = case snd $ collect_EAbsIT_ignore_Anno e of
                       EAbs _ => ()
                     | _ => raise MTCError "ERec: body should be EAbsITMany (EAbs (...))"
          val t = kc_against_kind itctx (t, KType ())
          val (e, i, _) = tc_against_ty (add_typing_full (fst name, t) ctx, IEmptyState) (e, t)
        in
          (MakeERec (name, t, e), t, i, st)
        end
      | EBinOp (EBPair (), e1, e2) =>
        let
          val (e1, t1, i1, st) = tc (ctx, st) e1
          val st_e1 = st
          val (e2, t2, i2, st) = tc (ctx, st) e2
          val (e1, e2) = if !anno_EPair then (e1 %: t1, e2 %: t2) else (e1, e2)
          val (e1, e2) = if !anno_EPair_state then (e1 %~ st_e1, e2 %~ st) else (e1, e2)
        in
          (EPair (e1, e2), TProd (t1, t2), i1 %%+ i2 %%+ (to_real C_EPair, N 2), st)
        end
      | ETuple es =>
        let
          val (ls, st) = foldl (fn (e, (acc, st)) =>
                                           let val res as (e, t, i, st) = tc (ctx, st) e
                                           in (res :: acc, st) end) ([], st) es
          fun get_e (e, t, i, st) =
            let
              val e = if !anno_EPair then e %: t else e
            in
              if !anno_EPair_state then e %~ st else e
            end
          val len = length es
          val i = combine_IBAdd_Time_Nat $ map #3 ls
        in
          (ETuple (map get_e ls), TTuple (map #2 ls), i %%+ (to_real $ C_ETuple len, N len), st)
        end
      | EBinOp (EBPrim opr, e1, e2) =>
        let
          val t1 = get_prim_expr_bin_op_arg1_ty opr
          val (e1, i1, st) = tc_against_ty (ctx, st) (e1, t1)
          val st_e1 = st
          val t2 = get_prim_expr_bin_op_arg2_ty opr
          val (e2, i2, st) = tc_against_ty (ctx, st) (e2, t2)
          val (e1, e2) = if !anno_EBPrim then (e1 %: t1, e2 %: t2) else (e1, e2)
          val (e1, e2) = if !anno_EBPrim_state then (e1 %~ st_e1, e2 %~ st) else (e1, e2)
          val e = EBinOpPrim (opr, e1, e2)
          val t = get_prim_expr_bin_op_res_ty opr
        in
          (e, t, i1 %%+ i2 %%+ TN (C_EBPrim opr), st)
        end
      | EBinOp (EBNew (), e1, e2) =>
        let
          val (e1, t1, j1, st) = tc (ctx, st) e1
          val st_e1 = st
          val t1 = whnf itctx t1
          val len = assert_TNat t1
          val (e2, t2, j2, st) = tc (ctx, st) e2
          val (e1, e2) = if !anno_ENew then (e1 %: t1, e2 %: t2) else (e1, e2)
          val (e1, e2) = if !anno_ENew_state then (e1 %~ st_e1, e2 %~ st) else (e1, e2)
          val cost = N C_ENew_order0 %+ N C_ENew_order1 %* len
        in
          (ENew (e1, e2), TArr (t2, len), j1 %%+ j2 %%+ (IToReal (cost, dummy), len %+ N1), st)
        end
      | ENewArrayValues (t, es) =>
        let
          val t = kc_against_kind itctx (t, KType ())
          val (eis, st) =
              foldl (fn (e, (eis, st)) =>
                        let
                          val (e, i, st) = tc_against_ty (ctx, st) (e, t)
                          val e = if !anno_ENewArrayValues_state then e %~ st else e
                        in
                          ((e, i) :: eis, st)
                        end) ([], st) es
          val (es, is) = unzip $ rev eis
          val i = combine_IBAdd_Time_Nat is
          val len = length es
        in
          (ENewArrayValues (t, es), TArr (t, INat len), i %%+ (to_real $ C_ENewArrayValues len, N $ len + 1), st)
        end
      | EBinOp (EBRead (), e1, e2) =>
        let
          val (e1, t1, j1, st) = tc (ctx, st) e1
          val st_e1 = st
          val (t, i1) = case whnf itctx t1 of
                            TArr data => data
                          | _ => raise MTCError "ERead 1"
          val (e2, t2, j2, st) = tc (ctx, st) e2
          val t2 = whnf itctx t2
          val i2 = assert_TNat_m t2 (fn s => raise MTCError $ "ERead: " ^ s)
          val () = check_prop (i2 %< i1)
          val (e1, e2) = if !anno_ERead then (e1 %: t1, e2 %: t2) else (e1, e2)
          val (e1, e2) = if !anno_ERead_state then (e1 %~ st_e1, e2 %~ st) else (e1, e2)
        in
          (ERead (e1, e2), t, j1 %%+ j2 %%+ TN C_ERead, st)
        end
      | EBinOp (EBMapPtr (), e1, e2) =>
        let
          val (e1, t1, j1, st) = tc (ctx, st) e1
          val st_e1 = st
          val t1 = whnf itctx t1
          val t = case t1 of
                      TState x => assert_fst_true $ st_types @!! x 
                    | _ => assert_TMap $ assert_TCell t1
          val (e2, j2, st) = tc_against_ty (ctx, st) (e2, TInt)
          val (e1, e2) = if !anno_EMapPtr then (e1 %: t1, e2 %: TInt) else (e1, e2)
          val (e1, e2) = if !anno_EMapPtr_state then (e1 %~ st_e1, e2 %~ st) else (e1, e2)
        in
          (EBinOp (EBMapPtr (), e1, e2), t, j1 %%+ j2 %%+ TN C_EMapPtr, st)
        end
      | EBinOp (opr as EBVectorGet (), e1, e2) =>
        let
          val (e1, t1, j1, st) = tc (ctx, st) e1
          val st_e1 = st
          val (e2, t2, j2, st) = tc (ctx, st) e2
          val i = assert_TNat_m t2 (fn s => raise MTCError $ "EVectorGet: " ^ s)
          val (x, t, len) = get_vector $ whnf itctx t1
          val () = check_prop (i %< len)
          val (e1, e2) = if !anno_EVectorGet then (e1 %: t1, e2 %: t2) else (e1, e2)
          val (e1, e2) = if !anno_EVectorGet_state then (e1 %~ st_e1, e2 %~ st) else (e1, e2)
        in
          (EBinOp (opr, e1, e2), t, j1 %%+ j2 %%+ TN C_EVectorGet, st)
        end
      | EBinOp (opr as EBVectorPushBack (), e1, e2) =>
        let
          val (e1, t1, j1, st) = tc (ctx, st) e1
          val st_e1 = st
          val (e2, t2, j2, st) = tc (ctx, st) e2
          val (x, t, len) = get_vector $ whnf itctx t1
          val () = is_eq_ty itctx (t2, t)
          val (e1, e2) = if !anno_EVectorPushBack then (e1 %: t1, e2 %: t2) else (e1, e2)
          val (e1, e2) = if !anno_EVectorPushBack_state then (e1 %~ st_e1, e2 %~ st) else (e1, e2)
        in
          (EBinOp (opr, e1, e2), TUnit, j1 %%+ j2 %%+ TN C_EVectorPushBack, st @%+ (x, len %+ N1))
        end
      | EUnOp (opr as EUTiML (EUVectorLen ()), e) =>
        let
          val (e, t, j, st) = tc (ctx, st) e
          val (_, _, len) = get_vector $ whnf itctx t
          val e = if !anno_EVectorLen then e %: t else e
          val e = if !anno_EVectorLen_state then e %~ st else e
        in
          (EUnOp (opr, e), TNat len, j %%+ TN C_EVectorLen, st)
        end
      | EUnOp (opr as EUTiML (EUVectorClear ()), e) =>
        let
          val (e, t, j, st) = tc (ctx, st) e
          val (x, _, _) = get_vector $ whnf itctx t
          val e = if !anno_EVectorClear then e %: t else e
          val e = if !anno_EVectorClear_state then e %~ st else e
        in
          (EUnOp (opr, e), TUnit, j %%+ TN C_EVectorClear, st @%+ (x, N0))
        end
      | ETriOp (opr as ETVectorSet (), e1, e2, e3) =>
        let
          val (e1, t1, j1, st) = tc (ctx, st) e1
          val st_e1 = st
          val (e2, t2, j2, st) = tc (ctx, st) e2
          val st_e2 = st
          val i = assert_TNat_m t2 (fn s => raise MTCError $ "EVectorSet: " ^ s)
          val (e3, t3, j3, st) = tc (ctx, st) e3
          val t1 = whnf itctx t1
          val (x, t, len) = get_vector t1
          val () = is_eq_ty itctx (t3, t)
          val () = check_prop (i %< len)
          val (e1, e2, e3) = if !anno_EVectorSet then (e1 %: t1, e2 %: t2, e3 %: t) else (e1, e2, e3)
          val (e1, e2, e3) = if !anno_EVectorSet_state then (e1 %~ st_e1, e2 %~ st_e2, e3 %~ st) else (e1, e2, e3)
        in
          (ETriOp (opr, e1, e2, e3), TUnit, j1 %%+ j2 %%+ j3 %%+ TN C_EVectorSet, st)
        end
      | EBinOp (opr as EBStorageSet (), e1, e2) =>
        let
          val (e1, t1, j1, st) = tc (ctx, st) e1
          val st_e1 = st
          val t1 = whnf itctx t1
          val t = assert_TCell t1
          val (e2, j2, st) = tc_against_ty (ctx, st) (e2, t)
          val (e1, e2) = if !anno_EStorageSet then (e1 %: t1, e2 %: t) else (e1, e2)
          val (e1, e2) = if !anno_EStorageSet_state then (e1 %~ st_e1, e2 %~ st) else (e1, e2)
        in
          (EBinOp (opr, e1, e2), TUnit, j1 %%+ j2 %%+ TN C_EStorageSet, st)
        end
      | EState x => (EState x, TState x, TN C_EState, st)
      | EBinOp (EBNat opr, e1, e2) =>
        let
          val (e1, t1, j1, st) = tc (ctx, st) e1
          val st_e1 = st
          val t1 = whnf itctx t1
          val i1 = case t1 of
                       TNat i => i
                     | _ => raise MTCError "ENatAdd 1"
          val (e2, t2, j2, st) = tc (ctx, st) e2
          val t2 = whnf itctx t2
          val i2 = case t2 of
                       TNat i => i
                     | _ => raise MTCError "ENatAdd 2"
          val i2 = Simp.simp_i $ update_i i2
          val () = if opr = EBNBoundedMinus () then check_prop (i2 %<= i1) else ()
          val (e1, e2) = if !anno_ENat then (e1 %: t1, e2 %: t2) else (e1, e2)
          val (e1, e2) = if !anno_ENat_state then (e1 %~ st_e1, e2 %~ st) else (e1, e2)
          val t = TNat $ interp_nat_expr_bin_op opr (i1, i2) (fn () => raise Impossible "Can only divide by a nat whose index is a constant")
        in
          (EBinOp (EBNat opr, e1, e2), t, j1 %%+ j2 %%+ TN (C_ENat opr), st)
        end
      | EBinOp (EBNatCmp opr, e1, e2) =>
        let
          val (e1, t1, j1, st) = tc (ctx, st) e1
          val st_e1 = st
          val t1 = whnf itctx t1
          val i1 = case t1 of
                       TNat i => i
                     | _ => raise MTCError "ENatAdd 1"
          val (e2, t2, j2, st) = tc (ctx, st) e2
          val t2 = whnf itctx t2
          val i2 = case t2 of
                       TNat i => i
                     | _ => raise MTCError "ENatAdd 2"
          val (e1, e2) = if !anno_ENatCmp then (e1 %: t1, e2 %: t2) else (e1, e2)
          val (e1, e2) = if !anno_ENatCmp_state then (e1 %~ st_e1, e2 %~ st) else (e1, e2)
          val t = TiBool $ interp_nat_cmp dummy opr (i1, i2)
        in
          (EBinOp (EBNatCmp opr, e1, e2), t, j1 %%+ j2 %%+ TN (C_ENatCmp opr), st)
        end
      | ETriOp (ETWrite (), e1, e2, e3) =>
        let
          val (e1, t1, j1, st) = tc (ctx, st) e1
          val st_e1 = st
          val t1 = whnf itctx t1
          val (t, i1) = case t1 of
                            TArr data => data
                          | _ => raise MTCError "EWrite 1"
          val (e2, t2, j2, st) = tc (ctx, st) e2
          val st_e2 = st
          val t2 = whnf itctx t2
          val i2 = case t2 of
                       TNat i => i
                     | _ => raise MTCError "EWrite 2"
          val () = check_prop (i2 %< i1)
          val (e3, j3, st) = tc_against_ty (ctx, st) (e3, t)
          val (e1, e2, e3) = if !anno_EWrite then (e1 %: t1, e2 %: t2, e3 %: t) else (e1, e2, e3)
          val (e1, e2, e3) = if !anno_EWrite_state then (e1 %~ st_e1, e2 %~ st_e2, e3 %~ st) else (e1, e2, e3)
        in
          (EWrite (e1, e2, e3), TUnit, j1 %%+ j2 %%+ j3 %%+ TN C_EWrite, st)
        end
      | EIfi data =>
        let
          val (e, (name1, e1), (name2, e2)) = unECase data
          val (e, t_e, j, st) = tc (ctx, st) e
          val i = assert_TiBool $ whnf itctx t_e
          val make_exists = make_exists "__p"
          val t1 = make_exists (SSubset_from_prop dummy $ i %= Itrue)
          val t2 = make_exists (SSubset_from_prop dummy $ i %= Ifalse)
          val (e1, t1, i1, st1) = tc (add_typing_full (fst name1, t1) ctx, st) e1
          val (e2, t2, i2, st2) = tc (add_typing_full (fst name2, t2) ctx, st) e2
          val e2 = if !anno_EIfi_e2_time then e2 |># i2 else e2
          val () = is_eq_ty itctx (t1, t2)
          val () = is_eq_idx (st2, st1)
          val e = if !anno_EIfi then e %: t_e else e
          val e = if !anno_EIfi_state then e %~ st else e
        in
          (EIfi (e, EBind (name1, e1), EBind (name2, e2)), t1, j %%+ TN C_Ifi %%+ IMaxPair (i1, i2), st1)
        end
      | EPack (t', t1, e) =>
        let
          val t' = kc_against_kind itctx (t', KType ())
          val t' = whnf itctx t'
          val (_, k, t) = assert_TExists t'
          val t1 = kc_against_kind itctx (t1, k)
          val t_e = subst0_t_t t1 t
          val (e, i, st) = tc_against_ty (ctx, st) (e, t_e)
          val e = if !anno_EPack then e %: t_e else e
          val e = if !anno_EPack_state then e %~ st else e
        in
          (EPack (t', t1, e), t', i %%+ TN C_EPack, st)
        end
      | EPackI (t', i, e) =>
        let
          val t' = kc_against_kind itctx (t', KType ())
          val t' = whnf itctx t'
          val (_, s, t) = assert_TExistsI t'
          val i = sc_against_sort ictx (i, s)
          val t_e = subst0_i_t i t
          val (e, j, st) = tc_against_ty (ctx, st) (e, t_e)
          val e = if !anno_EPackI then e %: t_e else e
          val e = if !anno_EPackI_state then e %~ st else e
        in
          (EPackI (t', i, e), t', j %%+ TN C_EPack, st)
        end
      | EUnpack data =>
        let
          val (e1, (tname, ename, e2)) = unEUnpack data
          val (e1, t_e1, i1, st) = tc (ctx, st) e1
          val st_e1 = st
          val t_e1 = whnf itctx t_e1
          val (_, k, t) = assert_TExists t_e1
          val (e2, t2, i2, st) = tc (add_typing_full (fst ename, t) $ add_kinding_full (fst tname, k) ctx, st) e2
          (* val () = println $ "trying to forget: " ^ (ExportPP.pp_t_to_string $ ExportPP.export_t (itctx_names $ add_kinding_it (tname, k) itctx) t2) *)
          val t2 = forget01_t_t t2
          (* val () = println "forget finished" *)
          val e1 = if !anno_EUnpack then e1 %: t_e1 else e1
          val e1 = if !anno_EUnpack_state then e1 %~ st_e1 else e1
        in
          (MakeEUnpack (e1, tname, ename, e2), t2, i1 %%+ TN C_EUnpack %%+ i2, st)
        end
      | EUnpackI data =>
        let
          val (e1, (iname, ename, e2)) = unEUnpack data
          val (e1, t_e1, i1, st) = tc (ctx, st) e1
          val st_e1 = st
          fun mismatch header got expect =
            sprintf "Mismatch when checking %:\n  got:    $\n  expect: $\n" [header, got, expect]
          val t_e1 = whnf itctx t_e1
          val (_, s, t) = assert_TExistsI t_e1
          val (e2, t2, i2, st) = open_close add_sorting_full (fst iname, s) ctx (fn ctx => tc (add_typing_full (fst ename, t) ctx, shift_i_i st) e2)
          val t2 = forget01_i_t t2
                   handle ForgetError (r, m) => raise ForgetError (r, m ^ " when forgetting type: " ^ (ExportPP.pp_t_to_string NONE $ ExportPP.export_t NONE (itctx_names $ add_sorting_it (fst iname, s) itctx) t2))
          fun forget_i name i =
            forget01_i_i i
            handle ForgetError (r, m) => raise ForgetError (r, m ^ sprintf " when forgetting $: $" [name, ToString.SN.strn_i $ ExportPP.export_i (fst iname :: map fst ictx) i])
          val i2 = mapPair (forget_i "time", forget_i "space") i2
          val st = forget_i "state" st
          val e1 = if !anno_EUnpackI then e1 %: t_e1 else e1
          val e1 = if !anno_EUnpackI_state then e1 %~ st_e1 else e1
        in
          (MakeEUnpackI (e1, iname, ename, e2), t2, i1 %%+ TN C_EUnpack %%+ i2, st)
        end
      | EPackIs (t, is, e) =>
        let
          val t = kc_against_kind itctx (t, KType ())
        in
          case is of
              [] =>
              let
                val (e, i, st) = tc_against_ty (ctx, st) (e, t)
              in
                (e, t, i, st)
              end
            | i :: is =>
              let
                val (_, _, t') = assert_TExistsI $ whnf itctx t
              in
                tc (ctx, st) $ EPackI (t, i, EPackIs (subst0_i_t i t', is, e))
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
                val (e1, t1, (i1, j1), st) = tc (ctx, st) e1
                val st_e1 = st
                val e2 = EAscTypes (e2, ts)
                val e2 = EAscTime (e2, IBinOp (IBMinus (), i, i1))
                val (e2, t2, (_, j2), st) = tc (add_typing_full (fst name, t1) ctx, st) e2
                val e1 = if !anno_ELet then e1 %: t1 else e1
                val e1 = if !anno_ELet_state then e1 %~ st_e1 else e1
                val e = MakeELet (e1, name, e2)
              in
                (e |> i, t2, (i, j1 %+ j2), st)
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
                val (e, t, (i1, j), st) = tc (ctx, st) e
                fun check_le_with_subtractions ictx (i, i') =
                  let
                    val collect_MinusI_left = collect_IBinOp_left (IBMinus ())
                    val (i', is) = assert_cons $ collect_MinusI_left i'
                    val i = combine_IBAdd_nonempty (i, is)
                    val () = check_prop (i %<= i')
                  in
                    ()
                  end
                val () = check_le_with_subtractions ictx (i1, i)
              in
                (e |> i, t, (i, j), st)
              end
        end
      | EAscSpace (e, i) =>
        let
          val i = sc_against_sort ictx (i, SNat)
          val (e, t, (j, i'), st) = tc (ctx, st) e
          val () = check_prop (i' %<= i)
        in
          (e |# i, t, (j, i), st)
        end
      | EAscType (e, t) =>
        let
          val t = kc_against_kind itctx (t, KType ())
          val (e, i, st) = tc_against_ty (ctx, st) (e, t)
        in
          (e %: t, t, i, st)
        end
      | EAscState (e, st') =>
        let
          val (e, t, i, st) = tc (ctx, st) e
          val st' = sc_against_sort ictx (st', SState)
          val () = is_eq_idx (st, st')
        in
          (EAscState (e, st'), t, i, st')
        end
      | EUnOp (EUTiML (EUAnno a), e) =>
        let
          val (e, t, i, st) = tc (ctx, st) e
        in
          (EUnOp (EUTiML (EUAnno a), e), t, i, st)
        end
      | ENever t =>
        let
          val t = kc_against_kind itctx (t, KType ())
          val () = check_prop (PFalse dummy)
        in
          (ENever t, t, TN C_ENever, st)
        end
      | EBuiltin (name, t) =>
        let
          val t = kc_against_kind itctx (t, KType ())
        in
          (EBuiltin (name, t), t, TN C_EBuiltin, st)
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
          fun foo ((name, e), (decls, ctx, st)) =
              let
                val (e, t, i, st) = tc (ctx, st) e
                val e = if !anno_ELet then e %: t else e
                val e = if !anno_ELet_state then e %~ st else e
                val decl = ((name, e), i)
                val decls = decl :: decls
                val ctx = add_typing_full (fst name, t) ctx
              in
                (decls, ctx, st)
              end
          val (decls, ctx, st) = foldl foo ([], ctx, st) decls
          val decls = rev decls
          val (decls, is) = unzip decls 
          val (e, t, i, st) = tc (ctx, st) e
          val e = ELets (decls, e)
          val is = combine_IBAdd_Time_Nat is
        in
          (e, t, is %%+ i, st)
        end
      | ELetType data =>
        let
          val (t, (name, e)) = unELetType data
          val _ = kc itctx t
        in
          tc (ctx, st) $ subst0_t_e t e (* todo: record type aliasing in ctx *)
        end
      | ELetIdx data =>
        let
          val (i, (name, e)) = unELetIdx data
          val (i, _) = sc ictx i
        in
          tc (ctx, st) $ subst0_i_e i e (* todo: record index aliasing in ctx *)
        end
      | ELetConstr data =>
        let
          val (e1, (name, e2)) = unELetConstr data
          val e = subst0_c_e e1 e2
          val e = eval_constr e
        in
          tc (ctx, st) e
        end
      | EMallocPair (a, b) =>
        let
          val () = assert_b "EMallocPair: is_value a" (is_value a)
          val () = assert_b "EMallocPair: is_value b" (is_value b)
          val (a, t1, i1, st) = tc (ctx, st) a
          val (b, t2, i2, st) = tc (ctx, st) b
          val e = EMallocPair (a, b)
          val t = TProdEx ((t1, false), (t2, false))
        in
          (e, t, i1 %%+ i2, st)
        end
      | EPairAssign (e1, proj, e2) =>
        let
          val (e1, t_e1, i_e1, st) = tc (ctx, st) e1
          val ((t1, b1), (t2, b2)) =
              case t_e1 of
                  TProdEx a => a
                | _ => raise MTCError "EPairAssign/assert-TProdEx"
          val t_e2 = choose (t1, t2) proj
          val (e2, i_e2, st) = tc_against_ty (ctx, st) (e2, t_e2)
          val (b1, b2) = choose_update (b1, b2) proj
          val e = EPairAssign (e1, proj, e2)
          val t = TProdEx ((t1, b1), (t2, b2))
        in
          (e, t, i_e1 %%+ i_e2, st)
        end
      | EProjProtected (proj, e) =>
        let
          val (e, t_e, i_e, st) = tc (ctx, st) e
          val ts =
              case t_e of
                  TProdEx a => a
                | _ => raise MTCError "EProjProtected/assert-TProdEx"
          val (t, b) = choose ts proj
          val () = if b then ()
                   else raise MTCError "EProjProtected/check-permission"
          val e = EProjProtected (proj, e)
        in
          (e, t, i_e, st)
        end
      | EHalt (e, t) =>
        let
          val t = kc_against_kind itctx (t, KType ())
          val (e, t_e, i_e, st) = tc (ctx, st) e
          val e = if !anno_EHalt then e %: t_e else e
          val e = if !anno_EHalt_state then e %~ st else e
        in
          (EHalt (e, t), t, i_e %%+ TN C_EHalt, st)
        end
      | EAbsConstr _ => err ()
      | EAppConstr _ => err ()
      | EVarConstr _ => err ()
      | EMatchSum _ => err ()
      | EMatchPair _ => err ()
      | EMatchUnfold _ => err ()
    fun extra_msg () = "\nwhen typechecking\n" ^ ((* substr 0 300 $  *)ExportPP.pp_e_to_string (NONE, NONE) $ ExportPP.export (NONE, SOME 5) (ctx_names ctx) e_input)
    val (e_output, t, i, st) = main ()
                 handle ForgetError (r, m) => raise MTCError ("Forgetting error: " ^ m ^ extra_msg ())
                      | MSCError (r, m) => raise MTCError ("Sortcheck error:\n" ^ join_lines m ^ extra_msg ())
                      | MUnifyError (r, m) => raise MTCError ("Unification error:\n" ^ join_lines m ^ extra_msg ())
                      | MTCError m => raise MTCError (m ^ extra_msg ())
                      | Impossible m => raise Impossible (m ^ extra_msg ())
    val () = println "tc() finished:"
    val () = print $ e_input_str
    val () = println "of type:"
    val () = println $ ExportPP.pp_t_to_string NONE $ ExportPP.export_t NONE (itctx_names (ictx, tctx)) $ MicroTiMLSimp.simp_t t
    val () = println "of time:"
    val () = println $ (* substr 0 100 $  *)ExportPP.str_i $ ExportPP.export_i (ictx_names ictx) $ simp_i $ fst i
  in
    (e_output, t, i, st)
  end

and tc_against_ty st_types (ctx as (ictx, tctx, _), st) (e, t) =
    let
      (* val () = print "tc_against_ty() start:\n" *)
      (* val e_str = substr 0 100 $ ExportPP.pp_e_to_string $ ExportPP.export (ctx_names ctx) e *)
      (* val t_str = ExportPP.pp_t_to_string NONE $ ExportPP.export_t NONE (itctx_names (ictx, tctx)) t *)
      (* val () = println $ sprintf "  $\n  $\n" [ *)
      (*       e_str, *)
      (*       t_str *)
      (*     ] *)
      val (e, t', i, st) = tc st_types (ctx, st) e
      (* val () = print "tc_against_ty() to compare types:\n" *)
      (* val () = println $ sprintf "  $\n  $\n" [ *)
      (*       ExportPP.pp_t_to_string NONE $ ExportPP.export_t NONE (itctx_names (ictx, tctx)) t', *)
      (*       t_str *)
      (*     ] *)
      val () = is_eq_ty (ictx, tctx) (t', t)
      (* val () = println "tc_against_ty() finished:" *)
      (* val () = println e_str *)
    in
      (e, i, st)
    end
    
and tc_against_time st_types (ctx as (ictx, tctx, _), st) (e, i) =
    let
      (* val () = print "tc_against_time() start:\n" *)
      (* val e_str = substr 0 100 $ ExportPP.pp_e_to_string $ ExportPP.export (ctx_names ctx) e *)
      (* val () = println e_str *)
      val (e, t, (i', j), st) = tc st_types (ctx, st) e
      (* val () = println "before tc_against_time()/check_prop()" *)
      val () = check_prop (i' %<= i)
      (* val () = println "tc_against_time() finished:" *)
      (* val () = println e_str *)
    in
      (e, t, j, st)
    end
    
and tc_against_time_space st_types (ctx as (ictx, tctx, _), st) (e, (i, j)) =
    let
      val (e, t, j', st) = tc_against_time st_types (ctx, st) (e, i)
      val () = check_prop (j' %<= j)
    in
      (e, t, st)
    end
    
and tc_against_ty_time st_types (ctx as (ictx, tctx, _), st) (e, t, i) =
    let
      val (e, (i', j), st) = tc_against_ty st_types (ctx, st) (e, t)
      val () = check_prop (i' %<= i)
    in
      (e, j, st)
    end

and tc_against_ty_time_space st_types (ctx as (ictx, tctx, _), st) (e, t, (i, j)) =
    let
      val (e, j', st) = tc_against_ty_time st_types (ctx, st) (e, t, i)
      val () = check_prop (j' %<= j)
    in
      (e, st)
    end

(* fun sort_to_hyps (name, s) = *)
(*   case s of *)
(*       SBasic (b, r) => [VarH (name, b)] *)
(*     | SSubset ((b, _), Bind.Bind (_, p), _) => [PropH p, VarH (name, b)] *)
(*     | _ => raise Impossible "sort_to_hyps" *)
      
(* fun to_vc (ctx, p) = (concatMap sort_to_hyps ctx, p) *)
  
(* fun runWriter m () = *)
(*   let  *)
(*     (* val () = vcs := [] *) *)
(*     (* val () = admits := [] *) *)
(*     val r = m () *)
(*     val vcs = [] *)
(*     val admits = [] *)
(*     (* val vcs = !vcs *) *)
(*     (* val admits = !admits *) *)
(*     (* val vcs = map to_vc vcs *) *)
(*     (* (* val () = println "after to_vc; calling simp_vc_vcs" *) *) *)
(*     (* (* val () = app println $ concatMap (fn ls => ls @ [""]) $ map (str_vc false "") vcs *) *) *)
(*     (* val vcs_len = length vcs *) *)
(*     (* (* val () = println $ "#VCs: " ^ str_int vcs_len *) *) *)
(*     (* (* val vcs = concatMapi (fn (i, vc) => (println (sprintf "vc $ @ $" [str_int vcs_len, str_int i]); simp_vc_vcs vc)) vcs *) *) *)
(*     (* (* val () = println "before simp vcs" *) *) *)
(*     (* (* val vcs = map VC.simp_vc vcs *) *) *)
(*     (* (* val () = println "after simp vcs" *) *) *)
(*     (* (* val vcs = TrivialSolver.simp_and_solve_vcs vcs *) *) *)
(*     (* val admits = map to_vc admits *) *)
(*   in  *)
(*     (r, vcs, admits)  *)
(*   end *)
    
datatype tc_flag =
         Allow_substate_call
       | Anno_EVar
       | Anno_EProj
       | Anno_EFold
       | Anno_EUnfold
       | Anno_EApp
       | Anno_EPair
       | Anno_EInj
       | Anno_EBPrim
       | Anno_ENew
       | Anno_ERead
       | Anno_ENat
       | Anno_ENatCmp
       | Anno_EWrite
       | Anno_ECase
       | Anno_EAbs
       | Anno_EAppT
       | Anno_EAppI
       | Anno_EPack
       | Anno_EPackI
       | Anno_EUnpack
       | Anno_EUnpackI
       | Anno_ELet
       | Anno_EHalt
       | Anno_ECase_e2_time
       | Anno_EIte_e2_time
       | Anno_EIfi_e2_time
       | Anno_EIfi
       | Anno_EVectorSet
       | Anno_EMapPtr
       | Anno_EVectorGet
       | Anno_EVectorPushBack
       | Anno_EStorageSet
       | Anno_EUPrim
       | Anno_EArrayLen
       | Anno_ENat2Int
       | Anno_EStorageGet
       | Anno_EProj_state
       | Anno_EPrintc_state
       | Anno_EUPrim_state
       | Anno_EArrayLen_state
       | Anno_ENat2Int_state
       | Anno_EInt2Nat_state
       | Anno_EStorageGet_state
       | Anno_EInj_state
       | Anno_EFold_state
       | Anno_EUnfold_state
       | Anno_EApp_state
       | Anno_EPair_state
       | Anno_EBPrim_state
       | Anno_ENew_state
       | Anno_ERead_state
       | Anno_EMapPtr_state
       | Anno_EVectorGet_state
       | Anno_EVectorPushBack_state
       | Anno_EVectorSet_state
       | Anno_EStorageSet_state
       | Anno_ENat_state
       | Anno_ENatCmp_state
       | Anno_EWrite_state
       | Anno_ECase_state
       | Anno_EIte_state
       | Anno_EIfi_state
       | Anno_EAppT_state
       | Anno_EAppI_state
       | Anno_EPack_state
       | Anno_EPackI_state
       | Anno_EUnpack_state
       | Anno_EUnpackI_state
       | Anno_ELet_state
       | Anno_ENewArrayValues_state
       | Anno_EHalt_state
       | Anno_EAbs_state
       | Anno_EVectorLen
       | Anno_EVectorClear
       | Anno_EVectorLen_state
       | Anno_EVectorClear_state

fun typecheck (flags, st_types) ctx e =
  let
    val mem = fn (a : tc_flag) => mem op= a
    val () = allow_substate_call := mem Allow_substate_call flags
    val () = anno_EVar := mem Anno_EVar flags
    val () = anno_EProj := mem Anno_EProj flags
    val () = anno_EFold := mem Anno_EFold flags
    val () = anno_EUnfold := mem Anno_EUnfold flags
    val () = anno_EApp := mem Anno_EApp flags
    val () = anno_EPair := mem Anno_EPair flags
    val () = anno_EInj := mem Anno_EInj flags
    val () = anno_EBPrim := mem Anno_EBPrim flags
    val () = anno_ENew := mem Anno_ENew flags
    val () = anno_ERead := mem Anno_ERead flags
    val () = anno_ENat := mem Anno_ENat flags
    val () = anno_ENatCmp := mem Anno_ENatCmp flags
    val () = anno_EWrite := mem Anno_EWrite flags
    val () = anno_ECase := mem Anno_ECase flags
    val () = anno_EAbs := mem Anno_EAbs flags
    val () = anno_EAppT := mem Anno_EAppT flags
    val () = anno_EAppI := mem Anno_EAppI flags
    val () = anno_EPack := mem Anno_EPack flags
    val () = anno_EPackI := mem Anno_EPackI flags
    val () = anno_EUnpack := mem Anno_EUnpack flags
    val () = anno_EUnpackI := mem Anno_EUnpackI flags
    val () = anno_ELet := mem Anno_ELet flags
    val () = anno_EHalt := mem Anno_EHalt flags
    val () = anno_ECase_e2_time := mem Anno_ECase_e2_time flags
    val () = anno_EIte_e2_time := mem Anno_EIte_e2_time flags
    val () = anno_EIfi_e2_time := mem Anno_EIfi_e2_time flags
    val () = anno_EIfi := mem Anno_EIfi flags
    val () = anno_EVectorSet := mem Anno_EVectorSet flags
    val () = anno_EMapPtr := mem Anno_EMapPtr flags
    val () = anno_EVectorGet := mem Anno_EVectorGet flags
    val () = anno_EVectorPushBack := mem Anno_EVectorPushBack flags
    val () = anno_EStorageSet := mem Anno_EStorageSet flags
    val () = anno_EUPrim := mem Anno_EUPrim flags
    val () = anno_EArrayLen := mem Anno_EArrayLen flags
    val () = anno_ENat2Int := mem Anno_ENat2Int flags
    val () = anno_EStorageGet := mem Anno_EStorageGet flags
    val () = anno_EProj_state := mem Anno_EProj_state flags
    val () = anno_EPrintc_state := mem Anno_EPrintc_state flags
    val () = anno_EUPrim_state := mem Anno_EUPrim_state flags
    val () = anno_EArrayLen_state := mem Anno_EArrayLen_state flags
    val () = anno_ENat2Int_state := mem Anno_ENat2Int_state flags
    val () = anno_EInt2Nat_state := mem Anno_EInt2Nat_state flags
    val () = anno_EStorageGet_state := mem Anno_EStorageGet_state flags
    val () = anno_EInj_state := mem Anno_EInj_state flags
    val () = anno_EFold_state := mem Anno_EFold_state flags
    val () = anno_EUnfold_state := mem Anno_EUnfold_state flags
    val () = anno_EApp_state := mem Anno_EApp_state flags
    val () = anno_EPair_state := mem Anno_EPair_state flags
    val () = anno_EBPrim_state := mem Anno_EBPrim_state flags
    val () = anno_ENew_state := mem Anno_ENew_state flags
    val () = anno_ERead_state := mem Anno_ERead_state flags
    val () = anno_EMapPtr_state := mem Anno_EMapPtr_state flags
    val () = anno_EVectorGet_state := mem Anno_EVectorGet_state flags
    val () = anno_EVectorPushBack_state := mem Anno_EVectorPushBack_state flags
    val () = anno_EVectorSet_state := mem Anno_EVectorSet_state flags
    val () = anno_EStorageSet_state := mem Anno_EStorageSet_state flags
    val () = anno_ENat_state := mem Anno_ENat_state flags
    val () = anno_ENatCmp_state := mem Anno_ENatCmp_state flags
    val () = anno_EWrite_state := mem Anno_EWrite_state flags
    val () = anno_ECase_state := mem Anno_ECase_state flags
    val () = anno_EIte_state := mem Anno_EIte_state flags
    val () = anno_EIfi_state := mem Anno_EIfi_state flags
    val () = anno_EAppT_state := mem Anno_EAppT_state flags
    val () = anno_EAppI_state := mem Anno_EAppI_state flags
    val () = anno_EPack_state := mem Anno_EPack_state flags
    val () = anno_EPackI_state := mem Anno_EPackI_state flags
    val () = anno_EUnpack_state := mem Anno_EUnpack_state flags
    val () = anno_EUnpackI_state := mem Anno_EUnpackI_state flags
    val () = anno_ELet_state := mem Anno_ELet_state flags
    val () = anno_ENewArrayValues_state := mem Anno_ENewArrayValues_state flags
    val () = anno_EHalt_state := mem Anno_EHalt_state flags
    val () = anno_EAbs_state := mem Anno_EAbs_state flags
val () = anno_EVectorLen := mem Anno_EVectorLen flags
val () = anno_EVectorClear := mem Anno_EVectorClear flags
val () = anno_EVectorLen_state := mem Anno_EVectorLen_state flags
val () = anno_EVectorClear_state := mem Anno_EVectorClear_state flags
    val ret = runWriter (fn () => tc st_types ctx e) ()
  in
    ret
  end

structure UnitTest = struct

structure TestUtil = struct

open LongId
open Util
open MicroTiML
open MicroTiMLVisitor
open MicroTiMLLongId
open MicroTiML
       
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
    (* val () = println $ str_e empty ToStringUtil.empty_ctx e *)
    (* val () = println "" *)
    val () = println "Started translating ..."
    val e = trans_e e
    val st_types = StMap.map (mapSnd trans_mt) st_types
    val () = println "Finished translating"
    open ExportPP
    val () = pp_e (NONE, NONE) $ export (NONE, NONE) ToStringUtil.empty_ctx e
    val () = println ""
    open TestUtil
    open ExportPP
    val () = println "Started MicroTiML typechecking ..."
    val ((_, t, i, st), (vcs, admits)) = typecheck ([], st_types) (([], [], []), IEmptyState) e
    val () = println "Finished MicroTiML typechecking"
    val () = println "Type:"
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
    val () = println $ "#VCs: " ^ str_int (length vcs)
    (* val () = println "VCs:" *)
    (* val () = app println $ concatMap (fn ls => ls @ [""]) $ map (str_vc false "") vcs *)
    val () = pp_e (NONE, NONE) $ export (NONE, NONE) ToStringUtil.empty_ctx e
    val () = println ""
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
