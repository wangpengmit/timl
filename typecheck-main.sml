structure TypeCheckMain = struct
structure U = UnderscoredExpr
open CollectUVar
open CostUtil
open MicroTiMLCosts
open RedundantExhaust
open Region
open Pervasive
open Expr
open Simp
open UVarExprUtil
open Subst
open Bind
open Package
open TypecheckUtil
open ToStringRaw
open UVar
structure Unify = UnifyFn (struct exception UnifyError = TypecheckUtil.Error end)
open Unify
open FreshUVar
open UVarForget
open Util
structure US = UnderscoredToString
structure UShift = UnderscoredExprShift
                 
infixr 0 $
infix 0 !!

infix 9 %@
infix 8 %^
infix 7 %*
infix 6 %+ 
infix 4 %<
infix 4 %>
infix 4 %<=
infix 4 %>=
infix 4 %=
infix 4 <?
infix 4 >?
infix 4 <=?
infix 4 >=?
infix 4 =?
infix 4 <>?
infixr 3 /\
infixr 3 /\?
infixr 2 \/
infixr 2 \/?
infixr 1 -->
infix 1 <->

infix 0 %:
infix 0 |>#
        
infix  9 @!
fun m @! k = StMap.find (m, k)
infix  6 @+
fun m @+ a = StMap.insert' (a, m)
                           
infix  9 @!!
fun m @!! k = StMapU.must_find m k
infix 6 @--
fun m @-- m' = StMapU.sub m m'
infix 6 @++
fun m @++ m' = StMapU.union m m'

val is_builtin_enabled = ref false
fun turn_on_builtin () = (is_builtin_enabled := true)
fun turn_off_builtin () = (is_builtin_enabled := false)
                            
fun str_sctx gctx sctx =
  snd $ foldr (fn ((name, sort), (sctxn, acc)) => (name :: sctxn, (name, str_s gctx sctxn sort) :: acc)) ([], []) sctx

fun get_basic_sort_IUVar gctx ctx ((), r) =
  let
    val bs = fresh_basic_sort ()
  in
    (fresh_i gctx ctx bs r, bs)
  end

fun match_BSArrow gctx ctx r bs =
  let
    val bs1 = fresh_basic_sort ()
    val bs2 = fresh_basic_sort ()
    val () = unify_bs r (bs, BSArrow (bs1, bs2))
  in
    (bs1, bs2)
  end

fun get_sort_type_SUVar gctx ctx ((), r) =
  fresh_sort gctx ctx r
              
structure Sortcheck = SortcheckFn (structure U = U
                                   structure T = Expr
                                   type sigcontext = sigcontext
                                   (* val str_v = str_v *)
                                   val str_bs = str_bs
                                   val str_i = str_i
                                   val str_s = str_s
                                   val U_str_i = US.str_i
                                   val fetch_sort = fetch_sort
                                   val is_wf_basic_sort_BSUVar = fresh_basic_sort
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
                                   exception Error = Error
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
       
fun check_sorts gctx (ctx, is : U.idx list, sorts, r) : idx list =
  (check_length r (is, sorts);
   ListPair.map (fn (i, s) => check_sort gctx (ctx, i, s)) (is, sorts))
    
fun check_Time_Nat gctx ctx (i, j) =
  (check_basic_sort gctx (ctx, i, BSTime), check_basic_sort gctx (ctx, j, BSNat))

fun add_ref a = binop_ref (curry $ swap StMap.insert') a
val st_types_ref = (ref StMap.empty, ref StMap.empty)
val st_ref = ref StMap.empty
fun add_state (x, t) =
  (add_ref (#1 st_types_ref) (x, t);
   add_ref (#2 st_types_ref) (x, StMap.numItems $ !(#2 st_types_ref));
   add_ref st_ref (x, N0 dummy))
fun clear_st_types () =
  (#1 st_types_ref := StMap.empty;
   #2 st_types_ref := StMap.empty)
fun get_st_types () =
  let
    val name2ty = !(#1 st_types_ref)
    val name2int = !(#2 st_types_ref)
  in
    (name2ty, name2int)
  end
    
val str_st_key = id
                   
fun is_good_st_key r k =
    case !(#1 st_types_ref) @! k of
        SOME _ => ()
      | _ => raise Error (r, ["unkown state field " ^ str_st_key k])
                   
fun is_wf_state gctx ctx m = StMap.mapi (fn (k, i) => let val r = U.get_region_i i in (is_good_st_key r k; check_sort gctx (ctx, i, SNat r)) end) m

fun is_wf_kind (k : U.kind) = mapSnd (map is_wf_basic_sort) k

(* k => Type *)
fun recur_kind k = (0, k)

(* higher-kind *)
datatype hkind =
         HKType
         | HKArrow of hkind * hkind
         | HKArrowI of basic_sort * hkind

fun str_hk k =
  case k of
      HKType => "*"
    | HKArrow (k1, k2) => sprintf "($ => $)" [str_hk k1, str_hk k2]
    | HKArrowI (s, k) => sprintf "($ => $)" [str_bs s, str_hk k]

val HType = HKType

fun kind_to_higher_kind (n, sorts) =
  let
    val k = foldr (fn (s, k) => HKArrowI (s, k)) HKType sorts
    val k = Range.for (fn (_, k) => HKArrow (HKType, k)) k (Range.zero_to n)
  in
    k
  end

fun unify_higher_kind r (k, k') =
  case (k, k') of
      (HKType, HKType) => ()
    | (HKArrow (k1, k2), HKArrow (k1', k2')) =>
      let
        val () = unify_higher_kind r (k1, k1')
        val () = unify_higher_kind r (k2, k2')
      in
        ()
      end
    | (HKArrowI (s, k), HKArrowI (s', k')) =>
      let
        val () = unify_bs r (s, s')
        val () = unify_higher_kind r (k, k')
      in
        ()
      end
    | _  => raise Error (r, [kind_mismatch (str_hk k) str_hk k'])

fun get_higher_kind gctx (ctx as (sctx : scontext, kctx : kcontext), c : U.mtype) : mtype * hkind = 
  let
    val get_higher_kind = get_higher_kind gctx
    val check_higher_kind = check_higher_kind gctx
    val check_higher_kind_Type = check_higher_kind_Type gctx
    val gctxn = gctx_names gctx
    val ctxn as (sctxn, kctxn) = (sctx_names sctx, names kctx)
    fun error (r, thing, expected, str_got, got) =
      raise Error (r, kind_mismatch_in_type expected str_got got thing)
    fun check_same_domain st st' =
      if StMapU.is_same_domain st st' then ()
      else raise Error (U.get_region_mt c, ["pre- and post-condition must have the same state fields"])
    (* val () = print (sprintf "Kinding $\n" [U.str_mt gctxn ctxn c]) *)
    fun main () =
      case c of
	  U.TArrow ((st1, c1), i, (st2, c2)) =>
          (check_same_domain st1 st2;
	   (TArrow ((is_wf_state gctx sctx st1, check_higher_kind_Type (ctx, c1)), 
	            check_Time_Nat gctx sctx i,
	            (is_wf_state gctx sctx st2, check_higher_kind_Type (ctx, c2))),
            HType))
        | U.TArray (t, i) =>
	  (TArray (check_higher_kind_Type (ctx, t),
	            check_basic_sort gctx (sctx, i, BSNat)),
           HType)
        | U.TNat (i, r) =>
	  (TNat (check_basic_sort gctx (sctx, i, BSNat), r),
           HType)
        | U.TiBool (i, r) =>
	  (TiBool (check_basic_sort gctx (sctx, i, BSBool), r),
           HType)
        | U.TUnit r => (TUnit r, HType)
	| U.TProd (c1, c2) => 
	  (TProd (check_higher_kind_Type (ctx, c1),
	         check_higher_kind_Type (ctx, c2)),
           HType)
	| U.TUniI (s, Bind ((name, r), (i, t)), r_all) => 
          let
            val s = is_wf_sort gctx (sctx, s)
            val t = open_close add_sorting_sk (name, s) ctx
                               (fn ctx as (sctx, _) =>
                                   (check_Time_Nat gctx sctx i,
                                    check_higher_kind_Type (ctx, t)))
          in
	    (TUniI (s, Bind ((name, r), t), r_all),
             HType)
          end
        | U.TAbsI (b, Bind ((name, r1), t), r) =>
          let
            val b = is_wf_basic_sort b
            val (t, k) = open_close add_sorting_sk (name, SBasic (b, r1)) ctx (fn ctx => get_higher_kind (ctx, t))
            val k = HKArrowI (b, k)
          in
            (TAbsI (b, Bind ((name, r1), t), r), k)
          end
        (* | U.TSumbool (s1, s2) => *)
        (*   (TSumbool (is_wf_sort gctx (sctx, s1), is_wf_sort gctx (sctx, s2)), HType) *)
	| U.TBase a => (TBase a, HType)
        | U.TUVar ((), r) =>
          (* type underscore will always mean a type of kind Type *)
          (fresh_mt gctx (sctx, kctx) r, HType)
        | U.TVar x =>
          (TVar x, kind_to_higher_kind $ fetch_kind gctx (kctx, x))
        | U.TAbs (k1, Bind ((name, r1), t), r) =>
          let
            val k1 = is_wf_kind k1
            val (t, k) = get_higher_kind (add_kinding_sk (name, k1) ctx, t)
            val k1' = kind_to_higher_kind k1
            val k = HKArrow (k1', k)
          in
            (TAbs (k1, Bind ((name, r1), t), r), k)
          end
        | U.TApp (t1, t2) =>
          let
            val (t1, k) = get_higher_kind (ctx, t1)
          in
            case k of
                HKArrow (k1, k2) =>
                let
                  val t2 = check_higher_kind (ctx, t2, k1)
                in
                  (TApp (t1, t2), k2)
                end
              | _ => error (get_region_mt t1, str_mt gctxn ctxn t1, "<kind> => <kind>", str_hk, k)
          end
        | U.TAppI (t, i) =>
          let
            val (t, k) = get_higher_kind (ctx, t)
          in
            case k of
                HKArrowI (b, k) =>
                let
                  val i = check_basic_sort gctx (sctx, i, b)
                in
                  (TAppI (t, i), k)
                end
              | _ => error (get_region_mt t, str_mt gctxn ctxn t, "<sort> => <kind>", str_hk, k)
          end
        | U.TDatatype _ => raise Impossible "get_higher_kind()/TDatatype"
        | U.TRecord (fields, r) =>
	  (TRecord (SMap.map (curry check_higher_kind_Type ctx) fields, r),
           HType)
        | U.TState (x, r) =>
          let
            val () = if Option.isSome $ !(#1 st_types_ref) @! x then ()
                     else raise Error (r, [sprintf "state field $ not found" [x]])
          in
	    (TState (x, r), HType)
          end
        | U.TMap t =>
	  (TMap (check_higher_kind_Type (ctx, t)),
           HType)
        | U.TVector t =>
	  (TVector (check_higher_kind_Type (ctx, t)),
           HType)
        | U.TSCell t =>
	  (TSCell (check_higher_kind_Type (ctx, t)),
           HType)
        | U.TNatCell r => (TNatCell r, HType)
        | U.TPtr t =>
	  (TPtr $ check_higher_kind_Type (ctx, t),
           HType)
    val ret =
        main ()
        handle
        Error (r, msg) => raise Error (r, msg @ ["when kind-checking of type "] @ indent [US.str_mt gctxn ctxn c])
  in
    ret
  end

and check_higher_kind gctx (ctx, t, k) =
    let
      val (t, k') = get_higher_kind gctx (ctx, t)
      val () = unify_higher_kind (get_region_mt t) (k', k)
    in
      t
    end

and check_higher_kind_Type gctx (ctx, t) =
    check_higher_kind gctx (ctx, t, HType)

fun b2opt b = if b then SOME () else NONE

fun is_HKType k =
  case k of
      HKType => true
    | _ => false

fun higher_kind_to_kind k =
  case k of
      HKType => SOME Type
    | HKArrow (k1, k2) => opt_bind (b2opt $ is_HKType k1) (fn () => opt_bind (higher_kind_to_kind k2) (fn (n, sorts) => SOME (n + 1, sorts)))
    | HKArrowI (s, k) => opt_bind (higher_kind_to_kind k) (fn (n, sorts) => if n = 0 then SOME (0, s :: sorts) else NONE)

fun get_kind gctx (ctx as (sctx : scontext, kctx : kcontext), t : U.mtype) : mtype * kind =
  let
    val (t, k) = get_higher_kind gctx (ctx, t)
    val k = lazy_default (fn () => raise Error (get_region_mt t, kind_mismatch_in_type "first-order kind (i.e. * => ... <sort> => ... => *)" str_hk k (str_mt (gctx_names gctx) (sctx_names sctx, names kctx) t))) $ higher_kind_to_kind k
  in
    (t, k)
  end

fun check_kind gctx (ctx, t, k) =
    let
      val (t, k') = get_kind gctx (ctx, t)
      val () = unify_k (get_region_mt t) (k', k)
    in
      t
    end

fun check_kind_Type gctx (ctx, t) =
    check_kind gctx (ctx, t, Type)

fun is_wf_type gctx (ctx as (sctx : scontext, kctx : kcontext), c : U.ty) : ty = 
  let 
    val ctxn as (sctxn, kctxn) = (sctx_names sctx, names kctx)
	                           (* val () = print (sprintf "Type wellformedness checking: $\n" [str_t ctxn c]) *)
  in
    case c of
        U.PTMono t =>
        PTMono (check_kind_Type gctx (ctx, t))
      | U.PTUni (i, Bind ((name, r), c), r_all) => 
	PTUni (
          check_Time_Nat gctx sctx i,
          Bind ((name, r), is_wf_type gctx (add_kinding_sk (name, Type) ctx, c)),
          r_all)
  end

infix 6 %%+ 

infix 6 ++
fun a ++ b = binop_pair op+ (a, b)

infix 6 %%-
fun a %%- b = binop_pair (fn (a, b) => IBinOp (IBMinus (), a, b)) (a, b)
                        
fun smart_max a b =
  if eq_i a (T0 dummy) then
    b
  else if eq_i b (T0 dummy) then
    a
  else
    IBinOp (IBMax (), a, b)

fun smart_max_list ds = foldl' (fn (d, ds) => smart_max ds d) (T0 dummy) ds

fun smart_max_pair a b = binop_pair (uncurry smart_max) (a, b)
(* fun smart_max_pair_list ds = foldl' (fn (d, ds) => smart_max_pair ds d) (TN0 dummy) ds *)
                               
fun check_redundancy gctx (ctx as (_, _, cctx), t, prevs, this, r) =
  let
  in
    if is_redundant gctx (ctx, t, prevs, this) then ()
    else
      raise Error (r, sprintf "Redundant rule: $" [str_cover (gctx_names gctx) (names cctx) this] :: indent [sprintf "Has already been covered by previous rules: $" [(join ", " o map (str_cover (gctx_names gctx) (names cctx))) prevs]])
  end
    
fun check_exhaustion gctx (ctx as (_, _, cctx), t : mtype, covers, r) =
  let
  in
    case is_exhaustive gctx (ctx, t, covers) of
        NONE => ()
      | SOME missed =>
	raise Error (r, [sprintf "Not exhaustive, at least missing this case: $" [str_habitant (gctx_names gctx) (names cctx) missed]])
  end

fun get_ds (_, _, _, tctxd) = map (snd o snd) tctxd

fun escapes nametype name domaintype domain cause =
  [sprintf "$ $ escapes local scope in $ $" [nametype, name, domaintype, domain]] @ indent (if cause = "" then [] else ["cause: it is (potentially) used by " ^ cause])
	                                                                                   
fun forget_mt r gctxn (skctxn as (sctxn, kctxn)) (sctxl, kctxl) t = 
  let val t = forget_t_mt 0 kctxl t
	      handle ForgetError (x, cause) => raise Error (r, escapes "type variable" (str_v kctxn x) "type" (str_mt gctxn skctxn t) cause)
      val t = forget_i_mt 0 sctxl t
	      handle ForgetError (x, cause) => raise Error (r, escapes "index variable" (str_v sctxn x) "type" (str_mt gctxn skctxn t) cause)
  in
    t
  end

fun forget_ctx_mt r gctx (sctx, kctx) (sctxd, kctxd, _, _) t =
  let val (sctxn, kctxn) = (sctx_names sctx, names kctx)
      val sctxl = sctx_length sctxd
  in
    forget_mt r (gctx_names gctx) (sctxn, kctxn) (sctxl, length kctxd) t
  end
    
fun forget_t r gctxn (skctxn as (sctxn, kctxn)) (sctxl, kctxl) t = 
  let val t = forget_t_t 0 kctxl t
	      handle ForgetError (x, cause) => raise Error (r, escapes "type variable" (str_v kctxn x) "type" (str_t gctxn skctxn t) cause)
      val t = forget_i_t 0 sctxl t
	      handle ForgetError (x, cause) => raise Error (r, escapes "index variable" (str_v sctxn x) "type" (str_t gctxn skctxn t) cause)
  in
    t
  end

fun forget_ctx_t r gctx (sctx, kctx, _, _) (sctxd, kctxd, _, _) t =
  let val (sctxn, kctxn) = (sctx_names sctx, names kctx)
      val sctxl = sctx_length sctxd
  in
    forget_t r (gctx_names gctx) (sctxn, kctxn) (sctxl, length kctxd) t
  end
    
fun forget_d r gctxn sctxn sctxl d =
  forget_i_i 0 sctxl d
  handle ForgetError (x, cause) => raise Error (r, escapes "index variable" (str_v sctxn x) "time" (str_i gctxn sctxn d) cause)

(* val anno_less = ref true *)
val anno_less = ref false

fun substx_i_i_nonconsuming x v b =
  let
    val v = forget_i_i x 1 v
  in
    shiftx_i_i x 1 $ substx_i_i 0 x v b
  end
    
fun substx_i_p_nonconsuming x v b =
  let
    val v = forget_i_i x 1 v
  in
    shiftx_i_p x 1 $ substx_i_p 0 x v b
  end
    
fun forget_ctx_d r gctx sctx sctxd d =
  let
    val sctxn = sctx_names sctx
    val sctxl = sctx_length sctxd
    val d = 
        case (!anno_less, sctxd) of
            (true, (_, SSubset (bs, Bind (name, PBinConn (BCAnd (), p1, p2)), r)) :: sorts') =>
            let
              val ps = collect_PAnd p1
              fun change (p, (d, p2)) =
                case p of
                    PBinPred (BPEq (), IVar (ID (x, _), _), i) =>
                    (substx_i_i_nonconsuming x i d,
                     substx_i_p_nonconsuming x i p2)
                  | _ => (d, p2)
              val (d, p2) = foldl change (d, p2) ps
              exception Prop2IdxError
              fun prop2idx p =
                case p of
                    PBinPred (opr, i1, i2) =>
                    let
                      val opr =
                          case opr of
                              BPEq () => IBEq ()
                            | BPLt () => IBLt ()
                            | BPGe () => IBGe ()
                            | _ => raise Prop2IdxError                       
                    in
                      IBinOp (opr, i1, i2)
                    end
                  | PBinConn (opr, p1, p2) =>
                    let
                      val opr =
                          case opr of
                              BCAnd () => IBAnd ()
                            | _ => raise Prop2IdxError                       
                    in
                      IBinOp (opr, prop2idx p1, prop2idx p2)
                    end
                  | _ => raise Prop2IdxError                       
            in
              IIte (prop2idx p2, d, T0 dummy, dummy)
              handle Prop2IdxError => d
            end
          | _ => d
  in
    forget_d r (gctx_names gctx) sctxn sctxl d
  end

fun forget_ctx_2i r gctx sctx sctxd = unop_pair $ forget_ctx_d r gctx sctx sctxd 
fun shift_ctx_2i ctx = unop_pair $ shift_ctx_i ctx
fun simp_2i a = unop_pair simp_i a
fun update_2i a = unop_pair update_i a
      
fun mismatch gctx (ctx as (sctx, kctx, _, _)) e expect got =  
  (get_region_e e,
   "Type mismatch:" ::
   indent ["expect: " ^ expect, 
           "got: " ^ str_t gctx (sctx, kctx) got,
           "in: " ^ str_e gctx ctx e])

fun mismatch_anno gctx ctx expect got =  
  (get_region_t got,
   "Type annotation mismatch:" ::
   indent ["expect: " ^ expect,
           "got: " ^ str_t gctx ctx got])

fun is_wf_return gctx (skctx as (sctx, _), (t, d, j)) =
  (Option.map (fn t => check_kind_Type gctx (skctx, t)) t,
   Option.map (fn d => check_basic_sort gctx (sctx, d, BSTime)) d,
   Option.map (fn j => check_basic_sort gctx (sctx, j, BSNat)) j)

(* If i1 or i2 is fresh, do unification instead of VC generation. Could be too aggressive. *)
fun smart_write_le gctx ctx (i1, i2, r) =
  let
    (* val () = println $ sprintf "Check Le : $ <= $" [str_i ctx i1, str_i ctx i2] *)
    (* fun is_fresh_i i = *)
    (*   case i of *)
    (*       IUVar (x, _) => is_fresh x *)
    (*     | _ => false *)
    fun is_fresh_i i = isSome $ is_IBApp_IUVar i
  in
    if is_fresh_i i1 orelse is_fresh_i i2 then unify_i r gctx ctx (i1, i2)
    else
      write_le (i1, i2, r)
  end

fun smart_write_le_2i gctx ctx r = binop_pair (fn (i1, i2) => smart_write_le gctx ctx (i1, i2, r))
    
fun forget_or_check_return r gctx (ctx as (sctx, kctx)) ctxd (t', (d', j')) (t, d, j) =
  let
    val gctxn = gctx_names gctx
    val (sctxn, kctxn) = (sctx_names sctx, names kctx)
    val t =
        case t of
            SOME t =>
            let
              val () = unify_mt r gctx (sctx, kctx) (t', shift_ctx_mt ctxd t)
            in
              t
            end
          | NONE =>
            let
	      val t' = forget_ctx_mt r gctx ctx ctxd t' 
            in
              t'
            end
    val d = 
        case d of
            SOME d =>
            let
              val () = smart_write_le gctxn sctxn (d', shift_ctx_i ctxd d, r)
            in
              d
            end
          | NONE =>
            let 
	      val d' = forget_ctx_d r gctx sctx (#1 ctxd) d'
            in
              d'
            end
    val j = 
        case j of
            SOME j =>
            let
              val () = smart_write_le gctxn sctxn (j', shift_ctx_i ctxd j, r)
            in
              j
            end
          | NONE =>
            let 
	      val j' = forget_ctx_d r gctx sctx (#1 ctxd) j'
            in
              j'
            end
  in
    (t, (d, j))
  end

(* change sort [s] to a [SSubset (s.basic_sort, p)] *)
fun set_prop r s p =
  case normalize_s s of
      SBasic (bs as (_, r)) => SSubset (bs, Bind (("__set_prop", r), p), r)
    | SSubset (bs, Bind (name, _), r) => SSubset (bs, Bind (name, p), r)
    | SUVar _ => raise Error (r, ["unsolved unification variable in module"])
    | SAbs _ => raise Impossible "set_prop()/SAbs: shouldn't be prop"
    | SApp _ => raise Error (r, ["unsolved unification variable in module (unnormalized application)"])
                      
fun add_prop r s p =
  case normalize_s s of
      SBasic (bs as (_, r)) => SSubset (bs, Bind (("__added_prop", r), p), r)
    | SSubset (bs, Bind (name, p'), r) => SSubset (bs, Bind (name, p' /\ p), r)
    | SUVar _ => raise Error (r, ["unsolved unification variable in module"])
    | SAbs _ => raise Impossible "add_prop()/SAbs: shouldn't be prop"
    | SApp _ => raise Error (r, ["unsolved unification variable in module (unnormalized application)"])
                             
fun sort_add_idx_eq r s' i =
  add_prop r s' (IVar (ID (0, r), []) %= shift_i_i i)
           
type typing_info = decl list * context * idx list * context

fun str_typing_info gctxn (sctxn, kctxn) (ctxd : context, ds) =
  let
    fun on_ns ((name, s), (acc, sctxn)) =
      ([sprintf "$ ::: $" [name, str_s gctxn sctxn s](* , "" *)] :: acc, name :: sctxn)
    val (idx_lines, sctxn) = foldr on_ns ([], sctxn) $ #1 $ ctxd
    val idx_lines = List.concat $ rev idx_lines
    fun on_nk ((name, k), (acc, kctxn)) =
      ([sprintf "$ :: $" [name, str_ke gctxn (sctxn, kctxn) k](* , "" *)] :: acc, name :: kctxn)
    val (type_lines, kctxn) = foldr on_nk ([], kctxn) $ #2 $ ctxd
    val type_lines = List.concat $ rev type_lines
    val expr_lines =
        (concatMap (fn (name, t) => [sprintf "$ : $" [name, str_t gctxn (sctxn, kctxn) t](* , "" *)]) o rev o #4) ctxd
    val time_lines =
        "Times:" :: "" ::
        (concatMap (fn d => [sprintf "|> $" [str_i gctxn sctxn d](* , "" *)])) ds
    val lines = 
        idx_lines
        @ type_lines
        @ expr_lines
            (* @ time_lines  *)
  in
    lines
  end
    
fun str_sig gctxn ctx =
  ["sig"] @
  indent (str_typing_info gctxn ([], []) (ctx, [])) @
  ["end"]

fun str_gctx old_gctxn gctx =
  let 
    fun str_sigging ((name, sg), (acc, gctxn)) =
      let
        val (ls, gctxnd) =
            case sg of
                Sig ctx =>
                ([sprintf "structure $ : " [name] ] @
                 indent (str_sig gctxn ctx),
                 [(name, ctx_names ctx)])
              | FunctorBind ((arg_name, arg), body) =>
                ([sprintf "functor $ (structure $ : " [name, arg_name] ] @
                 indent (str_sig gctxn arg) @
                 [") : "] @
                 indent (str_sig (Gctx.add (arg_name, ctx_names arg) gctxn) body),
                 [])
      in
        (ls :: acc, addList (gctxn, gctxnd))
      end
    val typing_lines = List.concat $ rev $ fst $ foldr str_sigging ([], old_gctxn) gctx
    val lines = 
        typing_lines @
        [""]
  in
    lines
  end

(* fun str_gctx gctxn gctx = *)
(*   let *)
(*     val gctxn = union (gctxn, gctx_names $ to_map gctx) *)
(*     fun str_sigging (name, sg) = *)
(*       case sg of *)
(*           Sig ctx => *)
(*           [sprintf "structure $ : " [name] ] @ *)
(*           indent (str_sig gctxn ctx) *)
(*         | FunctorBind ((arg_name, arg), body) => *)
(*           [sprintf "functor $ (structure $ : " [name, arg_name] ] @ *)
(*           indent (str_sig gctxn arg) @ *)
(*           [") : "] @ *)
(*           indent (str_sig (curry Gctx.insert' (arg_name, ctx_names arg) gctxn) body) *)
(*     val typing_lines = concatMap str_sigging gctx *)
(*     val lines =  *)
(*         typing_lines @ *)
(*         [""] *)
(*   in *)
(*     lines *)
(*   end *)

fun is_value (e : U.expr) : bool =
  let
    open U
  in
    case e of
        EVar _ => true (* todo: is this right? *)
      | EConst _ => true
      | EEnv _ => true
      | EState _ => true
      | EUnOp (opr, e, _) =>
        (case opr of
             EUProj _ => false
           | EUPtrProj _ => false
           | EUArrayLen () => false
           | EUPrim _ => false
           | EUNat2Int () => false
           | EUInt2Nat () => false
           | EUPrintc () => false
        (* | EUPrint () => false *)
           | EUStorageGet () => false
           | EUNatCellGet () => false
           | EUVectorClear () => false
           | EUVectorLen () => false
           | EUAnno _ => is_value e
           | EUField _ => false
        )
      | EBinOp (opr, e1, e2) =>
        (case opr of
             EBApp () => false
           | EBPair () => is_value e1 andalso is_value e2
           | EBNew () => false
           | EBRead () => false
           | EBPrim _ => false
           | EBNat _ => false
           | EBNatCmp _ => false
           | EBiBool _ => false
           | EBIntNatExp () => false
           | EBVectorGet () => false
           | EBVectorPushBack () => false
           | EBMapPtr () => false
           | EBStorageSet () => false
           | EBNatCellSet () => false
        )
      | ERecord (fields, _) => SMapU.all is_value fields
      | ENewArrayValues _ => false
      | ETriOp (opr, _, _, _) =>
        (case opr of
             ETWrite () => false
           | ETIte () => false
           | ETVectorSet () => false
        )                        
      | EEI (opr, e, i) =>
        (case opr of
             EEIAppI () => false
           (* | EEIAscTime () => false *)
           | EEIAscTime () => is_value e
           | EEIAscSpace () => is_value e
        )
      | EET (opr, e, t) =>
        (case opr of
             EETAppT () => false
           (* | EETAsc () => false *)
           | EETAsc () => is_value e
           | EETHalt () => false
        )
      | ET (opr, t, _) =>
        (case opr of
             ETNever () => true
           | ETBuiltin name => true
        )
      | EAbs _ => true
      | EAbsI _ => true
      | ELet _ => false
      | EAppConstr (_, _, _, e, _) => is_value e
      | ECase _ => false
      (* | ECaseSumbool _ => false *)
      | EIfi _ => false
      | ESet _ => false
      | EGet _ => false
  end

fun get_msg_info_type r name =
    case name of
        EnvSender () => TInt r
      | EnvValue () => TInt r
      | EnvNow () => TInt r
      | EnvThis () => TInt r
      | EnvBalance () => TInt r
      | EnvBlockNumber () => TInt r

fun get_expr_const_type (c, r) =
  case c of
      ECNat n => 
      if n >= 0 then
	TNat (INat (n, r), r)
      else
	raise Error (r, ["Natural number constant must be non-negative"])
    | ECiBool b => TiBool (IConst (ICBool b, r), r)
    | ECTT () => 
      TUnit r
    | ECInt n => 
      TInt r
    | ECBool _ => 
      TBool r
    | ECByte _ =>
      TByte r
    (* | ECString s =>  *)
(*   TBase (String, r) *)

fun get_prim_expr_un_op_arg_ty opr =
  case opr of
      EUPIntNeg () => BTInt ()
    | EUPBoolNeg () => BTBool ()
    | EUPBitNot () => BTInt ()
    | EUPInt2Byte () => BTInt ()
    | EUPByte2Int () => BTByte ()
    (* | EUPInt2Str () => Int *)
    (* | EUPStrLen () => String *)
               
fun get_prim_expr_un_op_res_ty opr =
  case opr of
      EUPIntNeg () => BTInt ()
    | EUPBoolNeg () => BTBool ()
    | EUPBitNot () => BTInt ()
    | EUPInt2Byte () => BTByte ()
    | EUPByte2Int () => BTInt ()
    (* | EUPInt2Str () => String *)
    (* | EUPStrLen () => Int *)
               
fun get_prim_expr_bin_op_arg1_ty opr =
  case opr of
      EBPIntAdd () => BTInt ()
    | EBPIntMult () => BTInt ()
    | EBPIntMinus () => BTInt ()
    | EBPIntDiv () => BTInt ()
    | EBPIntMod () => BTInt ()
    | EBPIntExp () => BTInt ()
    | EBPIntAnd () => BTInt ()
    | EBPIntOr () => BTInt ()
    | EBPIntXor () => BTInt ()
    | EBPIntLt () => BTInt ()
    | EBPIntGt () => BTInt ()
    | EBPIntLe () => BTInt ()
    | EBPIntGe () => BTInt ()
    | EBPIntEq () => BTInt ()
    | EBPIntNEq () => BTInt ()
    | EBPBoolAnd () => BTBool ()
    | EBPBoolOr () => BTBool ()
    (* | EBPStrConcat () => String *)
      
fun get_prim_expr_bin_op_arg2_ty opr =
  case opr of
      EBPIntAdd () => BTInt ()
    | EBPIntMult () => BTInt ()
    | EBPIntMinus () => BTInt ()
    | EBPIntDiv () => BTInt ()
    | EBPIntMod () => BTInt ()
    | EBPIntExp () => BTInt ()
    | EBPIntAnd () => BTInt ()
    | EBPIntOr () => BTInt ()
    | EBPIntXor () => BTInt ()
    | EBPIntLt () => BTInt ()
    | EBPIntGt () => BTInt ()
    | EBPIntLe () => BTInt ()
    | EBPIntGe () => BTInt ()
    | EBPIntEq () => BTInt ()
    | EBPIntNEq () => BTInt ()
    | EBPBoolAnd () => BTBool ()
    | EBPBoolOr () => BTBool ()
    (* | EBPStrConcat () => String *)
      
fun get_prim_expr_bin_op_res_ty opr =
  case opr of
      EBPIntAdd () => BTInt ()
    | EBPIntMult () => BTInt ()
    | EBPIntMinus () => BTInt ()
    | EBPIntDiv () => BTInt ()
    | EBPIntMod () => BTInt ()
    | EBPIntExp () => BTInt ()
    | EBPIntAnd () => BTInt ()
    | EBPIntOr () => BTInt ()
    | EBPIntXor () => BTInt ()
    | EBPIntLt () => BTBool ()
    | EBPIntGt () => BTBool ()
    | EBPIntLe () => BTBool ()
    | EBPIntGe () => BTBool ()
    | EBPIntEq () => BTBool ()
    | EBPIntNEq () => BTBool ()
    | EBPBoolAnd () => BTBool ()
    | EBPBoolOr () => BTBool ()
    (* | EBPStrConcat () => String *)

(* fun assert_TCell' got r (t, path) = *)
(*   case path of *)
(*       [] => t *)
(*     | proj :: path => *)
(*       let *)
(*         val t = *)
(*             case (t, proj) of *)
(*                 (TProd (t1, t2), inl n) => *)
(*                 if n = 0 then t1 *)
(*                 else if n = 1 then t2 *)
(*                 else raise Error (r (), [sprintf "tuple offset $ out of bound in type $" [str_int n, got ()]]) *)
(*               | (TRecord (fields, _), inr name) => *)
(*                 (case SMap.find (fields, name) of *)
(*                      SOME a => a *)
(*                    | _ => raise Error (r (), [sprintf "field name $ not found in type $" [name, got ()]]) *)
(*                 ) *)
(*               | _ => raise Error (r (), [sprintf "wrong projector $ for type $" [str_sum str_int id proj, got ()]]) *)
(*       in *)
(*         assert_TCell' got r (t, path) *)
(*       end *)
(* fun assert_TCell got r t = *)
(*   let *)
(*     val (t, (path, _)) = *)
(*         case t of *)
(*             TPtr a => a *)
(*           | _ => raise Error (r (), "type mismatch:" :: *)
(*                                     indent ["expect: pointer", *)
(*                                             "got: " ^ got ()]) *)
(*   in *)
(*     assert_TCell' got r (t, path) *)
(*   end *)
    
fun assert_TPtr got r t =
  case t of
      TPtr a => a
    | _ => raise Error (r (), "type mismatch:" ::
                              indent ["expect: pointer",
                                      "got: " ^ got ()])
                 
fun assert_TMap err t =
  case t of
      TMap a => a
    | _ => err ()
fun assert_TVector err t =
  case t of
      TVector a => a
    | _ => err ()
               
fun is_constr e =
  case e of
      EUnOp (EUAnno (EAConstr ()), e, _) => (true, e)
    | _ => (false, e)
               
fun N n = INat (n, dummy)
fun TN n = (to_real n, N 0)

fun match_ptrn gctx (ctx as (sctx : scontext, kctx : kcontext, cctx : ccontext), (* pcovers, *) pn : U.ptrn, t : mtype) : ptrn * cover * context * int =
  let
    val match_ptrn = match_ptrn gctx
    val gctxn = gctx_names gctx
    val skctxn as (sctxn, kctxn) = (sctx_names sctx, names kctx)
    (* val () = println $ sprintf "Checking pattern $ for type $" [U.str_pn gctxn (sctxn, kctxn, names cctx) pn, str_mt gctxn (sctxn, kctxn) t] *)
    (* val () = println $ "sctxn=" ^ (str_ls id sctxn) *)
  in
    case pn of
	U.PnConstr (Outer ((cx, ()), eia), inames, opn, r) =>
 	let
          val inames = map binder2str inames
          val c as (family, tbinds) = snd $ fetch_constr gctx (cctx, cx)
          val siblings = map fst $ get_family_siblings gctx cctx cx
          val pos_in_family = indexOf (curry eq_var cx) siblings !! (fn () => raise Impossible "family_pos")
          val (tname_kinds, ibinds) = unfold_binds tbinds
          val tnames = map fst tname_kinds
          val (name_sorts, (t1, is')) = unfold_binds ibinds
          val () = if eia then () else raise Impossible "eia shouldn't be false"
          val ts = map (fn _ => fresh_mt gctx (sctx, kctx) r) tnames
          val is = map (fn _ => fresh_i gctx sctx (fresh_basic_sort ()) r) is'
          val t_constr = TAppIs (TApps (TVar family) ts) is
	  val () = unify_mt r gctx (sctx, kctx) (t, t_constr)
                   handle
                   Error _ =>
                   let
                     val expect = str_mt gctxn skctxn t
                     val got = str_mt gctxn skctxn t_constr
                   in
                     raise Error
                           (r, sprintf "Type of constructor $ doesn't match datatype " [str_var #3 gctxn (names cctx) cx] ::
                               indent ["expect: " ^ expect,
                                       "got: " ^ got])
                   end
          val length_name_sorts = length name_sorts
          val () =
              if length inames = length_name_sorts then ()
              else raise Error (r, [sprintf "This constructor requires $ index argument(s), not $" [str_int (length_name_sorts), str_int (length inames)]])
          val ts = map (normalize_mt true gctx kctx) ts
          val is = map normalize_i is
	  val ts = map (shiftx_i_mt 0 (length_name_sorts)) ts
	  val is = map (shiftx_i_i 0 (length_name_sorts)) is
	  val t1 = subst_ts_mt ts t1
	  val ps = ListPair.map (fn (a, b) => PBinPred (BPEq (), a, b)) (is', is)
          (* val () = println "try piggyback:" *)
          (* val () = println $ str_ls (fn (name, sort) => sprintf "$: $" [name, sort]) $ str_sctx gctx $ rev name_sorts *)
          val sorts = rev $ map snd name_sorts
          val sorts =
              case (!anno_less, sorts) of
                  (true, SSubset (bs, Bind (name, p), r) :: sorts') =>
                  (* piggyback the equalities on a SSubset sort *)
                  let
                    (* val () = println "piggyback!" *)
                  in
                    SSubset (bs, Bind (name, combine_And ps /\ p), r) :: sorts'
                  end
                | _ => sorts
          val ctxd = ctx_from_full_sortings o ListPair.zip $ (rev inames, sorts)
          val () = open_ctx ctxd
          val () = open_premises ps
          val ctx = add_ctx_skc ctxd ctx
          val pn1 = opn
          val (pn1, cover, ctxd', nps) = match_ptrn (ctx, pn1, t1)
          val ctxd = add_ctx ctxd' ctxd
          val cover = ConstrC (cx, cover)
        in
	  (PnConstr (Outer ((cx, (length siblings, pos_in_family)), true), map str2ibinder inames, pn1, r), cover, ctxd, length ps + nps)
	end
      | U.PnVar ename =>
        let
          val name = binder2str ename
          (* val pcover = combine_covers pcovers *)
          (* val cover = cover_neg cctx t pcover *)
          fun is_first_capital s =
            String.size s >= 1 andalso Char.isUpper (String.sub (s, 0))
          val () = if is_first_capital name then println $ sprintf "Warning: pattern $ is treated as a wildcard (did you misspell a constructor name?)" [name]
                   else ()
        in
          (PnVar ename, TrueC, ctx_from_typing (name, PTMono t), 0)
        end
      | U.PnPair (pn1, pn2) =>
        let 
          val r = U.get_region_pn pn
          val t1 = fresh_mt gctx (sctx, kctx) r
          val t2 = fresh_mt gctx (sctx, kctx) r
          (* val () = println $ sprintf "before: $ : $" [U.str_pn (sctxn, kctxn, names cctx) pn, str_mt skctxn t] *)
          val () = unify_mt r gctx (sctx, kctx) (t, TProd (t1, t2))
          (* val () = println "after" *)
          val (pn1, cover1, ctxd, nps1) = match_ptrn (ctx, pn1, t1)
          val ctx = add_ctx_skc ctxd ctx
          val (pn2, cover2, ctxd', nps2) = match_ptrn (ctx, pn2, shift_ctx_mt ctxd t2)
          val ctxd = add_ctx ctxd' ctxd
        in
          (PnPair (pn1, pn2), PairC (cover1, cover2), ctxd, nps1 + nps2)
        end
      | U.PnTT r =>
        let
          val () = unify_mt r gctx (sctx, kctx) (t, TUnit dummy)
        in
          (PnTT r, TTC, empty_ctx, 0)
        end
      | U.PnAlias (ename, pn, r) =>
        let
          val pname = binder2str ename
          val ctxd = ctx_from_typing (pname, PTMono t)
          val (pn, cover, ctxd', nps) = match_ptrn (ctx, pn, t)
          val ctxd = add_ctx ctxd' ctxd
        in
          (PnAlias (ename, pn, r), cover, ctxd, nps)
        end
      | U.PnAnno (pn1, Outer t') =>
        let
          val t' = check_kind_Type gctx ((sctx, kctx), t')
          val () = unify_mt (U.get_region_pn pn) gctx (sctx, kctx) (t, t')
          val (pn1, cover, ctxd, nps) = match_ptrn (ctx, pn1, t')
        in
          (PnAnno (pn1, Outer t'), cover, ctxd, nps)
        end
  end

(* expand wildcard rules to reveal premises *)    
fun expand_rules gctx (ctx as (sctx, kctx, cctx), rules, t, r) =
  let
    fun expand_rule (rule as (pn, e), (pcovers, rules)) =
      let
        (* todo: run match_ptrn only to get [cover]? If so, that functionality should be carved out. *)
	val (pn, cover, ctxd, nps) = match_ptrn gctx (ctx, (* pcovers, *) pn, t)
        val () = close_n nps
        val () = close_ctx ctxd
        (* val cover = ptrn_to_cover pn *)
        (* val () = println "before check_redundancy()" *)
        val () = check_redundancy gctx (ctx, t, pcovers, cover, get_region_pn pn)
        (* val () = println "after check_redundancy()" *)
        val (pcovers, new_rules) =
            case (pn, e) of
                (PnVar _, U.ET (ETNever (), U.TUVar ((), _), _)) =>
                let
                  fun hab_to_ptrn cctx (* cutoff *) t hab =
                    let
                      (* open UnderscoredExpr *)
                      (* exception Error of string *)
                      (* fun runError m () = *)
                      (*   SOME (m ()) handle Error _ => NONE *)
                      fun loop (* cutoff *) t hab =
                        let
                          (* val t = normalize_mt t *)
                          val t = whnf_mt true gctx kctx t
                          fun default () = raise Impossible "hab_to_ptrn"
                        in
                          case hab of
                              ConstrH (x, h') =>
                              (case is_TAppV t of
                                   SOME (family, ts, _) =>
                                   let
                                     val (_, tbinds) = snd $ fetch_constr gctx (cctx, x)
                                     val (_, ibinds) = unfold_binds tbinds
                                     val (name_sorts, (t', _)) = unfold_binds ibinds
	                             val t' = subst_ts_mt ts t'
                                     (* cut-off so that [expand_rules] won't try deeper and deeper proposals *) 
                                     val pn' =
                                         loop (* (cutoff - 1) *) t' h'
                                              (* if cutoff > 0 then *)
                                              (*   loop (cutoff - 1) t' h' *)
                                              (* else *)
                                              (*   PnVar ("_", dummy) *)
                                   in
                                     PnConstr (Outer ((x, ()), true), repeat (length name_sorts) $ str2ibinder "_", pn', dummy)
                                   end
                                 | NONE => default ()
                              )
                            | TTH =>
                              (case t of
                                   TUnit _ =>
                                   PnTT dummy
                                 | _ => default ()
                              )
                            | PairH (h1, h2) =>
                              (case t of
                                   TProd (t1, t2) =>
                                   PnPair (loop (* cutoff *) t1 h1, loop (* cutoff *) t2 h2)
                                 | _ => default ()
                              )
                            | TrueH => PnVar $ str2ebinder "_"
                        end
                    in
                      (* runError (fn () => loop t hab) () *)
                      loop (* cutoff *) t hab
                    end
                  fun ptrn_to_cover pn =
                    let
                      (* open UnderscoredExpr *)
                    in
                      case pn of
                          PnConstr (Outer ((x, ()), _), _, pn, _) => ConstrC (x, ptrn_to_cover pn)
                        | PnVar _ => TrueC
                        | PnPair (pn1, pn2) => PairC (ptrn_to_cover pn1, ptrn_to_cover pn2)
                        | PnTT _ => TTC
                        | PnAlias (_, pn, _) => ptrn_to_cover pn
                        | PnAnno (pn, _) => ptrn_to_cover pn
                    end
                  fun convert_pn pn =
                    case pn of
                        PnTT a => U.PnTT a
                      | PnPair (pn1, pn2) => U.PnPair (convert_pn pn1, convert_pn pn2)
                      | PnConstr (x, inames, opn, r) => U.PnConstr (x, inames, convert_pn opn, r) 
                      | PnVar a => U.PnVar a
                      | PnAlias (name, pn, r) => U.PnAlias (name, convert_pn pn, r)
                      | PnAnno _ => raise Impossible "convert_pn can't convert AnnoP"
                  fun loop pcovers =
                    case any_missing false(*treat empty datatype as inhabited, so as to get a shorter proposal*) gctx ctx t $ combine_covers pcovers of
                        SOME hab =>
                        let
                          val pn = hab_to_ptrn cctx (* 10 *) t hab
                          (* val () = println $ sprintf "New pattern: $" [str_pn (names sctx, names kctx, names cctx) pn] *)
                          val (pcovers, rules) = loop $ pcovers @ [ptrn_to_cover pn]
                        in
                          (pcovers, [(convert_pn pn, e)] @ rules)
                        end
                      | NONE => (pcovers, [])
                  val (pcovers, rules) = loop pcovers
                in
                  (pcovers, rules)
                end
              | _ => (pcovers @ [cover], [rule])
      in
        (pcovers, rules @ new_rules)
      end
    val (pcovers, rules) = foldl expand_rule ([], []) $ rules
    val () = check_exhaustion gctx (ctx, t, pcovers, r);
  in
    rules
  end

fun get_rules_cost_adjustments (get_inj : 'cvar -> int * int) (rules : (('cvar, 'mtype) Pattern.ptrn * bool) list) =
    let
      open PatternEx
      val pns = map fst rules
      datatype fake_expr =
               FEConst of int
               | FEUnPair of fake_expr
               | FEUnSum of fake_expr list
               | FEUnfold of fake_expr
               | FEUnpackI of fake_expr
      val pns = map (from_TiML_ptrn get_inj) pns
      val pns = mapi (fn (n, pn) => PnBind (pn, FEConst n)) pns
      val shift_i_e = return3
      val shift_e_e = return3
      val subst_e_e = return4 
      val EV = FEConst
      fun str_e e = "[expr]"
      fun EMatchPair (matchee, ename1, ename2, e) =
        FEUnPair e
      fun EMatchSum (matchee, cases) =
        FEUnSum $ map snd cases
      fun EMatchUnfold (matchee, ename, e) =
        FEUnfold e
      fun EUnpackI (matchee, iname, ename, e) =
        FEUnpackI e
      val e = to_expr (shift_i_e, shift_e_e, subst_e_e, EV, str_e, (EMatchPair, EMatchSum, EMatchUnfold, EUnpackI)) (EV 0) pns
      datatype cost =
               CUnPair
               | CUnSum of int * int
               | CUnfold
               | CUnpackI
      fun collect_cost acc e =
        let
          val f = collect_cost
        in
          case e of
              FEConst n => [(n, acc)]
            | FEUnPair e => f (CUnPair :: acc) e
            | FEUnSum es =>
              let
                val len = length es
              in
                concatMapi (fn (i, e) => f (CUnSum (len, i) :: acc) e) es
              end
            | FEUnfold e => f (CUnfold :: acc) e
            | FEUnpackI e => f (CUnpackI :: acc) e
        end
      fun C_ECaseMany (len, i) =
        (assert_b "C_ECaseMany: len = 2" (len = 2);
         C_Case_BeforeCodeGen + i * C_JUMPDEST)
      fun eval_cost c =
        case c of
            CUnPair => 2 * C_EProj
          | CUnfold => C_EUnfold
          | CUnpackI => C_EUnpack
          | CUnSum (len, i) => C_ECaseMany (len, i)
      val () = println $ "C_EProj = " ^ str_int C_EProj
      val () = println $ "C_EUnfold = " ^ str_int C_EUnfold
      val () = println $ "C_EUnpack = " ^ str_int C_EUnpack
      val () = println $ "C_Case_BeforeCodeGen = " ^ str_int C_Case_BeforeCodeGen
      val () = println $ "C_ECaseMany (2, 0) = " ^ str_int (C_ECaseMany (2, 0))
      val () = println $ "C_ECaseMany (2, 1) = " ^ str_int (C_ECaseMany (2, 1))
      val () = println $ "C_App_BeforeCC = " ^ str_int C_App_BeforeCC
      val costs = collect_cost [] e
      fun str_cost c =
        case c of
            CUnPair => "CUnPair"
          | CUnfold => "CUnfold"
          | CUnpackI => "CUnpackI"
          | CUnSum (len, i) => sprintf "CUnSum ($, $)" [str_int len, str_int i]
      val () = println "costs:"
      val () = app println $ map (str_pair (str_int, str_ls str_cost)) costs
      val costs = IMapU.fromList_multi costs
      val costs = IMap.map (max_from_0 o map (sum o map eval_cost)) costs
      val () = println $ IMapU.str_map (str_int, str_int) costs
      fun m @! k = IMap.find (m, k)
      fun get_cost n = default 0 $ costs @! n
      val tail_app_cost = (C_App_BeforeCC, M_App_BeforeCC)
      val len = length rules
      fun get_tail_app_cost e =
        if len <= 1 orelse e then (0, 0) else tail_app_cost
      val ds = mapi (fn (n, rl) => (get_cost n, 0) ++ get_tail_app_cost (snd rl)) rules
      (* val () = println "after adjust:" *)
      (* val () = app println $ map (str_i Gctx.empty []) $ map fst ds *)
    in
      ds
    end
      
fun is_nullable_wordsize_ty t =
    case t of
        TNat _ => true
      | TiBool _ => true
      | TBase (t, _) =>
        (case t of
             BTInt () => true
           | BTBool () => true
           | BTByte () => true
        )
      | TUnit _ => true
      | _ => false
        
fun is_wordsize_ty t =
    if is_nullable_wordsize_ty t then true
    else
      case t of
          (* todo: single-constructor datatypes could also be wordsize *)
          _ => false
        
fun flatten_tuple_record t =
  let
    val loop = flatten_tuple_record
  in
    case t of
        (* TTuple (ts, _) => concatMap loop ts *)
        TProd (t1, t2) => loop t1 @ loop t2
      | TRecord (fields, _) => concatMap loop $ map snd $ sort cmp_str_fst $ listItemsi fields
      | _ => [t]
  end
    
fun get_mtype gctx (ctx_st : context_state) (e_all : U.expr) : expr * mtype * (idx * idx) * idx StMap.map =
  let
    val (ctx, st) = ctx_st
    val (sctx, kctx, cctx, tctx) = ctx
    val get_mtype = get_mtype gctx
    val check_mtype = check_mtype gctx
    val check_time = check_time gctx
    val check_space = check_space gctx
    val check_mtype_time = check_mtype_time gctx
    val check_decl = check_decl gctx
    val check_decls = check_decls gctx
    val check_rule = check_rule gctx
    val check_rules = check_rules gctx
    val st_types = !(#1 st_types_ref)
    val skctx = (sctx, kctx)
    val gctxn = gctx_names gctx
    val ctxn as (sctxn, kctxn, cctxn, tctxn) = ctx_names (sctx, kctx, cctx, tctx)
    val skctxn = (sctxn, kctxn)
    (* val () = print $ sprintf "Typing $\n" [US.str_e gctxn ctxn e_all] *)
    (* val () = print $ sprintf "  Typing $\n" [U.str_raw_e e_all] *)
    (* fun print_ctx gctx (ctx as (sctx, kctx, _, tctx)) = *)
    (*   let *)
    (*     (* val () = println $ str_ls (fn (name, sort) => sprintf "$: $" [name, sort]) $ str_sctx gctx sctx *) *)
    (*                      (* val () = println $ str_ls fst kctx *) *)
    (*     val () = app println $ map (fn (nm, t) => sprintf "$: $" [nm, str_t (gctx_names gctx) (sctx_names sctx, names kctx) t]) tctx *)
    (*   in *)
    (*     () *)
    (*   end *)
    (* val () = print_ctx gctx ctx *)
    fun get_vector r st t1 =
      let
        val x = case t1 of
                    TState (x, _) => x
                  | t1 => raise Error (r (), "type mismatch" ::
                                                        indent ["expect: state_field _",
                                                                "got: " ^ str_mt gctxn skctxn t1])
        val t = case st_types @!! x of
                    TVector t => t
                  | _ => raise Error (r (), [sprintf "type of $ should be vector" [str_st_key x]])
        val len = case st @! x of
                      SOME a => a
                    | _ => raise Error (r (), [sprintf "state field $ must be in state spec" [str_st_key x]])
      in
        (x, t, len)
      end
    fun get_nat_cell r st t1 =
      let
        val x = case t1 of
                    TState (x, _) => x
                  | t1 => raise Error (r (), "type mismatch" ::
                                                        indent ["expect: state_field _",
                                                                "got: " ^ str_mt gctxn skctxn t1])
        val () = case st_types @!! x of
                    TNatCell _ => ()
                  | _ => raise Error (r (), [sprintf "type of $ should be nat cell" [str_st_key x]])
        val i = case st @! x of
                      SOME a => a
                    | _ => raise Error (r (), [sprintf "state field $ must be in state spec" [str_st_key x]])
      in
        (x, i)
      end
    fun assert_wordsize_ty r t = if is_wordsize_ty t then ()
                                 else raise Error (r, ["must be word-sized type"])
    fun main () =
      case e_all of
	  U.EVar (x, eia) => raise Impossible "EVar should be surrounded by EAnnoLiveVars"
	| U.EUnOp (opr as EUAnno (EALiveVars (n_live_vars, has_k)), U.EVar (x, (eia, has_insert)), r) =>
          let
            val r = U.get_region_long_id x
            val t = fetch_type gctx (tctx, x)
            val () = println $ "has_k = " ^ str_bool has_k
            val () = println $ "n_live_vars = " ^ str_int n_live_vars
            fun assert err p = if p then () else err ()
            fun has_insert_err () = raise Error (r, ["implicit index/type arguments must be annotated with %"])
          in
            if eia then
              let
                fun insert_type_args t =
                  case t of
                      PTMono t => (t, TN0 dummy, [])
                    | PTUni (d2, Bind (_, t), _) =>
                      let
                        (* val t_arg = fresh_mt (sctx, kctx) r *)
                        val t_arg = U.TUVar ((), r)
                        val t_arg = check_kind_Type gctx (skctx, t_arg)
                        val t = subst_t_t t_arg t
                        val (t, cost, t_args) = insert_type_args t
                        val closure_cost =
                            if has_k then
                              (C_Abs_BeforeCC n_live_vars + C_Abs_Inner_BeforeCC n_live_vars,
                               M_Abs_BeforeCC n_live_vars + M_Abs_Inner_BeforeCC n_live_vars)
                            else (0, 0)
                        val () = println $ "d2 = " ^ (str_i gctxn sctxn $ simp_i $ fst d2)
                        val () = println $ "closure_cost = " ^ str_int (fst closure_cost)
                        val cost = cost %%+ mapPair' to_real N (closure_cost ++ (C_App_BeforeCC, M_App_BeforeCC)) %%+ d2
                      in
                        (t, cost, t_arg :: t_args)
                      end
                val (t, cost, t_args) = insert_type_args t
                val () = assert has_insert_err (imply (length t_args > 0) has_insert)
                val e = EVar (x, (true, false))
                val e = EAppTs (e, t_args)
                val () = println $ "cost = " ^ (str_i gctxn sctxn $ simp_i $ fst cost)
              in
                (e, t, TN C_EVar %%+ cost, st)
              end
            else
              let
                val (_, t) = collect_PTUni t
                val (ibinds, _) = collect_TUniI t
                val () = assert has_insert_err (imply (length ibinds > 0) has_insert)
                val e = U.EAnnoLiveVars (U.EVar (x, (true, has_insert)), (n_live_vars, has_k), r)
                val e = U.EAppIs (e, repeat (length ibinds) (U.IUVar ((), r)))
              in
                get_mtype (ctx, st) e
              end
          end
        | U.EConst (c, r) => (EConst (c, r), get_expr_const_type (c, r), TN C_EConst, st)
        | U.EEnv (name, r) => (EEnv (name, r), get_msg_info_type r name, TN $ C_EEnv name, st)
        | U.EUnOp (opr as EUProj proj, e, r) =>
	  let 
            (* val r = U.get_region_e e *)
            val t1 = fresh_mt gctx (sctx, kctx) r
            val t2 = fresh_mt gctx (sctx, kctx) r
            val (e, d, st) = check_mtype ctx_st (e, TProd (t1, t2)) 
          in 
            (EUnOp (opr, e, r), choose (t1, t2) proj, d %%+ TN C_EProj, st)
	  end
        | U.EUnOp (opr as EUPrintc (), e, r) =>
          let
            val (e, d, st) = check_mtype ctx_st (e, TByte r) 
          in
            (EUnOp (opr, e, r), TUnit r, d %%+ TN C_EPrintc, st)
          end
        (* | EUPrint => *)
        (*   let *)
        (*     val (e, d) = check_mtype (ctx, e, TBase (String, dummy))  *)
        (*   in *)
        (*     (EUnOp (EUPrint, e, r), TUnit dummy, d) *)
        (*   end *)
        | U.EUnOp (EUPrim opr, e, r) =>
          let
            val (e, d, st) = check_mtype ctx_st (e, TBase (get_prim_expr_un_op_arg_ty opr, r)) 
          in
            (EUnOp (EUPrim opr, e, r), TBase (get_prim_expr_un_op_res_ty opr, r), d %%+ TN (C_EUPrim opr), st)
          end
	| U.EUnOp (opr as EUArrayLen (), e, r) =>
          let
            val r = U.get_region_e e_all
            val t = fresh_mt gctx (sctx, kctx) r
            val i = fresh_i gctx sctx BSNat r
            val (e, d, st) = check_mtype ctx_st (e, TArray (t, i))
          in
            (EUnOp (opr, e, r), TNat (i, r), d %%+ TN C_EArrayLen, st)
          end
	| U.EUnOp (opr as EUNat2Int (), e, r) =>
          let
            val r = U.get_region_e e_all
            val i = fresh_i gctx sctx BSNat r
            val (e, d, st) = check_mtype ctx_st (e, TNat (i, r))
          in
            (EUnOp (opr, e, r), TInt r, d %%+ TN C_ENat2Int, st)
          end
	| U.EUnOp (opr as EUInt2Nat (), e, r) =>
          let
            val r = U.get_region_e e_all
            val (e, d, st) = check_mtype ctx_st (e, TInt r)
          in
            (EUnOp (opr, e, r), TVar $ QID $ qid_add_r r SOME_NAT_ID, d %%+ TN C_EInt2Nat, st)
          end
	| U.EUnOp (opr as EUAnno anno, e, r) =>
          let
            val (e, t, i, st) = get_mtype (ctx, st) e
          in
            (EUnOp (opr, e, r), t, i, st)
          end
	| U.EBinOp (opr as EBPair (), e1, e2) =>
	  let 
            val (e1, t1, d1, st) = get_mtype (ctx, st) e1
	    val (e2, t2, d2, st) = get_mtype (ctx, st) e2
          in
	    (EPair (e1, e2), TProd (t1, t2), d1 %%+ d2 %%+ (to_real C_EPair, N 2), st)
	  end
	| U.EBinOp (opr as EBApp (), e1, e2) =>
	  let
            val r1 = U.get_region_e e1
            val (e1, t1, d1, st) = get_mtype (ctx, st) e1
            val (is_constr, e1) = is_constr e1
            val t1 = whnf_mt true gctx kctx t1
            val ((pre_st, t2), d, (post_st, t)) =
                case t1 of
                    TArrow a => a
                  | t1 =>
                    case is_TApp_TUVar t1 of
                        SOME _ =>
                        let
                          val t2 = fresh_mt gctx (sctx, kctx) r1
                          val d = fresh_i gctx sctx BSTime r1
                          val j = fresh_i gctx sctx BSNat r1
                          val t = fresh_mt gctx (sctx, kctx) r1
                          val arrow = ((StMap.empty, t2), (d, j), (StMap.empty, t))
                          val () = unify_mt r1 gctx (sctx, kctx) (t1, TArrow arrow)
                        in
                          arrow
                        end
                      | NONE =>
                        raise Error (r1, "type mismatch:" ::
                                         indent ["expect: _ -- _ --> _",
                                                 "got: " ^ str_mt gctxn skctxn t1])
            val (e2, t2', d2, st) = get_mtype (ctx, st) e2
            (* todo: if I swap (t2, t2'), unify_mt() has a bug that it unifies the index arguments too eagerly *)
            val r2 = get_region_e e2
            val () = unify_mt r2 gctx (sctx, kctx) (t2, t2')
            fun check_submap pre_st st =
              let
                val pre_st_minus_st = pre_st @-- st
              in
                if StMap.numItems pre_st_minus_st = 0 then ()
                else raise Error (r1, ["these state fields are required by the function but missing in current state:", str_ls str_st_key $ StMapU.domain pre_st_minus_st])
              end
            val () = check_submap pre_st st
            val () = StMap.appi (fn (k, v) => unify_i r1 gctxn sctxn (st @!! k, v)) pre_st
            val st = st @++ post_st
            val (e2, (n_live_vars, has_k)) = assert_EAnnoLiveVars (fn () => raise Error (r2, ["Should be EAnnoLiveVars"])) e2
            val cost = if has_k then
                         (C_Abs_BeforeCC n_live_vars + C_Abs_Inner_BeforeCC n_live_vars,
                          M_Abs_BeforeCC n_live_vars + M_Abs_Inner_BeforeCC n_live_vars)
                       else (0, 0)
            val cost = cost ++ (C_App_BeforeCPS, M_App_BeforeCPS)
          in
            (EApp (e1, e2), t, if is_constr then d2 else d1 %%+ d2 %%+ mapPair' to_real N cost %%+ d, st) 
	  end
	| U.EBinOp (opr as EBNew (), e1, e2) =>
          let
            val r = U.get_region_e e_all
            val len = fresh_i gctx sctx BSTime r
            val (e1, d1, st) = check_mtype (ctx, st) (e1, TNat (len, r))
            val (e2, t, d2, st) = get_mtype (ctx, st) e2
            val cost = N C_ENew_order0 %+ N C_ENew_order1 %* len
          in
            (EBinOp (opr, e1, e2), TArray (t, len), d1 %%+ d2 %%+ (IToReal (cost, dummy), len %+ N1 dummy), st)
          end
	| U.EBinOp (opr as EBRead (), e1, e2) =>
          let
            val r = U.get_region_e e_all
            val t = fresh_mt gctx (sctx, kctx) r
            val i1 = fresh_i gctx sctx BSTime r
            val i2 = fresh_i gctx sctx BSTime r
            val (e1, d1, st) = check_mtype (ctx, st) (e1, TArray (t, i1))
            val (e2, d2, st) = check_mtype (ctx, st) (e2, TNat (i2, r))
            val () = write_lt (i2, i1, r)
          in
            (EBinOp (opr, e1, e2), t, d1 %%+ d2 %%+ TN C_ERead, st)
          end
	| U.EBinOp (EBPrim opr, e1, e2) =>
	  let
            val (e1, d1, st) = check_mtype (ctx, st) (e1, TBase (get_prim_expr_bin_op_arg1_ty opr, dummy))
	    val (e2, d2, st) = check_mtype (ctx, st) (e2, TBase (get_prim_expr_bin_op_arg2_ty opr, dummy)) in
	    (EBinOp (EBPrim opr, e1, e2), TBase (get_prim_expr_bin_op_res_ty opr, dummy), d1 %%+ d2 %%+ TN (C_EBPrim opr), st)
	  end
	| U.EBinOp (opr as EBIntNatExp (), e1, e2) =>
          let
            val r = U.get_region_e e_all
            val i2 = fresh_i gctx sctx BSTime r
            val (e1, d1, st) = check_mtype (ctx, st) (e1, TInt r)
            val (e2, d2, st) = check_mtype (ctx, st) (e2, TNat (i2, r))
          in
            (EBinOp (opr, e1, e2), TInt r, d1 %%+ d2 %%+ (E_nat_exp_cost i2, N0 r), st)
          end
	| U.EBinOp (EBiBool opr, e1, e2) =>
          let
            val r = U.get_region_e e_all
            val i1 = fresh_i gctx sctx BSTime r
            val i2 = fresh_i gctx sctx BSTime r
            val (e1, d1, st) = check_mtype (ctx, st) (e1, TiBool (i1, r))
            val (e2, d2, st) = check_mtype (ctx, st) (e2, TiBool (i2, r))
            val i = interp_ibool_expr_bin_op opr (i1, i2)
          in
            (EBinOp (EBiBool opr, e1, e2), TiBool (i, r), d1 %%+ d2 %%+ TN (C_EiBool opr), st)
          end
	| U.EBinOp (EBNat opr, e1, e2) =>
          let
            val r = U.get_region_e e_all
            val i1 = fresh_i gctx sctx BSTime r
            val i2 = fresh_i gctx sctx BSTime r
            val (e1, d1, st) = check_mtype (ctx, st) (e1, TNat (i1, r))
            val (e2, d2, st) = check_mtype (ctx, st) (e2, TNat (i2, r))
            val i2 = Simp.simp_i $ update_i i2
            val () = if opr = EBNBoundedMinus () then write_le (i2, i1, r) else ()
            val i = interp_nat_expr_bin_op opr (i1, i2) (fn () => raise Error (r, ["Can only divide by a nat whose index is a constant, not: " ^ str_i gctxn sctxn i2]))
            val cost =
                case opr of
                    EBNExp () => E_nat_exp_cost i2
                  | _ => to_real $ C_ENat opr
          in
            (EBinOp (EBNat opr, e1, e2), TNat (i, r), d1 %%+ d2 %%+ (cost, N0 r), st)
          end
	| U.EBinOp (EBNatCmp opr, e1, e2) =>
          let
            val r = U.get_region_e e_all
            val i1 = fresh_i gctx sctx BSTime r
            val i2 = fresh_i gctx sctx BSTime r
            val (e1, d1, st) = check_mtype (ctx, st) (e1, TNat (i1, r))
            val (e2, d2, st) = check_mtype (ctx, st) (e2, TNat (i2, r))
          in
            (EBinOp (EBNatCmp opr, e1, e2), TiBool (interp_nat_cmp r opr (i1, i2), r), d1 %%+ d2 %%+ TN (C_ENatCmp opr), st)
          end
	| U.EBinOp (opr as EBVectorGet (), e1, e2) =>
          let
            val r = U.get_region_e e_all
            val (e1, t1, j1, st) = get_mtype (ctx, st) e1
            val i = fresh_i gctx sctx BSNat r
            val (e2, j2, st) = check_mtype (ctx, st) (e2, TNat (i, r))
            val t1 = whnf_mt true gctx kctx t1
            val (x, t, len) = get_vector (fn () => get_region_e e1) st t1
            val () = write_lt (i, len, r)
          in
            (EBinOp (opr, e1, e2), t, j1 %%+ j2 %%+ TN C_EVectorGet, st)
          end
        | U.ETriOp (ETVectorSet (), e1, e2, e3) =>
          let
            val r = U.get_region_e e_all
            val (e1, t1, j1, st) = get_mtype (ctx, st) e1
            val i = fresh_i gctx sctx BSNat r
            val (e2, j2, st) = check_mtype (ctx, st) (e2, TNat (i, r))
            val (e3, t3, j3, st) = get_mtype (ctx, st) e3
            val t1 = whnf_mt true gctx kctx t1
            val (x, t, len) = get_vector (fn () => get_region_e e1) st t1
            val () = unify_mt r gctx (sctx, kctx) (t3, t)
            val () = write_lt (i, len, r)
          in
            (ETriOp (ETVectorSet (), e1, e2, e3), TUnit r, j1 %%+ j2 %%+ j3 %%+ TN C_EVectorSet, st)
          end
	| U.EBinOp (opr as EBVectorPushBack (), e1, e2) =>
          let
            val r = U.get_region_e e_all
            val (e1, t1, j1, st) = get_mtype (ctx, st) e1
            val (e2, t2, j2, st) = get_mtype (ctx, st) e2
            val t1 = whnf_mt true gctx kctx t1
            val (x, t, len) = get_vector (fn () => get_region_e e1) st t1
            val () = unify_mt r gctx (sctx, kctx) (t2, t)
          in
            (EBinOp (opr, e1, e2), TUnit r, j1 %%+ j2 %%+ TN C_EVectorPushBack, st @+ (x, len %+ N1 r))
          end
	| U.EUnOp (opr as EUVectorLen (), e, r) =>
          let
            val (e, t, j, st) = get_mtype (ctx, st) e
            val t = whnf_mt true gctx kctx t
            val (_, _, len) = get_vector (fn () => r) st t
          in
            (EUnOp (opr, e, r), TNat (len, r), j %%+ TN C_EVectorLen, st)
          end
	| U.EUnOp (opr as EUVectorClear (), e, r) =>
          let
            val (e, t, j, st) = get_mtype (ctx, st) e
            val t = whnf_mt true gctx kctx t
            val (x, _, _) = get_vector (fn () => r) st t
          in
            (EUnOp (opr, e, r), TUnit r, j %%+ TN C_EVectorClear, st @+ (x, N0 r))
          end
	| U.EUnOp (opr as EUNatCellGet (), e, r) =>
          let
            val (e, t, j, st) = get_mtype (ctx, st) e
            val t = whnf_mt true gctx kctx t
            val (_, i) = get_nat_cell (fn () => r) st t
          in
            (EUnOp (opr, e, r), TNat (i, r), j %%+ TN C_ENatCellGet, st)
          end
        | U.EBinOp (opr as EBNatCellSet (), e1, e2) =>
          let
            val r = U.get_region_e e_all
            val (e1, t1, j1, st) = get_mtype (ctx, st) e1
            val new = fresh_i gctx sctx BSNat r
            val (e2, j2, st) = check_mtype (ctx, st) (e2, TNat (new, r))
            val t1 = whnf_mt true gctx kctx t1
            val (x, old) = get_nat_cell (fn () => get_region_e e1) st t1
            val store_cost = IIte' (old =? N 0 /\? new <>? N 0, to_real C_sset, to_real C_sreset)
          in
            (EBinOp (opr, e1, e2), TUnit r, j1 %%+ j2 %%+ TN C_ENatCellSet %%+ (store_cost, N0 r), st @+ (x, new))
          end
	| U.EUnOp (opr as EUField (name, _), e, r) =>
          let
            val (e, t, i, st) = get_mtype (ctx, st) e
            val t = whnf_mt true gctx kctx t
            val (fields, _) =
                case t of
                    TRecord a => a
                  | _ => raise Error (r, ["can't infer the record type"])
            val fields = sort cmp_str_fst $ SMap.listItemsi fields
            val (offset, (_, t)) =
                case findi (fn (name', t) => name = name') fields of
                    SOME a => a
                  | NONE => raise Error (r, ["field not found"])
          in
            (EUnOp (EUField (name, SOME offset), e, r), t, i, st)
          end
	(* | U.EBinOp (opr as EBMapPtr (path, _), e1, e2) => *)
        (*   let *)
        (*     val r = U.get_region_e e_all *)
        (*     val (e1, t1, j1, st) = get_mtype (ctx, st) e1 *)
        (*     val t1 = whnf_mt true gctx kctx t1 *)
        (*     fun err () = raise Error (get_region_e e1, "map_ptr(e1, e2): type of e1 is wrong:" :: *)
        (*                                                indent ["expect: pointer", *)
        (*                                                        "got: " ^ str_mt gctxn skctxn t1]) *)
        (*     val t = assert_TMap err $ assert_TCell (fn () => str_mt gctxn skctxn t1) (fn () => get_region_e e1) t1 *)
        (*     val (e2, j2, st) = check_mtype (ctx, st) (e2, TInt r) *)
        (*     fun calculate_offset t path = *)
        (*       case path of *)
        (*           [] => 0 *)
        (*         | proj :: path => *)
        (*           let *)
        (*             val (ts, proj) = *)
        (*                 case (t, proj) of *)
        (*                     (TProd (t1, t2), inl n) => ([t1, t2], n) *)
        (*                   | (TRecord (fields, _), inr name) => *)
        (*                     let *)
        (*                       val sorted = sort cmp_str_fst $ listItemsi fields *)
        (*                       val n = case indexOf (fn (name', _) => name = name') sorted of *)
        (*                                   SOME a => a *)
        (*                                 | NONE => raise Error (r, [sprintf "field $ not found" [name]]) *)
        (*                     in *)
        (*                       (map snd sorted, n) *)
        (*                     end *)
        (*                   | _ => raise Error (r, ["type and projector doesn't match"]) *)
        (*             val former = take n ts *)
        (*             val t = hd $ drop n ts *)
        (*             val former = concatMap flatten_tuple_record former *)
        (*           in *)
        (*             length former + calculate_offset t path *)
        (*           end *)
        (*     val offset = calculate_offset t path *)
        (*     val path = (path, SOME offset) *)
        (*   in *)
        (*     (EBinOp (EBMapPtr path, e1, e2), TPtr (t, path), j1 %%+ j2 %%+ TN C_EMapPtr, st) *)
        (*   end *)
	| U.EBinOp (opr as EBMapPtr (), e1, e2) =>
          let
            val r = U.get_region_e e_all
            val (e1, t1, j1, st) = get_mtype (ctx, st) e1
            val t1 = whnf_mt true gctx kctx t1
            fun err () = raise Error (get_region_e e1, "map_ptr(e1, e2): type of e1 is wrong:" ::
                                                       indent ["expect: pointer of map",
                                                               "got: " ^ str_mt gctxn skctxn t1])
            val t = assert_TMap err $ assert_TPtr (fn () => str_mt gctxn skctxn t1) (fn () => get_region_e e1) t1
            val (e2, j2, st) = check_mtype (ctx, st) (e2, TInt r)
          in
            (EBinOp (EBMapPtr (), e1, e2), TPtr t, j1 %%+ j2 %%+ TN C_EMapPtr, st)
          end
	| U.EUnOp (opr as EUPtrProj (proj, _), e, r) =>
          let
            val r = U.get_region_e e_all
            val (e, t, j, st) = get_mtype (ctx, st) e
            val t = whnf_mt true gctx kctx t
            fun err () = raise Error (get_region_e e, "pointer_proj e: type of e is wrong:" ::
                                                       indent ["expect: pointer",
                                                               "got: " ^ str_mt gctxn skctxn t])
            val t = assert_TPtr (fn () => str_mt gctxn skctxn t) (fn () => get_region_e e) t
            fun calculate_offset t proj =
              let
                val (ts, n) =
                    case (t, proj) of
                        (TProd (t1, t2), inl n) => ([t1, t2], n)
                      | (TRecord (fields, _), inr name) =>
                        let
                          val sorted = sort cmp_str_fst $ listItemsi fields
                          val n = case indexOf (fn (name', _) => name = name') sorted of
                                      SOME a => a
                                    | NONE => raise Error (r, [sprintf "field $ not found" [name]])
                        in
                          (map snd sorted, n)
                        end
                      | _ => raise Error (r, ["type and projector doesn't match"])
                val former = take n ts
                val t = hd $ drop n ts
                val former = concatMap flatten_tuple_record former
              in
                (t, length former)
              end
            val (t, offset) = calculate_offset t proj
            val len = length $ flatten_tuple_record t
            val proj = (proj, SOME (offset, len))
          in
            (EUnOp (EUPtrProj proj, e, r), TPtr t, j %%+ TN C_EPtrProj, st)
          end
        | U.EState (x, r) =>
          let
            val st_t = case st_types @! x of
                           SOME t => t
                         | _ => raise Error (r, [sprintf "unknown state field $" [str_st_key x]])
            val t =
                case st_t of
                    TMap _ => TPtr st_t
                  | TSCell t => TPtr t
                  | _ => TState (x, r)
          in
            (EState (x, r), t, TN C_EState, st)
          end
	| U.EUnOp (opr as EUStorageGet (), e, r) =>
          let
            val (e, t, j, st) = get_mtype ctx_st e
            val t = whnf_mt true gctx kctx t
            val t = assert_TPtr (fn () => str_mt gctxn skctxn t) (fn () => r) t
            val () = assert_wordsize_ty r t
          in
            (EUnOp (opr, e, r), t, j %%+ TN C_EStorageGet, st)
          end
	| U.EBinOp (opr as EBStorageSet (), e1, e2) =>
          let
            val r = U.get_region_e e_all
            val (e1, t1, j1, st) = get_mtype (ctx, st) e1
            val t1 = whnf_mt true gctx kctx t1
            val t = assert_TPtr (fn () => str_mt gctxn skctxn t1) (fn () => get_region_e e1) t1
            val () = assert_wordsize_ty r t
            val (e2, j2, st) = check_mtype (ctx, st) (e2, t)
          in
            (EBinOp (opr, e1, e2), TUnit r, j1 %%+ j2 %%+ TN C_EStorageSet, st)
          end
        | U.EGet (x, es, r) =>
          let
            val st_t = case st_types @! x of
                             SOME t => t
                          | _ => raise Error (r, [sprintf "unknown state field $" [str_st_key x]])
            val x = U.EState (x, r)
            val e =
                case st_t of
                    (* TMap _ => *)
                    (* let *)
                    (* in *)
                    (*   U.EStorageGet (foldl (fn (offset, acc) => U.EMapPtr (acc, offset)) x es, r) *)
                    (* end *)
                    TMap _ =>
                    let
                    in
                      U.EStorageGet (foldl (fn (offset, acc) => U.EMapPtrProj (acc, offset)) x es, r)
                    end
                  (* | TArray _ => *)
                  (*   let *)
                  (*     val x = U.EVar (ID (x, r), (false, false)) *)
                  (*   in *)
                  (*     case es of *)
                  (*         [] => U.ERead (x, U.ENat 0) *)
                  (*       | [e1] => U.ERead (x, e1) *)
                  (*       | _ => raise Error (r, ["for memory ref, there can't be more than one offset"]) *)
                  (*   end *)
                  | TSCell _ =>
                    let
                      val () = case es of
                                   [] => ()
                                 | _ => raise Error (r, ["for storage ref, there can't be offsets"])
                    in
                      U.EStorageGet (x, r)
                    end
                  | TNatCell _ =>
                    let
                      val () = case es of
                                   [] => ()
                                 | _ => raise Error (r, ["for storage ref, there can't be offsets"])
                    in
                      U.ENatCellGet (x, r)
                    end
                  | TVector _ =>
                    let
                      val offset = case es of
                                       [(e, [])] => e
                                     | _ => raise Error (r, ["for vector there must only be one offset"])
                    in
                      U.EVectorGet (x, offset)
                    end
                  | _ => raise Error (r, ["invalid state type"])
          in
            get_mtype ctx_st e
          end
        | U.ESet (x, es, e, r) =>
        (* | U.ESetModify (is_modify, x, es, e, r) => *)
          (* if is_modify then *)
          (*   let *)
          (*     fun check_value e = *)
          (*       if is_value e then () *)
          (*       else raise Error (r, ["must be value"]) *)
          (*     val () = app check_value es *)
          (*     val (e, n_live_vars) = U.assert_EAnnoLiveVars (fn () => raise Error (r, ["Should be EAnnoLiveVars"])) e *)
          (*     (* fun asc_time e = U.EAscTime (e, U.IUVar ((), r)) *) *)
          (*     val e = U.ESetModify (false, x, es, (* asc_time $  *)U.EApp (e, U.EAnnoLiveVars ((* asc_time $  *)U.EGet (x, es, r), n_live_vars, r)), r) *)
          (*   in *)
          (*     get_mtype ctx_st e *)
          (*   end *)
          (* else *)
          let
            val st_t = case st_types @! x of
                             SOME t => t
                          | _ => raise Error (r, [sprintf "unknown state field $" [str_st_key x]])
            val x = U.EState (x, r)
            val e =
                case st_t of
                    (* TMap _ => *)
                    (* let *)
                    (* in *)
                    (*   U.EStorageSet (foldl (fn (offset, acc) => U.EMapPtr (acc, offset)) x es, e) *)
                    (* end *)
                    TMap _ =>
                    let
                    in
                      U.EStorageSet (foldl (fn (offset, acc) => U.EMapPtrProj (acc, offset)) x es, e)
                    end
                  (* | TArray _ => *)
                  (*   let *)
                  (*     val x = U.EVar (ID (x, r), (false, false)) *)
                  (*   in *)
                  (*     case es of *)
                  (*         [] => U.EWrite (x, U.ENat 0, e) *)
                  (*       | [e1] => U.EWrite (x, e1, e) *)
                  (*       | _ => raise Error (r, ["for memory ref, there can't be more than one offset"]) *)
                  (*   end *)
                  | TSCell _ =>
                    let
                      val () = case es of
                                   [] => ()
                                 | _ => raise Error (r, ["for storage ref, there can't be offsets"])
                    in
                      U.EStorageSet (x, e)
                    end
                  | TNatCell _ =>
                    let
                      val () = case es of
                                   [] => ()
                                 | _ => raise Error (r, ["for storage ref, there can't be offsets"])
                    in
                      U.ENatCellSet (x, e)
                    end
                  | TVector _ =>
                    let
                      val offset = case es of
                                       [(a, [])] => a
                                     | _ => raise Error (r, ["for vector there must only be one offset"])
                    in
                      U.EVectorSet (x, offset, e)
                    end
                  | _ => raise Error (r, ["invalid state type"])
          in
            get_mtype ctx_st e
          end
	| U.ETriOp (ETWrite (), e1, e2, e3) =>
          let
            val r = U.get_region_e e_all
            val t = fresh_mt gctx (sctx, kctx) r
            val i1 = fresh_i gctx sctx BSTime r
            val i2 = fresh_i gctx sctx BSTime r
            val (e1, d1, st) = check_mtype (ctx, st) (e1, TArray (t, i1))
            val (e2, d2, st) = check_mtype (ctx, st) (e2, TNat (i2, r))
            val () = write_lt (i2, i1, r)
            val (e3, d3, st) = check_mtype (ctx, st) (e3, t)
          in
            (ETriOp (ETWrite (), e1, e2, e3), TUnit r, d1 %%+ d2 %%+ d3 %%+ TN C_EWrite, st)
          end
	| U.EEI (opr, e, i) =>
          (case opr of
	       EEIAppI () =>
	       let 
                 fun get_n_live_vars e =
                   let
                     val (e, _) = U.collect_EAppI e
                     val (e, _) = U.collect_EAppT e
                   in
                     snd $ U.assert_EAnnoLiveVars (fn () => raise Error (U.get_region_e e, ["Should be EAnnoLiveVars"])) e
                   end
                 val (n_live_vars, has_k) = get_n_live_vars e
                 val (e, t, d, st) = get_mtype (ctx, st) e
                 val cost = if has_k then
                              (C_Abs_BeforeCC n_live_vars + C_Abs_Inner_BeforeCC n_live_vars,
                               M_Abs_BeforeCC n_live_vars + M_Abs_Inner_BeforeCC n_live_vars)
                            else (0, 0)
                 val cost = cost ++ (C_App_BeforeCC, M_App_BeforeCC)
                 val cost = mapPair' to_real N cost
                 fun subst_i_2i v b = unop_pair (subst_i_i v) b
               in
                 case t of
                     TUniI (s, Bind ((arg_name, _), (d2, t1)), r) =>
                     let
                       val i = check_sort gctx (sctx, i, s) 
                     in
	               (EAppI (e, i), subst_i_mt i t1, d %%+ cost %%+ subst_i_2i i d2, st)
                     end
                   | _ =>
                     (* If the type is not in the expected form (maybe due to uvar), we try to unify it with the expected template. This may lose generality because the the inferred argument sort will always be a base sort. *)
	             let 
                       val r = get_region_e e
                       val s = fresh_sort gctx sctx r
                       val arg_name = "_"
                       val sctx' = add_sorting (arg_name, s) sctx
                       val t1 = fresh_mt gctx (sctx', kctx) r
                       val d2 = (fresh_i gctx sctx' BSTime r, fresh_i gctx sctx' BSNat r)
                       val t_e = TUniI (s, Bind ((arg_name, r), (d2, t1)), r)
                       (* val () = println $ "t1 = " ^ str_mt gctxn (sctx_names sctx, names kctx) t1 *)
                       (* val () = println $ "t1 = " ^ str_raw_mt t1 *)
                       (* val () = println $ "t_e = " ^ str_mt gctxn (sctx_names sctx, names kctx) t_e *)
                       (* val () = println "before" *)
                       val () = unify_mt r gctx (sctx, kctx) (t, t_e)
                       (* val () = println $ "t = " ^ str_mt gctxn (sctx_names sctx, names kctx) t *)
                       (* val () = println $ "t_e = " ^ (str_mt gctxn (sctx_names sctx, names kctx) $ normalize_mt gctx kctx t_e) *)
                       (* val () = println "after" *)
                       val i = check_sort gctx (sctx, i, s) 
                     in
	               (EAppI (e, i), subst_i_mt i t1, d %%+ cost %%+ subst_i_2i i d2, st)
	             end
               end
	     | EEIAscTime () => 
	       let val i = check_basic_sort gctx (sctx, i, BSTime)
	           val (e, t, j, st) = check_time (ctx, st) (e, i)
               in
	         (EAscTime (e, i), t, (i, j), st)
	       end
	     | EEIAscSpace () => 
	       let val i = check_basic_sort gctx (sctx, i, BSNat)
	           val (e, t, j, st) = check_space (ctx, st) (e, i)
               in
	         (EAscSpace (e, i), t, (j, i), st)
	       end
          )
	| U.EET (opr, e, t) =>
          (case opr of
	       EETAppT () => raise Impossible "get_mtype()/EAppT"
	     | EETAsc () => 
	       let
                 val t = check_kind_Type gctx (skctx, t)
	         val (e, d, st) = check_mtype (ctx, st) (e, t)
               in
	         (EAsc (e, t), t, d, st)
	       end
             | EETHalt () => 
	       let
                 val t = check_kind_Type gctx (skctx, t)
	         val (e, _, d, st) = get_mtype (ctx, st) e
               in
	         (EET (opr, e, t), t, d %%+ TN C_EHalt, StMap.empty(* st *))
	       end
          )
	| U.ET (opr, t, r) =>
          (case opr of
	       ETNever () => 
               let
	         val t = check_kind_Type gctx (skctx, t)
	         val () = write_prop (PFalse dummy, U.get_region_e e_all)
               in
	         (ENever (t, r), t, TN C_ENever, st)
               end
	     | ETBuiltin name => 
               let
	         val t = check_kind_Type gctx (skctx, t)
	         val () = if !is_builtin_enabled then ()
                          else raise Error (r, ["builtin keyword is only available in standard library"])
               in
	         (EBuiltin (name, t, r), t, TN C_EBuiltin, st)
               end
          )
        | U.ENewArrayValues (t, es, r) =>
          let
	    val t = check_kind_Type gctx (skctx, t)
            fun ignore2 (a, _, c) = (a, c)
            val (es, ds, st) = foldl (fn (e, (es, ds, st)) => let val (e, d, st) = check_mtype (ctx, st) (e, t) in (e :: es, d :: ds, st) end) ([], [], st) es
            val es = rev es
            val ds = rev ds
            val d = combine_IBAdd_Time_Nat ds
            val len = length es
          in
            (ENewArrayValues (t, es, r), TArray (t, INat (length es, r)), d %%+ (to_real $ C_ENewArrayValues len, N $ len + 1), st)
          end
	| U.ERecord (fields, r) =>
	  let
            val fields = sort cmp_str_fst $ SMap.listItemsi fields
            val (names, es) = unzip fields
            val (es, ts, ds, st) = foldl (fn (e, (es, ts, ds, st)) => let val (e, t, d, st) = get_mtype (ctx, st) e in (e :: es, t :: ts, d :: ds, st) end) ([], [], [], st) es
            val es = rev es
            val ts = rev ts
            val ds = rev ds
            val d = combine_IBAdd_Time_Nat ds
            val len = length es
          in
	    (ERecord (SMapU.fromList $ zip (names, es), r), TRecord (SMapU.fromList $ zip (names, ts), r), d %%+ (to_real $ C_ETuple len, N len), st)
	  end
	| U.EAbsI (bind, r_all) => 
	  let 
            val ((iname, s), e) = unBindAnno bind
            val (name, r) = unName iname
	    val () = if is_value e then ()
		     else raise Error (U.get_region_e e, ["The body of a universal abstraction must be a value"])
            val s = is_wf_sort gctx (sctx, s)
            val ctxd = ctx_from_sorting (name, s)
            val ctx = add_ctx ctxd ctx
            val () = open_ctx ctxd
	    val (e, t, d, _) = get_mtype (ctx, StMap.empty) e
            val () = close_ctx ctxd
            val (is_rec, e) = is_rec_body e
            val excluded = if is_rec then [0] else [] (* argument and (optionally) self-reference are not free evars *)
            val n_fvars = EVarSet.numItems $ EVarSet.difference (FreeEVars.free_evars e, EVarSetU.fromList $ map inl excluded)
            val () = println $ "EAbsI/n_fvars = " ^ str_int n_fvars
            val tail_app_cost = if is_tail_call e then (0, 0)
                                else (C_App_BeforeCC, M_App_BeforeCC)
            val extra_inner_cost = (C_AbsI_Inner_BeforeCPS n_fvars, M_AbsI_Inner_BeforeCPS n_fvars) ++ tail_app_cost
            val () = println $ "EAbsI/d = " ^ (ToString.str_i Gctx.empty [] $ Simp.simp_i $ fst d)
            val () = println $ "EAbsI/extra_inner_cost = " ^ str_int (fst extra_inner_cost)
            val d = d %%+ mapPair' to_real N extra_inner_cost
            val cost = mapPair' to_real N (C_Abs_BeforeCC n_fvars, M_Abs_BeforeCC n_fvars)
          in
	    (EAbsI (BindAnno ((iname, s), e), r_all), TUniI (s, Bind ((name, r), (d, t)), r_all), cost, st)
	  end
	| U.ELet (return, bind, r) => 
	  let
            val (decls, e) = Unbound.unBind bind
            val decls = unTeles decls
            val return = is_wf_return gctx (skctx, return)
            val (decls, ctxd as (sctxd, kctxd, _, _), nps, ds, ctx, st) = check_decls (ctx, st) decls
	    val (e, t, d, st) = get_mtype (ctx, st) e
            val ds = rev (d :: ds)
            val d = combine_IBAdd_Time_Nat ds
            (* val d = foldl' (fn (d, acc) => acc %+ d) (T0 dummy) ds *)
	    (* val t = forget_ctx_mt r ctx ctxd t  *)
            (* val ds = map (forget_ctx_d r ctx ctxd) ds *)
	    val (t, d) = forget_or_check_return (get_region_e e) gctx (#1 ctx, #2 ctx) ctxd (t, d) return 
            val st = StMap.map (forget_ctx_d r gctx (#1 ctx) (#1 ctxd)) st
            val () = close_n nps
            val () = close_ctx ctxd
            val e = EAsc (e, shift_ctx_mt ctxd t)
          in
	    (ELet ((SOME t, SOME $ fst d, SOME $ snd d), Unbound.Bind (Teles decls, e), r), t, d, st)
	  end
        (* | U.ECaseSumbool (e, bind1, bind2, r) => *)
        (*   let *)
        (*     val s1 = fresh_sort gctx sctx r *)
        (*     val s2 = fresh_sort gctx sctx r *)
        (*     val (e, j_e, st) = check_mtype (ctx, st) (e, TSumbool (s1, s2)) *)
        (*     val (iname1, e1) = unBindSimpName bind1 *)
        (*     val (iname2, e2) = unBindSimpName bind2 *)
        (*     val (e1, t1, j1, st1) = open_close add_sorting_skcts (fst iname1, s1) (ctx, st) (fn ctx_st => get_mtype ctx_st e1) *)
        (*     val ctxd = ctx_from_sorting (fst iname1, s1) *)
        (*     val skctx' = add_sorting_sk (fst iname1, s1) (#1 ctx, #2 ctx) *)
        (*     val (t1, j1) = forget_or_check_return r gctx skctx' ctxd (t1, j1) (NONE, NONE, NONE) *)
        (*     val st1 = StMap.map (forget_ctx_d r gctx (#1 skctx') (#1 ctxd)) st1 *)
        (*     val (e2, t2, j2, st2) = open_close add_sorting_skcts (fst iname2, s2) (ctx, st) (fn ctx_st => get_mtype ctx_st e2) *)
        (*     val ctxd = ctx_from_sorting (fst iname2, s2) *)
        (*     val skctx' = add_sorting_sk (fst iname2, s2) (#1 ctx, #2 ctx) *)
        (*     val (t2, j2) = forget_or_check_return r gctx skctx' ctxd (t2, j2) (NONE, NONE, NONE) *)
        (*     val st2 = StMap.map (forget_ctx_d r gctx (#1 skctx') (#1 ctxd)) st2 *)
        (*     val () = unify_mt r gctx (sctx, kctx) (t2, t1) *)
        (*     val () = unify_state r gctxn sctxn (st2, st1) *)
        (*   in *)
        (*     (ECaseSumbool (e, IBind (iname1, e1), IBind (iname2, e2), r), t1, j_e %%+ smart_max_pair j1 j2, st1) *)
        (*   end *)
	| U.EAppConstr ((x, (eia, _)), ts, is, e, ot) => 
	  let
            val () = assert (fn () => null ts) "get_mtype()/EAppConstr: null ts"
            val () = assert (fn () => isNone ot) "get_mtype()/EAppConstr: isNone ot"
            val tc = fetch_constr_type gctx (cctx, x)
	    (* delegate to checking [x {is} e] *)
            val r = U.get_region_long_id x
	    val f = U.EAnnoLiveVars (U.EVar ((ID (0, r)), (eia, true)), (0, true), r)
	    val f = foldl (fn (i, e) => U.EAppI (e, i)) f is
	    val e = U.EApp (U.EAnnoConstr (f, r), UShift.shift_e_e $ U.EAnnoLiveVars (e, (0, true), r))
            val f_name = str_var #3 (gctx_names gctx) (names cctx) x
	    val (e, t, d, st) = get_mtype (add_typing_skct (f_name, tc) ctx, st) e 
            val d = update_2i d
            val d = simp_2i d
            val (ts, is, e) =
                case e of
                    EBinOp (EBApp (), f, e) =>
                    let
                      val (f, is) = collect_EAppI f
                      val (f, ts) = collect_EAppT f
                      val () = case f of
                                   EVar (_, (true, false)) => ()
                                 | _ => raise Impossible "get_mtype()/EAppConstr: EVar (_, (true, false))"
                    in
                      (ts, is, e)
                    end
                  | _ => raise Impossible "get_mtype (): U.EAppConstr: e in wrong form"
            val e = ExprShift.forget_e_e 0 1 e
            val siblings = get_family_siblings gctx cctx x
            val pos_in_family = indexOf (curry eq_var x) (map fst siblings) !! (fn () => raise Impossible "get_mtype(): family_pos")
            val family = get_family $ snd $ hd siblings
            val family_type = TVar family
            (* now [length is] is the number of [packI]'s *)
            val len_is = length is
            fun get_num_inj (len, n) = 
              if len <= 0 then raise Impossible "get_num_inj(): len=0"
              else if len = 1 then (assert (fn () => n = 0) "get_num_inj(): n = 0"; 0)
              else
                if n <= 0 then 1
                else 1 + get_num_inj (len-1, n-1)
            val num_inj = get_num_inj (length siblings, pos_in_family)
            val cost = d %%+ mapPair' to_real N ((len_is + 1) * C_EPack + num_inj * C_EInj + C_EFold, num_inj * M_Inj)
	  in
	    (EAppConstr ((x, (true, false)), ts, is, e, SOME (pos_in_family, family_type)), t, cost, st)
	  end
	| U.ECase (e, return, rules, r) => 
	  let
            val rules = map Unbound.unBind rules
            val return = if !anno_less then (#1 return, NONE, NONE) else return
            val (e, t1, d1, st) = get_mtype (ctx, st) e
            val (e, (n_live_vars, has_k)) = assert_EAnnoLiveVars (fn () => raise Error (r, ["Should be EAnnoLiveVars"])) e
            val return = is_wf_return gctx (skctx, return)
            val rules = expand_rules gctx ((sctx, kctx, cctx), rules, t1, r)
            val (rules, t_d_sts) = unzip $ check_rules (ctx, st) (rules, (t1, return), r)
            val (ts, ds, sts) = unzip3 t_d_sts
            fun computed_t () : mtype =
              case ts of
                  [] => raise Error (r, ["Empty case-matching must have a return type clause"])
                | t :: ts => 
                  (map (fn t' => unify_mt r gctx (sctx, kctx) (t, t')) ts; 
                   t)
            val (times, spaces) = unzip ds
            fun computed_time () =
              smart_max_list times
            fun computed_space () =
              smart_max_list spaces
            (* val (t, time, space) = (lazy_default computed_t $ #1 return, computed_time (), computed_space ()) *)
            val (t, time, space) = map_triple (lazy_default computed_t, lazy_default computed_time, lazy_default computed_space) return
            fun unify_states sts =
              case sts of
                  [] => NONE
                | st :: ls => (app (fn st' => unify_state r gctxn sctxn (st', st)) ls; SOME st)
            val st = default st $ unify_states sts
            val len = length rules
            val cost = if len >= 2 andalso has_k then
                         (C_Abs_BeforeCC n_live_vars + C_Abs_Inner_BeforeCC n_live_vars,
                          M_Abs_BeforeCC n_live_vars + M_Abs_Inner_BeforeCC n_live_vars)
                       else (0, 0)
            val d = d1 %%+ mapPair' to_real N cost %%+ (time, space)
            (* val () = println $ "ECase: d1 = " ^ str_i gctxn sctxn (fst d1) *)
            (* val () = println $ "ECase: cost = " ^ str_int (fst cost) *)
            (* val () = println $ "ECase: d = " ^ str_i gctxn sctxn (fst d) *)
          in
            (ECase (e, return, map Unbound.Bind rules, r), t, d, st)
          end
        | U.EIfi (e, bind1, bind2, r) =>
          let
            val i = fresh_i gctx sctx BSBool r
            val (e, j_e, st) = check_mtype (ctx, st) (e, TiBool (i, r))
            val (iname1, e1) = unBindSimpName bind1
            val (iname2, e2) = unBindSimpName bind2
            val s1 = SSubset_from_prop r $ i %= ITrue r
            val s2 = SSubset_from_prop r $ i %= IFalse r
            val (e1, t1, j1, st1) = open_close add_sorting_skcts (fst iname1, s1) (ctx, st) (fn ctx_st => get_mtype ctx_st e1)
            val ctxd = ctx_from_sorting (fst iname1, s1)
            val skctx' = add_sorting_sk (fst iname1, s1) (#1 ctx, #2 ctx)
            val (t1, j1) = forget_or_check_return r gctx skctx' ctxd (t1, j1) (NONE, NONE, NONE)
            val st1 = StMap.map (forget_ctx_d r gctx (#1 skctx') (#1 ctxd)) st1
            val (e2, t2, j2, st2) = open_close add_sorting_skcts (fst iname2, s2) (ctx, st) (fn ctx_st => get_mtype ctx_st e2)
            val ctxd = ctx_from_sorting (fst iname2, s2)
            val skctx' = add_sorting_sk (fst iname2, s2) (#1 ctx, #2 ctx)
            val (t2, j2) = forget_or_check_return r gctx skctx' ctxd (t2, j2) (NONE, NONE, NONE)
            val st2 = StMap.map (forget_ctx_d r gctx (#1 skctx') (#1 ctxd)) st2
            val () = unify_mt r gctx (sctx, kctx) (t2, t1)
            val () = unify_state r gctxn sctxn (st2, st1)
            val (e2, (n_live_vars, has_k)) = assert_EAnnoLiveVars (fn () => raise Error (get_region_e e2, ["Should be EAnnoLiveVars"])) e2
            val cost = if has_k then
                         (C_Abs_BeforeCC n_live_vars + C_Abs_Inner_BeforeCC n_live_vars,
                          M_Abs_BeforeCC n_live_vars + M_Abs_Inner_BeforeCC n_live_vars)
                       else (0, 0)
            val cost = mapFst (add C_Ifi_BeforeCodeGen) cost
            val cost = mapFst (add C_EUnpack) cost
            val branch_extra = (C_App_BeforeCC, M_App_BeforeCC)
            val branch1_extra = if is_tail_call e1 then (0, 0) else branch_extra
            val branch2_extra = if is_tail_call e2 then (0, 0) else branch_extra
          in
            (EIfi (e, IBind (iname1, e1), IBind (iname2, e2), r), t1, j_e %%+ mapPair' to_real N cost %%+ smart_max_pair (j1 %%+ mapPair' to_real N branch1_extra) (TN C_JUMPDEST %%+ j2 %%+ mapPair' to_real N branch2_extra), st1)
          end
	| U.ETriOp (ETIte (), e, e1, e2) =>
          let
            val r = U.get_region_e e_all
            val (e, d, st) = check_mtype (ctx, st) (e, TBool r)
            val (e1, t, d1, st1) = get_mtype (ctx, st) e1
            val (e2, d2, st2) = check_mtype (ctx, st) (e2, t)
            val () = unify_state r gctxn sctxn (st2, st1)
            val (e2, (n_live_vars, has_k)) = assert_EAnnoLiveVars (fn () => raise Error (get_region_e e2, ["Should be EAnnoLiveVars"])) e2
            val cost = if has_k then
                         (C_Abs_BeforeCC n_live_vars + C_Abs_Inner_BeforeCC n_live_vars,
                          M_Abs_BeforeCC n_live_vars + M_Abs_Inner_BeforeCC n_live_vars)
                       else (0, 0)
            val cost = mapFst (add C_Ite_BeforeCodeGen) cost
            val branch_extra = (C_App_BeforeCC, M_App_BeforeCC)
            val branch1_extra = if is_tail_call e1 then (0, 0) else branch_extra
            val branch2_extra = if is_tail_call e2 then (0, 0) else branch_extra
          in
            (ETriOp (ETIte (), e, e1, e2), t, d %%+ mapPair' to_real N cost %%+ smart_max_pair (d1 %%+ mapPair' to_real N branch1_extra) (TN C_JUMPDEST %%+ d2 %%+ mapPair' to_real N branch2_extra), st1)
          end
	| U.EAbs (pre_st, bind, d_spec) => 
	  let
            val pre_st = is_wf_state gctx sctx pre_st
            val d_spec = Option.map (check_Time_Nat gctx (#1 ctx)) d_spec
            val (pn, e) = Unbound.unBind bind
            val r = U.get_region_pn pn
            val t = fresh_mt gctx (sctx, kctx) r
            val skcctx = (sctx, kctx, cctx) 
            val (pn, cover, ctxd, nps (* number of premises *)) = match_ptrn gctx (skcctx, pn, t)
	    val () = check_exhaustion gctx (skcctx, t, [cover], get_region_pn pn)
            val (ctx, pre_st) = add_ctx_ctxst ctxd (ctx, pre_st)
            val (is_rec, e) = U.is_rec_body e
	    val (e, t1, d, post_st) = get_mtype (ctx, pre_st) e
            val r = get_region_e e
	    val t1 = forget_ctx_mt r gctx (#1 ctx, #2 ctx) ctxd t1 
            val d = forget_ctx_2i r gctx (#1 ctx) (#1 ctxd) d
            val post_st = StMap.map (forget_ctx_d r gctx (#1 ctx) (#1 ctxd)) post_st
            val () = close_n nps
            val () = close_ctx ctxd
            val len_pn_ebinds = length $ snd $ PatternVisitor.collect_binder_pn pn
            val excluded = (if is_rec then [len_pn_ebinds] else []) @ list_of_range (0, len_pn_ebinds) (* argument and (optionally) self-reference are not free evars *)
            val n_fvars = EVarSet.numItems $ EVarSet.difference (FreeEVars.free_evars e, EVarSetU.fromList $ map inl excluded)
            val () = println $ "EAbs/is_rec = " ^ str_bool is_rec
            val () = println $ "EAbs/n_fvars = " ^ str_int n_fvars
            val d = mapPair' to_real N (hd $ get_rules_cost_adjustments snd [(pn, is_tail_call e)]) %%+ d
            val extra_inner_cost = (C_Abs_Inner_BeforeCPS n_fvars, M_Abs_Inner_BeforeCPS n_fvars)
            val d = mapPair' to_real N extra_inner_cost %%+ d
            val tail_app_cost = if is_tail_call e then (0, 0)
                                else (C_App_BeforeCC, M_App_BeforeCC)
            val d = d %%+ mapPair' to_real N tail_app_cost
            val d = case d_spec of
                        SOME d_spec => (smart_write_le_2i gctx (#1 ctx) r (d, d_spec); d_spec)
                      | NONE => d
            val outer_cost = mapPair' to_real N (C_Abs_BeforeCC n_fvars, M_Abs_BeforeCC n_fvars)
          in
	    (EAbs (pre_st, Unbound.Bind (PnAnno (pn, Outer t), e), d_spec), TArrow ((pre_st, t), d, (post_st, t1)), outer_cost, st)
	  end
    fun extra_msg () = ["when typechecking"] @ indent [US.str_e gctxn ctxn e_all]
    val (e, t, d, st) = main ()
    handle
    Error (r, msg) => raise Error (r, msg @ extra_msg ())
    | Impossible msg => raise Impossible $ join_lines $ msg :: extra_msg ()
    val t = SimpType.simp_mt $ normalize_mt true gctx kctx t
    val d = simp_2i $ unop_pair normalize_i d
    (* val () = println $ str_ls id $ #4 ctxn *)
    (* val () = println $ " Typed: " ^ str_e gctxn ctxn e *)
    (* val () = println $ "  Time: " ^ str_i gctxn sctxn (fst d) *)
    (* val () = println $ "  Type: " ^ str_mt gctxn skctxn t *)
    (* val () = print (sprintf " Typed $: \n        $\n" [str_e gctxn ctxn e, str_mt gctxn skctxn t]) *)
    (* val () = print (sprintf "  type: $ [for $]\n  time: $\n" [str_mt gctxn skctxn t, str_e gctxn ctxn e, str_i gctxn sctxn d]) *)
  in
    (e, t, d, st)
  end

and check_rules gctx (ctx as (sctx, kctx, cctx, tctx), st) (rules, t as (t1, return), r) =
    let 
      fun get_inj (cx, _) =
        let
          val c as (family, tbinds) = snd $ fetch_constr gctx (cctx, cx)
          val siblings = map fst $ get_family_siblings gctx cctx cx
          val pos_in_family = indexOf (curry eq_var cx) siblings !! (fn () => raise Impossible "get_inj()/family_pos")
        in
          (length siblings, pos_in_family)
        end
      val ds = get_rules_cost_adjustments get_inj $ map (mapSnd U.is_tail_call) rules
      val skcctx = (sctx, kctx, cctx)
      fun f ((rule, adjust), acc) =
	let
          (* val previous_covers = map (snd o snd) $ rev acc *)
          val ans as (rule, tdst, cover) = check_rule gctx (ctx, st) ((* previous_covers, *) rule, t, adjust)
          (* val covers = rev $ map (snd o snd) acc *)
	  (* val () = check_redundancy (skcctx, t1, covers, cover, get_region_rule rule) *)
	in
	  ans :: acc
	end 
      val (rules_tdsts, covers) = unzip $ map (fn (a, b, c) => ((a, b), c)) $ rev $ foldl f [] $ zip (rules, ds)
      (* val () = check_exhaustion (skcctx, t1, covers, r) *)
    in
      rules_tdsts
    end

and check_rule gctx (ctx as (sctx, kctx, cctx, tctx), st) ((* pcovers, *) (pn, e), t as (t1, return), adjust) =
    let 
      val skcctx = (sctx, kctx, cctx) 
      val (pn, cover, ctxd as (sctxd, kctxd, _, _), nps) = match_ptrn gctx (skcctx, (* pcovers, *) pn, t1)
      val ctx0 = ctx
      val (ctx, st) = add_ctx_ctxst ctxd (ctx, st)
      val (e, t, d, st) = get_mtype gctx (ctx, st) e
      val r = get_region_e e
      val d = mapPair' to_real N adjust %%+ d
      val (t, d) = forget_or_check_return r gctx (#1 ctx, #2 ctx) ctxd (t, d) return 
      val st = StMap.map (forget_ctx_d r gctx (#1 ctx) (#1 ctxd)) st
      val () = close_n nps
      val () = close_ctx ctxd
      val e = e %: shift_ctx_mt ctxd t |># (shift_ctx_2i ctxd d %%- mapPair' to_real N adjust)
    in
      ((pn, e), (t, d, st), cover)
    end

and check_decl gctx (ctx as (sctx, kctx, cctx, _), st) decl =
    let
      val check_decl = check_decl gctx
      val check_decls = check_decls gctx
      val get_mtype = get_mtype gctx
      val check_mtype_time = check_mtype_time gctx
      val tail_app_cost = (C_App_BeforeCC, M_App_BeforeCC)
      fun get_tname_times n_fvars is_tail_call i_e len = 
        let
          val extra = mapPair' to_real N (C_AbsI_Inner_BeforeCPS n_fvars, M_AbsI_Inner_BeforeCPS n_fvars)
          val cost = mapPair' to_real N (C_Abs_BeforeCC n_fvars, M_Abs_BeforeCC n_fvars)
          (*  cost  ...  cost  i_e
                   extra ... extra              
           *)
          val times = int_mapi (fn n => if n = len - 1 then i_e else cost) len
          val times = mapi (fn (n, i) => i %%+ extra %%+ mapPair' to_real N (if n = len - 1 andalso is_tail_call then (0, 0) else tail_app_cost)) times
          val i_e = if len = 0 then i_e else cost
        in
          (times, i_e)
        end
      fun check_tname_times r sctxn n_fvars is_tail_call i_e names = 
        let
          val extra = mapPair' to_real N (C_AbsI_Inner_BeforeCPS n_fvars, M_AbsI_Inner_BeforeCPS n_fvars)
          val cost = mapPair' to_real N (C_Abs_BeforeCC n_fvars, M_Abs_BeforeCC n_fvars)
          val (times, i_e) = get_tname_times n_fvars is_tail_call i_e $ length names
          val gctxn = gctx_names gctx
          fun unify_2i a = ignore $ binop_pair (unify_i r gctxn sctxn) a
          val () = app2 unify_2i (map snd names, times)
        in
          i_e
        end
      fun generalize n_fvars is_tail_call i_e t = 
        let
          fun collect_uvar_t_ctx (_, _, cctx, tctx) =
            (* cctx can't contain uvars *)
            (concatMap collect_uvar_t_c o map snd) cctx @
            (concatMap collect_uvar_t_t o map snd) tctx 
          fun generalized_uvar_name n =
            if n < 26 then
              "'_" ^ (str o chr) (ord #"a" + n)
            else
              "'_" ^ str_int n
          val t = update_mt t
          val free_uvars = dedup op= $ diff op= (map #1 $ collect_uvar_t_mt t) (map #1 $ collect_uvar_t_ctx ctx)
          val t = shiftx_t_mt 0 (length free_uvars) t
          val t = foldli (fn (v, uvar_ref, t) => SubstUVar.substu_t_mt uvar_ref v t) t free_uvars
          val free_uvar_names = map (attach_snd dummy) $ Range.map generalized_uvar_name (0, (length free_uvars))
          val (times, i_e) = get_tname_times n_fvars is_tail_call i_e $ length free_uvar_names
          val free_uvar_names = zip (free_uvar_names, times)
          val poly_t = PTUni_Many (free_uvar_names, PTMono t, dummy)
        in
          (t, poly_t, free_uvars, free_uvar_names, i_e)
        end
      (* fun generalize_e free_uvars e =  *)
      (*   let *)
      (*     val e = foldli (fn (v, uvar_ref, e) => substu_e uvar_ref v t) e free_uvars *)
      (*     (* val e = Range.for (fn (i, t) => (EAbsT (TBind ((generalized_uvar_name i, dummy), t), dummy))) e (0, (length free_uvars)) *) *)
      (*   in *)
      (*     e *)
      (*   end *)
      (* val () = println $ sprintf "Typing Decl $" [fst $ U.str_decl (gctx_names gctx) (ctx_names ctx) decl] *)
      fun main () = 
        case decl of
            U.DVal (ename, Outer bind, r) =>
            let
              val name = binder2str ename
              (* val () = println $ "DVal " ^ name *)
              val (tnames, e) = Unbound.unBind bind
              val tnames = map (mapPair' unBinderName unOuter) tnames
              val tnames = map (mapSnd $ check_Time_Nat gctx sctx) tnames
              val is_value = is_value e
              val (e, t, d, st) = get_mtype (add_kindings_skct (zip (rev $ map (fst o fst) tnames, repeat (length tnames) Type)) ctx, st) e
              val is_tail_call = is_tail_call e
              fun ty2mtype t = snd $ collect_PTUni t
            in
              if is_value then 
                let
                  val n_fvars = EVarSet.numItems $ FreeEVars.free_evars e
                  val sctxn = sctx_names sctx
                  val (t, poly_t, free_uvars, free_uvar_names, d) = generalize n_fvars is_tail_call d t
                  val e = UpdateExpr.update_e e
                  val e = ExprShift.shiftx_t_e 0 (length free_uvars) e
                  val e = foldli (fn (v, uvar_ref, e) => SubstUVar.substu_t_e uvar_ref v e) e free_uvars
                  val d = check_tname_times r sctxn n_fvars is_tail_call d tnames
                  val poly_t = PTUni_Many (tnames, poly_t, r)
                  val tnames = tnames @ free_uvar_names
                in
                  (DVal (ename, Outer $ Unbound.Bind (map (mapPair' (Binder o TName) Outer) tnames, EAsc (e, ty2mtype poly_t)), r), ctx_from_typing (name, poly_t), 0, [d], st)
                end
              else if length tnames = 0 then
                (DVal (ename, Outer $ Unbound.Bind ([], EAsc (e, t)), r), ctx_from_typing (name, PTMono t), 0, [d], st)
              else
                raise Error (r, ["explicit type variable cannot be generalized because of value restriction"])
            end
          | U.DValPtrn (pn, Outer e, r) =>
            let 
              val skcctx = (sctx, kctx, cctx) 
              val (e, t, d, st) = get_mtype (ctx, st) e
              val (pn, cover, ctxd, nps) = match_ptrn gctx (skcctx, pn, t)
              val extra = hd $ get_rules_cost_adjustments snd [(pn, false)]
              val d = d %%+ mapPair' to_real N extra
              val d = shift_ctx_2i ctxd d
              val st = StMap.map (shift_ctx_i ctxd) st
	      val () = check_exhaustion gctx (skcctx, t, [cover], get_region_pn pn)
            in
              (DValPtrn (pn, Outer e, r), ctxd, nps, [d], st)
            end
	  | U.DRec (name, bind, r) =>
            (* a version that delegates most of the work to EAbs and EAbsI *)
	    let
              val () = println "before DRec"
              val (name, r1) = unBinderName name
              val ((tnames, Rebind binds), ((pre_st, post_st), (t, d), e)) = Unbound.unBind $ unInner bind
              val tnames = map (mapPair' unBinderName unOuter) tnames
              val tnames = map (mapSnd $ check_Time_Nat gctx sctx) tnames
              val binds = unTeles binds
              val ctx as (sctx, kctx, cctx, tctx) = add_kindings_skct (zip (rev $ map (fst o fst) tnames, repeat (length tnames) Type)) ctx
              fun attach_bind_e (bind, e) =
                case bind of
                    U.SortingST (name, Outer s) => U.MakeEAbsI (unBinderName name, s, e, r)
                  | U.TypingST pn => U.MakeEAbs (StMap.empty, pn, e)
              val len_binds = length binds
              val e = foldri (fn (n, bind, e) =>
                                 let
                                   val e = if n = len_binds - 1 then
                                             let
                                               val e = U.EAnnoBodyOfRecur (e, r)
                                             in
                                               e
                                             end
                                           else e
                                 in
                                   if n = 0 then
                                     (case bind of
                                          U.TypingST pn => U.MakeEAbsWithAnno (pre_st, pn, e, SOME d)
                                        | _ => raise Error (r, ["Recursion must have a typing bind as the last bind"]))
                                   else attach_bind_e (bind, e)
                                 end
                             ) e binds
              (* val e = *)
              (*     case rev binds of *)
              (*         U.TypingST pn :: binds => *)
              (*         foldl attach_bind_e (U.MakeEAbs (pre_st, pn, e)) binds *)
              (*       | _ => raise Error (r, ["Recursion must have a typing bind as the last bind"]) *)
              fun type_from_ptrn pn =
                case pn of
                    U.PnAnno (_, Outer t) => t
                  | U.PnAlias (_, pn, _) => type_from_ptrn pn
                  | U.PnTT _ => U.TUnit r
                  | U.PnPair (pn1, pn2) => U.TProd (type_from_ptrn pn1, type_from_ptrn pn2) 
                  | U.PnVar _ => U.TUVar ((), r)
                  | U.PnConstr _ => U.TUVar ((), r) (* todo: pn mustn't introduce index vars *)
              val IUnderscore2 = (U.IUVar ((), r), U.IUVar ((), r))
              fun attach_bind_t (bind, t) =
                case bind of
	            U.SortingST (name, Outer s) => U.TUniI (s, Bind (unBinderName name, (IUnderscore2, t)), r)
	          | U.TypingST pn => U.TArrow ((StMap.empty, type_from_ptrn pn), IUnderscore2, (StMap.empty, t))
              val te =
                  case rev binds of
                      U.TypingST pn :: binds =>
                      foldl attach_bind_t (U.TArrow ((pre_st, type_from_ptrn pn), d, (post_st, t))) binds
                    | _ => raise Error (r, ["Recursion must have a typing bind as the last bind"])
              (* val () = println $ sprintf "te[pre] = $" [US.str_mt (gctx_names gctx) (sctx_names sctx, names kctx) te] *)
	      val te = check_kind_Type gctx ((sctx, kctx), te)
              (* val () = println $ sprintf "te[post] = $" [str_mt (gctx_names gctx) (sctx_names sctx, names kctx) te] *)
              val () = println "before check_mtype"
	      val (e, i, st) = check_mtype gctx (add_typing_skct (name, PTMono te) ctx, st) (e, te) 
              val () = println "after check_mtype"
              val n_fvars = EVarSet.numItems $ EVarSetU.delete (FreeEVars.free_evars e, inl 0)
              val sctxn = sctx_names sctx
              val is_tail_call = is_tail_call e
              val (te, poly_te, free_uvars, free_uvar_names, i) = generalize n_fvars is_tail_call i te
              val e = UpdateExpr.update_e e
              val e = ExprShift.shiftx_t_e 0 (length free_uvars) e
              val e = foldli (fn (v, uvar_ref, e) => SubstUVar.substu_t_e uvar_ref v e) e free_uvars
              val () = println "before check_tname_times"
              val i = check_tname_times r sctxn n_fvars is_tail_call i tnames
              val () = println "after check_tname_times"
              val poly_te = PTUni_Many (tnames, poly_te, r)
              val tnames = tnames @ free_uvar_names
              val decl = DRec (Binder $ EName (name, r1), Inner $ Unbound.Bind ((map (mapPair' (Binder o TName) Outer) tnames, Rebind TeleNil), ((StMap.empty, StMap.empty), (te, TN0 r), e)), r)
              val () = println "after DRec"
            in
              (decl, ctx_from_typing (name, poly_te), 0, [i], st)
	    end
          | U.DIdxDef (name, Outer s, Outer i) =>
            let
              val (name, r) = unBinderName name
              val s = s !! (fn () => raise Impossible "typecheck/DIdxDef: s must be SOME")
              val s = is_wf_sort gctx (sctx, s)
              val i = check_sort gctx (sctx, i, s)
              val s = sort_add_idx_eq r s i
              val st = StMap.map shift_i_i st
              val ctxd = ctx_from_sorting (name, s)
              val () = open_ctx ctxd
                                (* val ps = [PBinPred (EqP, IVar (NONE, (0, r)), shift_ctx_i ctxd i)] *)
                                (* val () = open_premises ps *)
            in
              (DIdxDef (Binder $ IName (name, r), Outer $ SOME s, Outer i), ctxd, 0, [], st)
            end
          | U.DAbsIdx2 (name, Outer s, Outer i) =>
            let
              val (name, r) = unBinderName name
              val s = is_wf_sort gctx (sctx, s)
              val i = check_sort gctx (sctx, i, s)
              val st = StMap.map shift_i_i st
              val ctxd = ctx_from_sorting (name, s)
              val () = open_ctx ctxd
              val ps = [PBinPred (BPEq (), IVar (ID (0, r), []), shift_ctx_i ctxd i)]
              val () = open_premises ps
            in
              (DAbsIdx2 (Binder $ IName (name, r), Outer s, Outer i), ctxd, length ps, [], st)
            end
          | U.DTypeDef (name, Outer t) =>
            (case t of
                 U.TDatatype (dt, r) =>
                 let
                   val (dt, ctxd) = is_wf_datatype gctx ctx (dt, r)
                 in
                   (DTypeDef (name, Outer $ TDatatype (dt, r)), ctxd, 0, [], st)
                 end
               | _ =>
                 let
                   val (name, r) = unBinderName name
                   val (t, k) = get_kind gctx ((sctx, kctx), t)
                   val kinding = (name, KeTypeEq (k, t))
                 in
                   (DTypeDef (Binder $ TName (name, r), Outer t), ctx_from_kindingext kinding, 0, [], st)
                 end
            )
          | U.DAbsIdx ((name, Outer s, Outer i), Rebind decls, r) =>
            let
              val (name, r1) = unBinderName name
              val decls = unTeles decls
              val s = is_wf_sort gctx (sctx, s)
              (* localized the scope of the evars introduced in type-checking absidx's definition *)
              val () = open_paren ()
              val i = check_sort gctx (sctx, i, s)
              (* val () = println $ sprintf "sort and value of absidx $: \n$\n$" [name, str_s (gctx_names gctx) (sctx_names sctx) s, str_i (gctx_names gctx) (sctx_names sctx) i] *)
              val st = StMap.map shift_i_i st
              val ctxd = ctx_from_sorting (name, s)
              val () = open_ctx ctxd
              val ps = [PBinPred (BPEq (), IVar (ID (0, r), []), shift_ctx_i ctxd i)]
              val () = open_premises ps
              val (decls, ctxd2, nps, ds, _, st) = check_decls (add_ctx ctxd ctx, st) decls
              val () = if nps = 0 then ()
                       else raise Error (r, ["Can't have premise-generating pattern in abstype"])
              (* close and reopen *)
              val () = close_ctx ctxd2
              val () = close_n (length ps)
              val () = close_ctx ctxd
              val () = close_paren ()
              val ctxd = add_ctx ctxd2 ctxd
              val () = open_ctx ctxd
              val decl = DAbsIdx ((Binder $ IName (name, r1), Outer s, Outer i), Rebind $ Teles decls, r)
            in
              (decl, ctxd, 0, ds, st)
            end
          | U.DOpen (m, octx) =>
            let
              val (m, r) = unInner m
              fun link_module (m, r) (sctx, kctx, cctx, tctx) =
                let
                  fun sort_set_idx_eq s' i =
                    set_prop r s' (IVar (ID (0, r), []) %= shift_i_i i)
                  val sctx = mapWithIdx (fn (i, (name, s)) => (name, sort_set_idx_eq s $ IVar (QID ((m, r), (i, r)), []))) sctx
                  fun kind_set_type_eq (k, _) t = (k, SOME t)
                  val kctx = mapWithIdx (fn (i, (name, k)) => (name, kind_set_type_eq k $ TVar $ QID ((m, r), (i, r)))) kctx
                in
                  (sctx, kctx, cctx, tctx)
                end
              fun clone_module gctx (m, r) =
                let
                  val ctx = fetch_module gctx (m, r)
                  (* val ctxd = package_ctx (m, r) ctxd  *)
                  val ctx = link_module (m, r) ctx
                in
                  ctx
                end
              val ctxd = clone_module gctx (m, r)
              val st = StMap.map (shift_ctx_i ctxd) st
              val () = open_ctx ctxd
            in
              (DOpen (Inner (m, r), octx), ctxd, 0, [], st)
            end
          | U.DConstrDef _ => raise Impossible "typecheck/DConstrDef"
      fun extra_msg () = ["when type-checking declaration "] @ indent [fst $ US.str_decl (gctx_names gctx) (ctx_names ctx) decl]
      val ret as (decl, ctxd, nps, ds, st) =
          main ()
          handle
          Error (r, msg) => raise Error (r, msg @ extra_msg ())
          | Impossible msg => raise Impossible $ join_lines $ msg :: extra_msg ()
               (* val () = println $ sprintf " Typed Decl $ " [fst $ str_decl (gctx_names gctx) (ctx_names ctx) decl] *)
	       (* val () = print $ sprintf "   Time : $: \n" [str_i sctxn d] *)
    in
      ret
    end

and check_mtype gctx (ctx_st as (ctx as (sctx, kctx, cctx, tctx), st)) (e, t) =
    let
      val (e, t', d, st) = get_mtype gctx ctx_st e
      fun extra_msg () =
        let
          val ctxn as (sctxn, kctxn, cctxn, tctxn) = ctx_names ctx
          val gctxn = gctx_names gctx
        in
          ["when comparing type"] @ indent [str_mt gctxn (sctxn, kctxn) t'] @ ["against"] @ indent [str_mt gctxn (sctxn, kctxn) t] @ ["for expr"] @ indent [str_e gctxn ctxn e]
        end
      val () = unify_mt (get_region_e e) gctx (sctx, kctx) (t', t)
               handle
               Error (r, msg) => raise Error (r, msg @ extra_msg ())
               | Impossible msg => raise Impossible $ join_lines $ msg :: extra_msg ()
                        (* val () = println "check type" *)
                        (* val () = println $ str_region "" "ilist.timl" $ get_region_e e *)
    in
      (e, d, st)
    end

and check_time gctx (ctx_st as (ctx as (sctx, kctx, cctx, tctx), st)) (e, d) =
    let 
      val (e, t, (d', j), st) = get_mtype gctx ctx_st e
      val () = smart_write_le (gctx_names gctx) (names sctx) (d', d, get_region_e e)
    in
      (e, t, j, st)
    end

and check_space gctx (ctx_st as (ctx as (sctx, kctx, cctx, tctx), st)) (e, i) =
    let 
      val (e, t, (j, i'), st) = get_mtype gctx ctx_st e
      val () = smart_write_le (gctx_names gctx) (names sctx) (i', i, get_region_e e)
    in
      (e, t, j, st)
    end

and check_mtype_time gctx (ctx_st as (ctx as (sctx, kctx, cctx, tctx), st)) (e, t, d) =
    let 
      val ctxn as (sctxn, kctxn, cctxn, tctxn) = ctx_names ctx
      (* val () = print (sprintf "Type checking $ against $ and $\n" [U.str_e ctxn e, str_mt (sctxn, kctxn) t, str_i sctxn d]) *)
      val (e, (d', j), st) = check_mtype gctx ctx_st (e, t)
      (* val () = println "check type & time" *)
      (* val () = println $ str_region "" "ilist.timl" $ get_region_e e *)
      val () = smart_write_le (gctx_names gctx) (names sctx) (d', d, get_region_e e)
    in
      (e, j, st)
    end

and check_mtype_time_space gctx (ctx_st as (ctx as (sctx, kctx, cctx, tctx), st)) (e, t, (d, j)) =
    let 
      val ctxn as (sctxn, kctxn, cctxn, tctxn) = ctx_names ctx
      val (e, j', st) = check_mtype_time gctx ctx_st (e, t, d)
      val r = get_region_e e
      val () = smart_write_le (gctx_names gctx) (names sctx) (j', j, r)
    in
      (e, st)
    end

and check_decls gctx (ctx, st) decls : decl list * context * int * (idx * idx) list * context * idx StMap.map = 
    let 
      val skctxn_old = (sctx_names $ #1 ctx, names $ #2 ctx)
      fun f (decl, (decls, ctxd, nps, ds, ctx, st)) =
        let 
          val (decl, ctxd', nps', ds', st) = check_decl gctx (ctx, st) decl
          val decls = decl :: decls
          val ctxd = add_ctx ctxd' ctxd
          val nps = nps + nps'
          val ds = ds' @ map (shift_ctx_2i ctxd') ds
          val ctx = add_ctx ctxd' ctx
        in
          (decls, ctxd, nps, ds, ctx, st)
        end
      val (decls, ctxd, nps, ds, ctx, st) = foldl f ([], empty_ctx, 0, [], ctx, st) decls
      val decls = rev decls
      val ctxd = (map4 o map o mapSnd) (SimpType.simp_t o update_t) ctxd
      val ds = map simp_2i $ map update_2i $ rev ds
                   (* val () = println "Typed Decls:" *)
                   (* val () = app println $ str_typing_info (gctx_names gctx) skctxn_old (ctxd, ds) *)
    in
      (decls, ctxd, nps, ds, ctx, st)
    end

and is_wf_datatype gctx ctx (Bind (name, tbinds) : U.mtype U.datatype_def, r) : mtype datatype_def * context =
    let
      val (tname_kinds, (sorts, constr_decls)) = unfold_binds tbinds
      val tnames = map fst tname_kinds
      val sorts = map is_wf_basic_sort sorts
      val nk = (fst name, ((length tnames, sorts), NONE))
      val ctx as (sctx, kctx, _, _) = add_kindingext_skct nk ctx
      fun make_constr ((name, ibinds, r) : U.mtype U.constr_decl) : mtype constr_decl * (string * mtype constr_info) =
	let
          val family = ID (0, r)
          val c = (family, fold_binds (tname_kinds, ibinds))
	  val t = U.constr_type U.TVar LongIdSubst.shiftx_long_id c
	  val t = is_wf_type gctx ((sctx, kctx), t)
		  handle Error (_, msg) =>
			 raise Error (r, 
				      "Constructor is ill-formed" :: 
				      "Cause:" :: 
				      indent msg)
          val () = if length (collect_uvar_t_t t) > 0 then
                     raise Error (r, ["Constructor has unresolved unification type variable(s)"])
                   else ()
          val t = normalize_t true gctx kctx t
          fun constr_from_type t =
            let
              val (tnames, t) = collect_PTUni t
              val tnames = map fst tnames
              val (ns, t) = collect_TUniI t
              fun err t = raise Impossible $ sprintf "constr_from_type (): type ($) not the right form" [str_raw_mt t]
              val (t, is) =
                  case t of
                      TArrow ((_, t), _, (_, t2)) =>
                      (case is_TAppV t2 of
                           SOME (_, _, is) => (t, is)
                         | NONE => err t2
                      )
                    | _ => err t
            in
              (tnames, fold_binds (map (mapSnd fst) ns, (t, is)))
            end
          val (_, ibinds) = constr_from_type t
	in
	  ((name, ibinds, r), (fst name, (family, fold_binds (tname_kinds, ibinds))))
	end
      val (constr_decls, constrs) = (unzip o map make_constr) constr_decls
      val dt = Bind (name, fold_binds (tname_kinds, (sorts, constr_decls)))
      val nk = mapSnd (mapSnd (const_fun (SOME $ TDatatype (dt, r)))) nk
    in
      (dt, ([], add_kindingext nk [], rev constrs, []))
    end
      
fun link_sig r gctx m (ctx' as (sctx', kctx', cctx', tctx') : context) =
  let
    val gctxn = gctx_names gctx
    (* val () = println $ sprintf "Linking module $ (%$) against signature" [str_v (names gctxn) $ fst m, str_int $ fst m] *)
    fun match_sort ((name, s'), sctx') =
      let
        (* val () = println $ sprintf "before fetch_sort_by_name $.$" [str_v (names gctxn) $ fst m, name] *)
        val (x, s) = fetch_sort_by_name gctx [] $ QID (m, (name, r))
        val () = is_sub_sort r gctxn (sctx_names sctx') (s, s')
        val s' = sort_add_idx_eq r s' (IVar (x, []))
        val sctx' = open_and add_sorting (name, s') sctx'
      in
        sctx'
      end
    val sctx' = foldr match_sort [] sctx'
    fun match_kind ((name, k'), kctx') =
      let
        val (x, k) = fetch_kindext_by_name gctx [] $ QID (m, (name, r))
        val () = is_sub_kindext r gctx (sctx', kctx') (k, k')
        fun kind_add_type_eq t (k', t') =
          case t' of
              NONE => (k', SOME t)
           |  SOME t' =>
              let
                (* don't need this check because in this case unify_mt() has been called by is_sub_kindext above *)
                (* val () = unify_mt r gctx (sctx', kctx') (t, t') *)
              in
                (k', SOME t)
              end
        val k' = kind_add_type_eq (TVar x) k'
        val ret = add_kindingext (name, k') kctx'
      in
        ret
      end
    val kctx' = foldr match_kind [] kctx'
    fun match_constr_type (name, c) =
      let
        val (_, t) = fetch_constr_type_by_name gctx [] $ QID (m, (name, r))
        val t' = constr_type TVar LongIdSubst.shiftx_long_id c
      in
        unify_t r gctx (sctx', kctx') (t', t)
      end
    val () = app match_constr_type cctx'
    fun match_type (name, t') =
      let
        val (_, t) = fetch_type_by_name gctx [] $ QID (m, (name, r))
      in
        unify_t r gctx (sctx', kctx') (t, t')
      end
    val () = app match_type tctx'
    val () = close_ctx ctx'
  in
    (sctx', kctx', cctx', tctx')
  end

(* and link_sig_pack (* sigs *) gctx_base sg sg' = *)
(*     case (sg, sg') of *)
(*         (Sig sg, Sig sg') => Sig $ link_sig (* sigs *) gctx_base sg sg' *)
(*       | _ => raise Impossible "link_sig_pack (): only Sig should appear here" *)

fun is_sub_sig r gctx ctx ctx' =
  let
    val mod_name = find_unique (domain gctx) "__link_sig_module" 
    val gctx = add_sigging (mod_name, ctx) gctx
    val () = open_module (mod_name, ctx)
    val _ = link_sig r gctx (mod_name, r) ctx'
    val () = close_n 1
  in
    ()
  end
    
fun is_wf_sig gctx (specs, r) =
  let
    fun is_wf_spec (ctx as (sctx, kctx, _, _)) spec =
      case spec of
          U.SpecVal ((name, r), t) =>
          let
            val t = is_wf_type gctx ((sctx, kctx), t)
          in
            (SpecVal ((name, r), t), add_typing_skct (name, t) ctx)
          end
        | U.SpecIdx ((name, r), s) =>
          let
            val s = is_wf_sort gctx (sctx, s)
          in
            (SpecIdx ((name, r), s), open_and add_sorting_skct (name, s) ctx)
          end
        | U.SpecType ((name, r), k) =>
          let
            val k = is_wf_kind k
          in
            (SpecType ((name, r), k), add_kinding_skct (name, k) ctx)
          end
        | U.SpecTypeDef ((name, r), t) =>
          (case t of
               U.TDatatype (dt, r) =>
               let
                 val (dt, ctxd) = is_wf_datatype gctx ctx (dt, r)
               in
                 (SpecTypeDef ((name, r), TDatatype (dt, r)), add_ctx ctxd ctx)
               end
             | _ =>
               let
                 val (t, k) = get_kind gctx ((sctx, kctx), t)
               in
                 (SpecTypeDef ((name, r), t), add_type_eq_skct (name, (k, t)) ctx)
               end
          )
    fun iter (spec, (specs, ctx)) =
      let
        val (spec, ctx) = is_wf_spec ctx spec
      in
        (spec :: specs, ctx)
      end
    val (specs, ctxd) = foldl iter ([], empty_ctx) specs
    val specs = rev specs
    val () = close_ctx ctxd
  in
    ((specs, r), ctxd)
  end
(* | U.SigVar (x, r) => *)
(*   (case lookup_sig gctx x of *)
(*        SOME sg => sg *)
(*      | NONE => raise Error (r, ["Unbound signature"]) *)
(*   ) *)
(* | U.SigWhere (sg, ((x, r), t)) => *)
(*   let *)
(*     val sg = is_wf_sig gctx sg *)
(*     val k =  *)
(*   in *)
(*   end *)

val debug_dir_name = ref (NONE : string option)
fun debug_write_file filename s =
  case !debug_dir_name of
      SOME dirname => write_file (join_dir_file' dirname filename, s)
    | NONE => ()

structure UPP = UnderscoredPrettyPrint
                  
fun get_sig gctx m =
  case m of
      U.ModComponents (decls, r) =>
      let
        val decls = Teles decls
        val () = debug_write_file
                   "debug-before-TiML-tc.tmp" $
                   fst $ UPP.pp_decls_to_string Gctx.empty ToStringUtil.empty_ctx decls
        val (decls, _) = LiveVars.live_vars_decls decls (* todo: live-evar analysis does not cross module boundaries, so there will be under-estimation if there are top-level function applications *)
        val () = debug_write_file
                   "debug-before-TiML-tc-after-live-vars.tmp" $
                   fst $ UPP.pp_decls_to_string Gctx.empty ToStringUtil.empty_ctx decls
        val decls = unTeles decls
        val (decls, ctxd, nps, ds, _, st) = check_decls gctx (empty_ctx, !st_ref) decls
        val () = StMap.app (fn i => ignore $ forget_above_i_i 0 i handle _ => raise Error (r, ["state can't mention index variables"])) st
        val () = st_ref := st
        val () = close_n nps
        val () = close_ctx ctxd
      in
        (ModComponents (decls, r), ctxd)
      end
    | U.ModSeal (m, sgn) =>
      let
        val (sgn, sg) = is_wf_sig gctx sgn
        val (m, sg') = get_sig gctx m
        val () = is_sub_sig (get_region_m m) gctx sg' sg
      in
        (ModSeal (m, sgn), sg)
      end
    | U.ModTransparentAsc (m, sgn) =>
      let
        val (sgn, sg) = is_wf_sig gctx sgn
        val (m, sg') = get_sig gctx m
        val () = is_sub_sig (get_region_m m) gctx sg' sg
      in
        (ModTransparentAsc (m, sgn), sg')
      end

fun is_wf_map_val t =
    let
      val loop = is_wf_map_val
    in
      case t of
          TMap t => loop t
        | TProd (t1, t2) => loop t1 andalso loop t2
        | TRecord (fields, _) => SMapU.all loop fields
        | _ => is_nullable_wordsize_ty t
    end

fun is_wf_state_ty t =
  case t of
      TMap t => is_wf_map_val t
    | TVector t => is_wordsize_ty t (* vector elements can't be tuples because there is no primitive push_back operation for them on the assembly level *)
    | TSCell t => is_wordsize_ty t
    | TNatCell _ => true
    | _ => false

fun check_top_bind gctx (name, bind) =
  let
    val gctxd = 
        case bind of
            U.TBMod m =>
            let
              val (m, sg) = get_sig gctx m
            in
              (TBMod m, [(name, Sig sg)])
            end
          | U.TBFunctor (((arg_name, r), arg_sg), m) =>
            (* functor applications will be implemented fiberedly instead of parametrizedly *)
            let
              (* val arg_name = name ^ "_" ^ arg_name *)
              val (arg_sg, arg) = is_wf_sig gctx arg_sg
              val gctx = add_sigging (arg_name, arg) gctx
              val () = open_module (arg_name, arg)
              val (m, sg) = get_sig gctx m
              val () = close_n 1
            in
              (TBFunctor (((arg_name, r), arg_sg), m),
               [(name, FunctorBind ((arg_name, arg), sg))])
            end
          | U.TBFunctorApp (f, m) =>
            let
              fun lookup_functor gctx m =
                opt_bind (Gctx.find (gctx, m)) is_FunctorBind
              fun fetch_functor gctx ((m, r) : mod_id) =
                case lookup_functor gctx m of
                    SOME a => a
                  | NONE => raise Error (r, ["Unbound functor " ^ m])
              val ((formal_arg_name, formal_arg), body) = fetch_functor gctx f
              val formal_arg = link_sig (snd m) gctx m formal_arg
            in
              (TBFunctorApp (f, m), [(name, Sig body), (formal_arg_name, Sig formal_arg)])
            end
          | U.TBState t =>
            let
              val t = check_kind_Type Gctx.empty (([], []), t)
              val () = if is_wf_state_ty t then ()
                       else raise Error (get_region_mt t, ["illegal state type"])
              val () = add_state (name, t)
            in
              (TBState t, [])
            end
          | U.TBPragma s => (TBPragma s, [])
    (* val () = println $ sprintf "Typechecked program:" [] *)
    (* val () = app println $ map fst gctxd *)
    (* val () = app println $ str_gctx (gctx_names gctx) gctxd *)
  in
    gctxd
  end

fun collect_mod_long_id acc id =
  case id of
      ID _ => acc
    | QID ((m, _), _) => m :: acc

fun collect_mod_mod_id acc (m, _) = m :: acc

structure CollectMod = CollectModFn (structure Expr = Expr
                                     val on_var = collect_mod_long_id
                                     val on_mod_id = collect_mod_mod_id
                                    )
local
open CollectMod
in
fun collect_mod_ke (k, t) = default [] (Option.map collect_mod_mt t)
                                        
fun collect_mod_ctx ((sctx, kctx, cctx, tctx) : context) =
  let
    val acc = []
    val acc = (concatMap collect_mod_s $ map snd sctx) @ acc
    val acc = (concatMap collect_mod_ke $ map snd kctx) @ acc
    val acc = (concatMap collect_mod_constr $ map snd cctx) @ acc
    val acc = (concatMap collect_mod_t $ map snd tctx) @ acc
  in
    acc
  end
end

fun collect_mod_sgntr b =
  case b of
      Sig ctx => collect_mod_ctx ctx
    | FunctorBind ((name, arg), ctx) => diff op = (collect_mod_ctx ctx) [name]
                                             
structure SU = SetUtilFn (StringBinarySet)
structure S = StringBinarySet

fun get_dependency_graph gctx = Gctx.map (SU.to_set o collect_mod_sgntr) gctx

structure TopoSort = TopoSortFn (structure M = Gctx
                                 structure S = S
                                )

fun check_prog gctx (binds : U.prog) =
    let
      (* val () = println "Begin check_prog()" *)
      fun open_gctx gctx =
        let
          val gctx = filter_module gctx
        in
          app open_module $ find_many gctx $ TopoSort.topo_sort $ Gctx.map (SU.to_set o collect_mod_ctx) $ gctx
          handle TopoSort.TopoSortFailed =>
                 raise Error (dummy, [sprintf "There is circular dependency in models $" [str_ls id $ domain gctx]])
        end
      fun close_gctx gctx =
        close_n $ Gctx.length $ filter_module gctx
      fun iter (((name, r), bind), (binds, acc, gctx)) =
        let
          val () = open_gctx gctx
          val (bind, gctxd) = check_top_bind gctx (name, bind)
          val () = close_gctx gctx
        in
          (((name, r), bind) :: binds, gctxd @ acc, addList (gctx, gctxd))
        end
      val (binds, gctxd, gctx) = foldl iter ([], [], gctx) binds
      val binds = rev binds
                      (* val () = println "End check_prog()" *)
    in
      (binds, gctxd, gctx)
    end

end
