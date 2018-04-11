functor SortcheckFn (structure U : IDX where type base_sort = BaseSorts.base_sort
                                         and type name = string * Region.region
                                         and type region = Region.region
                     structure T : IDX where type base_sort = BaseSorts.base_sort
                                         and type name = string * Region.region
                                         and type region = Region.region
                                         and type 'idx exists_anno = ('idx -> unit) option
                     sharing type U.var = T.var
                     (* val str_v : ToStringUtil.scontext -> U.var -> string *)
                     val str_bs : T.bsort -> string
                     val str_i : ToStringUtil.global_context -> ToStringUtil.scontext -> T.idx -> string
                     val str_s : ToStringUtil.global_context -> ToStringUtil.scontext -> T.sort -> string
                     val U_str_i : ToStringUtil.global_context -> ToStringUtil.scontext -> U.idx -> string
                     type sigcontext
                     val fetch_sort : sigcontext -> (string * T.sort) list * U.var -> T.sort
                     val is_wf_bsort_UVarBS : U.bsort U.uvar_bs -> T.bsort
                     val get_bsort_UVarI : sigcontext -> (string * T.sort) list -> (U.bsort, U.idx) U.uvar_i * U.region -> T.idx * T.bsort
                     val match_BSArrow : sigcontext -> (string * T.sort) list -> Region.region -> T.bsort -> T.bsort * T.bsort
                     val get_sort_type_UVarS : sigcontext -> (string * T.sort) list -> (U.bsort, U.sort) U.uvar_s * U.region -> T.sort
                     val unify_bs : Region.region -> T.bsort * T.bsort -> unit
                     val get_region_i : T.idx -> Region.region
                     val get_region_s : T.sort -> Region.region
                     val U_get_region_i : U.idx -> Region.region
                     val U_get_region_p : U.prop -> Region.region
                     val open_close : (string * T.sort -> (string * T.sort) list -> (string * T.sort) list) -> string * T.sort -> (string * T.sort) list -> ((string * T.sort) list -> 'a) -> 'a
                     val add_sorting : string * T.sort -> (string * T.sort) list -> (string * T.sort) list
                     val update_bs : T.bsort -> T.bsort
                     exception Error of Region.region * string list
                     val get_base : ((T.bsort, T.sort) T.uvar_s * Region.region * (UVar.uvar_name * (string * T.bsort) list) * T.idx list -> T.bsort) -> T.sort -> T.bsort
                     val gctx_names : sigcontext -> ToStringUtil.global_context
                     val normalize_s : T.sort -> T.sort
                     val subst_i_p : T.idx -> T.prop -> T.prop
                     val write_admit : (string * T.sort) list -> T.prop * Region.region -> unit
                     val write_prop : (string * T.sort) list -> T.prop * Region.region -> unit
                     val get_uvar_info : (T.bsort, T.sort) T.uvar_s -> (int * (string * T.bsort) list) option
                     val refine : (T.bsort, T.sort) T.uvar_s -> T.sort -> unit
                    ) = struct

structure IdxUtil = IdxUtilFn (T)
open IdxUtil
open T
open Operators
open BaseSorts
open Util
       
infixr 0 $
infixr 0 !!
         
fun idx_un_op_type opr =
  case opr of
      ToReal => (Nat, Time)
    | Log2 => (Time, Time)
    | Ceil => (Time, Nat)
    | Floor => (Time, Nat)
    | B2n => (BoolSort, Nat)
    | Neg => (BoolSort, BoolSort)
    | IUDiv _ => raise Impossible "idx_un_op_type ()"
    | IUExp _ => raise Impossible "idx_un_op_type ()"

fun idx_bin_op_type opr =
  case opr of
      AndI => (BoolSort, BoolSort, BoolSort)
    | ExpNI => (Nat, Nat, Nat)
    | MaxI => raise Impossible "idx_bin_op_type ()"
    | MinI => raise Impossible "idx_bin_op_type ()"
    | IApp => raise Impossible "idx_bin_op_type ()"
    | EqI => raise Impossible "idx_bin_op_type ()"
    | LtI => raise Impossible "idx_bin_op_type ()"
    | GtI => raise Impossible "idx_bin_op_type ()"
    | LeI => raise Impossible "idx_bin_op_type ()"
    | GeI => raise Impossible "idx_bin_op_type ()"
    | AddI => raise Impossible "idx_bin_op_type ()"
    | MultI => raise Impossible "idx_bin_op_type ()"
    | BoundedMinusI => raise Impossible "idx_bin_op_type ()"
    | MinusI => raise Impossible "idx_bin_op_type()/MinusI"

fun sort_mismatch gctx ctx i expect have =  "Sort mismatch for " ^ str_i gctx ctx i ^ ": expect " ^ expect ^ " have " ^ str_s gctx ctx have

fun is_wf_bsort (bs : U.bsort) : bsort =
  case bs of
      U.Base bs => Base bs
    | U.BSArrow (a, b) => BSArrow (is_wf_bsort a, is_wf_bsort b)
    | U.UVarBS data => is_wf_bsort_UVarBS data

(* a classifier for [sort], since [sort] has [SAbs] and [SApp] *)        
type sort_type = bsort list
val Sort : sort_type = []
fun is_Sort (t : sort_type) = null t

open Bind
       
fun sctx_names ctx = (* List.mapPartial id $ *) map fst ctx
                                                                 
fun get_sort_type gctx (ctx, s : U.sort) : sort * sort_type =
  let
    val get_sort_type = get_sort_type gctx
    val is_wf_sort = is_wf_sort gctx
    val is_wf_prop = is_wf_prop gctx
    val get_bsort = get_bsort gctx
    val check_bsort = check_bsort gctx
  in
    case s of
	U.Basic (bs, r) => (Basic (is_wf_bsort bs, r), Sort)
      | U.Subset ((bs, r), Bind ((name, r2), p), r_all) =>
        let 
          val bs = is_wf_bsort bs
          val p = open_close add_sorting (name, Basic (bs, r)) ctx (fn ctx => is_wf_prop (ctx, p))
        in
          (Subset ((bs, r), Bind ((name, r2), p), r_all), Sort)
        end
      | U.UVarS data => 
        (* sort underscore will always mean a sort of type Sort *)
        (get_sort_type_UVarS gctx ctx data, Sort)
      | U.SAbs (b, Bind ((name, r1), s), r) =>
        let
          val b = is_wf_bsort b
          val (s, t) = get_sort_type (add_sorting (name, Basic (b, r1)) ctx, s)
        in
          (SAbs (b, Bind ((name, r1), s), r), b :: t)
        end
      | U.SApp (s, i) =>
        let
          val (s, t) = get_sort_type (ctx, s)
          val (b, t) =
              case t of
                  b :: t => (b, t)
                | [] => raise Error (get_region_s s, [sprintf "sort $ should be an abstract" [str_s (gctx_names gctx) (sctx_names ctx) s]])
          val i = check_bsort (ctx, i, b)
        in
          (SApp (s, i), t)
        end
        
  end

and is_wf_sort gctx (ctx, s) =
  let
    val (s, t) = get_sort_type gctx (ctx, s)
    val r = get_region_s s
    val () =
        if is_Sort t then
          ()
        else
          raise Error (r, [sprintf "sort $ is ill-formed (not fully applied)" [str_s (gctx_names gctx) (sctx_names ctx) s]])
  in
    s
  end

and is_wf_prop gctx (ctx, p) =
    let
      val is_wf_sort = is_wf_sort gctx
      val is_wf_prop = is_wf_prop gctx
      val get_bsort = get_bsort gctx
      val check_bsort = check_bsort gctx
    in
      case p of
	  U.PTrueFalse (b, r) => PTrueFalse (b, r)
        | U.Not (p, r) => 
          Not (is_wf_prop (ctx, p), r)
        | U.BinConn (opr, p1, p2) =>
	  BinConn (opr,
                   is_wf_prop (ctx, p1),
	           is_wf_prop (ctx, p2))
        | U.BinPred (EqP, i1, i2) =>
	  let 
            val (i1, bs1) = get_bsort (ctx, i1)
	    val (i2, bs2) = get_bsort (ctx, i2)
            (* val () = println $ sprintf "is_wf_prop()/EqP: $ vs $" [str_bs bs1, str_bs bs2] *)
            val () = unify_bs (U_get_region_p p) (bs1, bs2)
	  in
            BinPred (EqP, i1, i2)
	  end
        | U.BinPred (opr, i1, i2) =>
	  let 
            val (i1, bs1) = get_bsort (ctx, i1)
	    val (i2, bs2) = get_bsort (ctx, i2)
            val () = unify_bs (U_get_region_p p) (bs1, bs2)
            val bs = update_bs bs1
            fun error expected =
              Error (U_get_region_p p, sprintf "Sorts of operands of $ must be both $:" [str_bin_pred opr, expected] :: indent ["left: " ^ str_bs bs1, "right: " ^ str_bs bs2])
            val () =
                case opr of
                    BigO =>
                    let
                      val (args, ret) = collect_BSArrow bs
                      val r = U_get_region_p p
                      val () =
                          case ret of
                              UVarBS _ => ()  (* if it's uvar, it may be BSArrow *)
                            | _ => unify_bs r (ret, Base Time)
                      val () = app (fn arg => unify_bs r (arg, Base Nat)) args
                    in
                      ()
                    end
                  | _ =>
                    (case bs of
                         Base Nat => ()
                       | Base Time => ()
                       | _ => raise error "Nat or Time"
                    )
	  in
            BinPred (opr, i1, i2)
	  end
        | U.Quan (q, bs, Bind ((name, r), p), r_all) =>
          let
            val q = case q of
                        Forall => Forall
                      | Exists _ => Exists NONE
            val bs = is_wf_bsort bs
            val p = open_close add_sorting (name, Basic (bs, r)) ctx (fn ctx => is_wf_prop (ctx, p))
          in
            Quan (q, bs, Bind ((name, r), p), r_all)
          end
    end
      
and get_bsort gctx (ctx, i) =
    let
      val is_wf_sort = is_wf_sort gctx
      val is_wf_prop = is_wf_prop gctx
      val get_bsort = get_bsort gctx
      val check_bsort = check_bsort gctx
      fun main () =
        case i of
	    U.VarI (x, sorts) =>
            let
              fun get_base_from_sort s =
                  let
                    fun error r gctx ctx () = Error (r, [sprintf "Can't figure out base sort of $" [str_s gctx ctx s]])
                  in
                    get_base (fn _ => raise error (U_get_region_i i) (gctx_names gctx) (sctx_names ctx) ()) s
                  end
            in
              case sorts of
                 s :: sorts =>
                 let
                   val s = is_wf_sort (ctx, s)
                   val i = check_sort gctx (ctx, U.VarI (x, sorts), s)
                   val (x, sorts) = case i of
                                VarI a => a
                              | _ => raise Impossible "get_bsort/VarI"
                 in
                   (VarI (x, s :: sorts), get_base_from_sort s)
                 end
               | [] =>
                 let
                   val s = fetch_sort gctx (ctx, x)
                 in
                   (VarI (x, [s]), get_base_from_sort s)
                 end
            end
          | U.IConst (c, r) =>
            (case c of
	         ICBool _ => 
                 (IConst (c, r), Base BoolSort)
	       | ICTT => 
                 (TTI r, Base UnitSort)
	       | ICTime x => 
	         (ConstIT (x, r), Base Time)
	       | ICNat n => 
	         if n >= 0 then
	           (ConstIN (n, r), Base Nat)
	         else
	           raise Error (r, ["Natural number constant must be non-negative"])
	       | ICAdmit => 
                 (AdmitI r, Base UnitSort)
            )
          | U.UnOpI (opr, i, r) =>
            (case opr of
                 IUDiv n =>
                 let 
                   val i = check_bsort (ctx, i, Base Time)
	           val () = if n > 0 then ()
	                    else raise Error (r, ["Can only divide by positive integer"])
                 in
                   (DivI (i, (n, r)), Base Time)
                 end
               | IUExp n =>
                 let 
                   val i = check_bsort (ctx, i, Base Time)
                 in
                   (ExpI (i, (n, r)), Base Time)
                 end
               | _ =>
                 let
                   val (atype, rettype) = idx_un_op_type opr
                 in
                   (UnOpI (opr,
                           check_bsort (ctx, i, Base atype),
                           r),
                    Base rettype)
                 end
            )
	  | U.BinOpI (opr, i1, i2) =>
            let
              (* overloaded binary operations *)
              fun overloaded bases rettype =
                let 
                  val (i1, bs1) = get_bsort (ctx, i1)
                  val (i2, bs2) = get_bsort (ctx, i2)
                  val () = unify_bs (U_get_region_i i) (bs1, bs2)
                  val bs = update_bs bs1
                  fun error () = Error (U_get_region_i i, sprintf "Sorts of operands of $ must be the same and from $:" [str_idx_bin_op opr, str_ls str_b bases] :: indent ["left: " ^ str_bs bs1, "right: " ^ str_bs bs2])
                  val rettype =
                      case bs of
                          Base b =>
                          if mem op= b bases then
                            case rettype of
                                SOME b => Base b
                              | NONE => bs
                          else raise error ()
                        | _ => raise error ()
                in
                  (BinOpI (opr, i1, i2), rettype)
                end
            in
              case opr of
                  IApp =>
                  let
                    (* val () = println $ U.str_i (names ctx) i *)
                    val (i1, bs) = get_bsort (ctx, i1)
                    val (bs1, bs2) = match_BSArrow gctx ctx (get_region_i i1) bs
                    val i2 = check_bsort (ctx, i2, bs1)
                  in
                    (BinOpI (opr, i1, i2), bs2)
                  end
                | AddI => overloaded [Nat, Time] NONE
                | BoundedMinusI => overloaded [Nat, Time] NONE
                | MinusI => overloaded [Nat, Time] NONE
                | MultI => overloaded [Nat, Time] NONE
                | MaxI => overloaded [Nat, Time] NONE
                | MinI => overloaded [Nat, Time] NONE
                | EqI => overloaded [Nat, BoolSort, UnitSort] (SOME BoolSort)
                | LtI => overloaded [Nat, Time(* , BoolSort, UnitSort *)] (SOME BoolSort)
                | GtI => overloaded [Nat, Time(* , BoolSort, UnitSort *)] (SOME BoolSort)
                | LeI => overloaded [Nat, Time(* , BoolSort, UnitSort *)] (SOME BoolSort)
                | GeI => overloaded [Nat, Time(* , BoolSort, UnitSort *)] (SOME BoolSort)
                | _ =>
                  let
                    val (arg1type, arg2type, rettype) = idx_bin_op_type opr
                  in
                    (BinOpI (opr,
                             check_bsort (ctx, i1, Base arg1type),
                             check_bsort (ctx, i2, Base arg2type)),
                     Base rettype)
                  end
            end
          | i_all as U.Ite (i, i1, i2, r) =>
            let
              val i = check_bsort (ctx, i, Base BoolSort)
              val (i1, bs1) = get_bsort (ctx, i1)
              val (i2, bs2) = get_bsort (ctx, i2)
              val () = unify_bs (U_get_region_i i_all) (bs1, bs2)
            in
              (Ite (i, i1, i2, r), bs1)
            end
          | U.IAbs (bs1, Bind ((name, r1), i), r) =>
            let
              val bs1 = is_wf_bsort bs1
              val (i, bs) = open_close add_sorting (name, Basic (bs1, r1)) ctx (fn ctx => get_bsort (ctx, i))
            in
              (IAbs (bs1, Bind ((name, r1), i), r), BSArrow (bs1, bs))
                (* case bs of *)
                (*     Base (TimeFun arity) => *)
                (*     (IAbs ((name, r1), i, r), Base (TimeFun (arity + 1))) *)
                (*   | _ => raise Error (get_region_i i, "Sort of time funtion body should be time function" :: indent ["want: time function", "got: " ^ str_bs bs]) *)
            end
          | U.UVarI data => get_bsort_UVarI gctx ctx data
      val ret = main ()
                handle
                Error (r, msg) =>
                raise Error (r, msg @ ["when sort-checking index "] @ indent [U_str_i (gctx_names gctx) (sctx_names ctx) i])
                (* raise Error (r, msg @ [sprintf "when sort-checking index $ in context $" [U.str_i (gctx_names gctx) (sctx_names ctx) i, str_ls (fn (name, sort) => sprintf "\n$: $" [name, sort]) $ str_sctx (gctx_names gctx) ctx]]) *)
      (* val () = println $ sprintf "get_bsort() result: $ : $" [str_i (gctx_names gctx) (sctx_names ctx) (fst ret), str_bs (snd ret)] *)
    in
      ret
    end

and check_bsort gctx (ctx, i : U.idx, bs : bsort) : idx =
    let 
      (* val () = println $ sprintf "check_bsort $ against $" [U_str_i (gctx_names gctx) (sctx_names ctx) i, str_bs bs] *)
      val (i, bs') = get_bsort gctx (ctx, i)
      val () = unify_bs (get_region_i i) (bs', bs)
    in
      i
    end

(* fun subst_uvar_error r body i ((fresh, fresh_ctx), x) = *)
(*   Error (r, *)
(*          sprintf "Can't substitute for $ in unification variable $ in $" [str_v fresh_ctx x, fresh, body] :: *)
(*          indent [ *)
(*            sprintf "because the context of $ is [$] which contains $" [fresh, join ", " $ fresh_ctx, str_v fresh_ctx x] *)
(*         ]) *)

and check_sort gctx (ctx, i : U.idx, s : sort) : idx =
  let 
    (* val () = println $ sprintf "sortchecking $ against $" [U_str_i (gctx_names gctx) (sctx_names ctx) i, str_s (gctx_names gctx) (sctx_names ctx) s] *)
    val (i, bs') = get_bsort gctx (ctx, i)
    val r = get_region_i i
    val s = normalize_s s
    exception UnifySAppFailed
    fun unify_SApp_UVarS s =
      let
        val ((x, _), _) = is_SApp_UVarS s !! (fn () => raise UnifySAppFailed)
        val (_, ctx) = get_uvar_info x !! (fn () => raise Impossible "check_sort()/unify_SApp_UVar(): x should be Fresh")
        val s = Basic (bs', r)
        val s = SAbs_Many (rev ctx, s, r)
        val () = refine x s
      in
        ()
      end
    fun main s =
      case s of
	  Subset ((bs, _), Bind ((name, _), p), _) =>
          let
	    val () = unify_bs r (bs', bs)
            val r = get_region_i i
            val (i, is_admit) =
                case i of
                    IConst (ICAdmit, r) => (TTI r, true)
                  | _ => (i, false)
            (* val () = println $ "is_admit=" ^ str_bool is_admit *)
            val p = subst_i_p i p
            (* val () = println $ sprintf "Writing prop $ $" [str_p (gctx_names gctx) (sctx_names ctx) p, str_region "" "" r] *)
	    val () =
                if is_admit then
                  write_admit ctx (p, r)
                else
                  write_prop ctx (p, r)
          in
            ()
          end
	| Basic (bs, _) => 
	  unify_bs r (bs', bs)
        | UVarS _ => raise Impossible "check_sort()/main(): s should be UVarS"
        | SAbs _ => raise Impossible "check_sort()/main(): s shouldn't be SAbs"
        | SApp _ => raise Impossible "check_sort()/main(): s shouldn't be SApp"
    val () =
        unify_SApp_UVarS s
        handle
        UnifySAppFailed =>
        (main s
         handle Error (_, msg) =>
                let
                  val ctxn = sctx_names ctx
                  val gctxn = gctx_names gctx
                in
                  raise Error (r,
                               sprintf "index $ (of base sort $) is not of sort $" [str_i gctxn ctxn i, str_bs bs', str_s gctxn ctxn s] ::
                               "Cause:" ::
                               indent msg)
                end
        )
  in
    i
  end

fun is_wf_sorts gctx (ctx, sorts : U.sort list) : sort list = 
  map (fn s => is_wf_sort gctx (ctx, s)) sorts
      
end
