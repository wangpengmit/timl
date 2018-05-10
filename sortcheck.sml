functor SortcheckFn (structure U : IDX where type base_sort = BaseSorts.base_sort
                                         and type name = string * Region.region
                                         and type region = Region.region
                     structure T : IDX where type base_sort = BaseSorts.base_sort
                                         and type name = string * Region.region
                                         and type region = Region.region
                                         and type 'idx exists_anno = ('idx -> unit) option
                     sharing type U.var = T.var
                     (* val str_v : ToStringUtil.scontext -> U.var -> string *)
                     val str_bs : T.basic_sort -> string
                     val str_i : ToStringUtil.global_context -> ToStringUtil.scontext -> T.idx -> string
                     val str_s : ToStringUtil.global_context -> ToStringUtil.scontext -> T.sort -> string
                     val U_str_i : ToStringUtil.global_context -> ToStringUtil.scontext -> U.idx -> string
                     type sigcontext
                     val fetch_sort : sigcontext -> (string * T.sort) list * U.var -> T.sort
                     val is_wf_basic_sort_BSUVar : U.basic_sort U.uvar_bs -> T.basic_sort
                     val get_basic_sort_IUVar : sigcontext -> (string * T.sort) list -> (U.basic_sort, U.idx) U.uvar_i * U.region -> T.idx * T.basic_sort
                     val match_BSArrow : sigcontext -> (string * T.sort) list -> Region.region -> T.basic_sort -> T.basic_sort * T.basic_sort
                     val get_sort_type_SUVar : sigcontext -> (string * T.sort) list -> (U.basic_sort, U.sort) U.uvar_s * U.region -> T.sort
                     val unify_bs : Region.region -> T.basic_sort * T.basic_sort -> unit
                     val get_region_i : T.idx -> Region.region
                     val get_region_s : T.sort -> Region.region
                     val U_get_region_i : U.idx -> Region.region
                     val U_get_region_p : U.prop -> Region.region
                     val open_close : (string * T.sort -> (string * T.sort) list -> (string * T.sort) list) -> string * T.sort -> (string * T.sort) list -> ((string * T.sort) list -> 'a) -> 'a
                     val add_sorting : string * T.sort -> (string * T.sort) list -> (string * T.sort) list
                     val update_bs : T.basic_sort -> T.basic_sort
                     exception Error of Region.region * string list
                     val get_base : ((T.basic_sort, T.sort) T.uvar_s * Region.region * (UVar.uvar_name * (string * T.basic_sort) list) * T.idx list -> T.basic_sort) -> T.sort -> T.basic_sort
                     val gctx_names : sigcontext -> ToStringUtil.global_context
                     val normalize_s : T.sort -> T.sort
                     val subst_i_p : T.idx -> T.prop -> T.prop
                     val write_admit : (string * T.sort) list -> T.prop * Region.region -> unit
                     val write_prop : (string * T.sort) list -> T.prop * Region.region -> unit
                     val get_uvar_info : (T.basic_sort, T.sort) T.uvar_s -> (int * (string * T.basic_sort) list) option
                     val refine : (T.basic_sort, T.sort) T.uvar_s -> T.sort -> unit
                    ) = struct

structure IdxUtil = IdxUtilFn (T)
open IdxUtil
open T
open Operators
open BaseSorts
open Util
       
infixr 0 $
infixr 0 !!
         
val BSTime = BSBase BSSTime
val BSNat = BSBase BSSNat
val BSBool = BSBase BSSBool
val BSUnit = BSBase BSSUnit
val BSState = BSBase BSSState
                 
fun STime r = SBasic (BSTime, r)
fun SNat r = SBasic (BSNat, r)
fun SBool r = SBasic (BSBool, r)
fun SUnit r = SBasic (BSUnit, r)
                  
fun sort_mismatch gctx ctx i expect have =  "Sort mismatch for " ^ str_i gctx ctx i ^ ": expect " ^ expect ^ " have " ^ str_s gctx ctx have

fun is_wf_basic_sort (bs : U.basic_sort) : basic_sort =
  case bs of
      U.BSBase bs => BSBase bs
    | U.BSArrow (a, b) => BSArrow (is_wf_basic_sort a, is_wf_basic_sort b)
    | U.BSUVar data => is_wf_basic_sort_BSUVar data

(* a classifier for [sort], since [sort] has [SAbs] and [SApp] *)        
type sort_type = basic_sort list
val Sort : sort_type = []
fun is_Sort (t : sort_type) = null t

open Bind
       
fun sctx_names ctx = (* List.mapPartial id $ *) map fst ctx
                                                                 
fun get_sort_type gctx (ctx, s : U.sort) : sort * sort_type =
  let
    val get_sort_type = get_sort_type gctx
    val is_wf_sort = is_wf_sort gctx
    val is_wf_prop = is_wf_prop gctx
    val get_basic_sort = get_basic_sort gctx
    val check_basic_sort = check_basic_sort gctx
  in
    case s of
	U.SBasic (bs, r) => (SBasic (is_wf_basic_sort bs, r), Sort)
      | U.SSubset ((bs, r), Bind ((name, r2), p), r_all) =>
        let 
          val bs = is_wf_basic_sort bs
          val p = open_close add_sorting (name, SBasic (bs, r)) ctx (fn ctx => is_wf_prop (ctx, p))
        in
          (SSubset ((bs, r), Bind ((name, r2), p), r_all), Sort)
        end
      | U.SUVar data => 
        (* sort underscore will always mean a sort of type Sort *)
        (get_sort_type_SUVar gctx ctx data, Sort)
      | U.SAbs (b, Bind ((name, r1), s), r) =>
        let
          val b = is_wf_basic_sort b
          val (s, t) = get_sort_type (add_sorting (name, SBasic (b, r1)) ctx, s)
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
          val i = check_basic_sort (ctx, i, b)
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
      val get_basic_sort = get_basic_sort gctx
      val check_basic_sort = check_basic_sort gctx
    in
      case p of
	  U.PTrueFalse (b, r) => PTrueFalse (b, r)
        | U.PNot (p, r) => 
          PNot (is_wf_prop (ctx, p), r)
        | U.PBinConn (opr, p1, p2) =>
	  PBinConn (opr,
                   is_wf_prop (ctx, p1),
	           is_wf_prop (ctx, p2))
        | U.PBinPred (EqP, i1, i2) =>
	  let 
            val (i1, bs1) = get_basic_sort (ctx, i1)
	    val (i2, bs2) = get_basic_sort (ctx, i2)
            (* val () = println $ sprintf "is_wf_prop()/EqP: $ vs $" [str_bs bs1, str_bs bs2] *)
            val () = unify_bs (U_get_region_p p) (bs1, bs2)
	  in
            PBinPred (BPEq, i1, i2)
	  end
        | U.PBinPred (opr, i1, i2) =>
	  let 
            val (i1, bs1) = get_basic_sort (ctx, i1)
	    val (i2, bs2) = get_basic_sort (ctx, i2)
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
                              BSUVar _ => ()  (* if it's uvar, it may be BSArrow *)
                            | _ => unify_bs r (ret, BSTime)
                      val () = app (fn arg => unify_bs r (arg, BSNat)) args
                    in
                      ()
                    end
                  | _ =>
                    (case bs of
                         BSBase Nat => ()
                       | BSBase Time => ()
                       | _ => raise error "Nat or Time"
                    )
	  in
            PBinPred (opr, i1, i2)
	  end
        | U.PQuan (q, bs, Bind ((name, r), p), r_all) =>
          let
            val q = case q of
                        Forall => Forall
                      | Exists _ => Exists NONE
            val bs = is_wf_basic_sort bs
            val p = open_close add_sorting (name, SBasic (bs, r)) ctx (fn ctx => is_wf_prop (ctx, p))
          in
            PQuan (q, bs, Bind ((name, r), p), r_all)
          end
    end
      
and get_basic_sort gctx (ctx, i) =
    let
      val is_wf_sort = is_wf_sort gctx
      val is_wf_prop = is_wf_prop gctx
      val get_basic_sort = get_basic_sort gctx
      val check_basic_sort = check_basic_sort gctx
      fun main () =
        case i of
	    U.IVar (x, sorts) =>
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
                   val i = check_sort gctx (ctx, U.IVar (x, sorts), s)
                   val (x, sorts) = case i of
                                IVar a => a
                              | _ => raise Impossible "get_basic_sort/IVar"
                 in
                   (IVar (x, s :: sorts), get_base_from_sort s)
                 end
               | [] =>
                 let
                   val s = fetch_sort gctx (ctx, x)
                 in
                   (IVar (x, [s]), get_base_from_sort s)
                 end
            end
          | U.IConst (c, r) =>
            (case c of
	         ICBool _ => 
                 (IConst (c, r), BSBool)
	       | ICTT => 
                 (ITT r, BSUnit)
	       | ICTime x => 
	         (ITime (x, r), BSTime)
	       | ICNat n => 
	         if n >= 0 then
	           (INat (n, r), BSNat)
	         else
	           raise Error (r, ["Natural number constant must be non-negative"])
	       | ICAdmit => 
                 (IAdmit r, BSUnit)
            )
          | U.IUnOp (opr, i, r) =>
            let
              fun idx_un_op_type opr =
                case opr of
                    IUToReal => (BSSNat, BSSTime)
                  | IULog _ => (BSSTime, BSSTime)
                  | IUCeil => (BSSTime, BSSNat)
                  | IUFloor => (BSSTime, BSSNat)
                  | IUB2n => (BSSBool, BSSNat)
                  | IUNeg => (BSSBool, BSSBool)
                  | IUDiv _ => raise Impossible "idx_un_op_type ()"
                                     (* | IUExp _ => raise Impossible "idx_un_op_type ()" *)
            in
              case opr of
                  IUDiv n =>
                  let 
                    val i = check_basic_sort (ctx, i, BSTime)
	            val () = if n > 0 then ()
	                     else raise Error (r, ["Can only divide by positive integer"])
                  in
                    (IDiv (i, (n, r)), BSTime)
                  end
                (* | IUExp n => *)
                (*   let  *)
                (*     val i = check_basic_sort (ctx, i, BSBase Time) *)
                (*   in *)
                (*     (ExpI (i, (n, r)), BSBase Time) *)
                (*   end *)
                | _ =>
                  let
                    val (atype, rettype) = idx_un_op_type opr
                  in
                    (IUnOp (opr,
                            check_basic_sort (ctx, i, BSBase atype),
                            r),
                     BSBase rettype)
                  end
            end
	  | U.IBinOp (opr, i1, i2) =>
            let
              (* overloaded binary operations *)
              fun overloaded bases rettype =
                let 
                  val (i1, bs1) = get_basic_sort (ctx, i1)
                  val (i2, bs2) = get_basic_sort (ctx, i2)
                  val () = unify_bs (U_get_region_i i) (bs1, bs2)
                  val bs = update_bs bs1
                  fun error () = Error (U_get_region_i i, sprintf "Sorts of operands of $ must be the same and from $:" [str_idx_bin_op opr, str_ls str_b bases] :: indent ["left: " ^ str_bs bs1, "right: " ^ str_bs bs2])
                  val rettype =
                      case bs of
                          BSBase b =>
                          if mem op= b bases then
                            case rettype of
                                SOME b => BSBase b
                              | NONE => bs
                          else raise error ()
                        | _ => raise error ()
                in
                  (IBinOp (opr, i1, i2), rettype)
                end
              fun idx_bin_op_type opr =
                case opr of
                    IBAndI => (BSSBool, BSSBool, BSSBool)
                  | IBOr => (BSSBool, BSSBool, BSSBool)
                  | IBExpN => raise Impossible "idx_bin_op_type ()"
                  | IBMax => raise Impossible "idx_bin_op_type ()"
                  | IBMin => raise Impossible "idx_bin_op_type ()"
                  | IBApp => raise Impossible "idx_bin_op_type ()"
                  | IBEq => raise Impossible "idx_bin_op_type ()"
                  | IBLt => raise Impossible "idx_bin_op_type ()"
                  | IBGt => raise Impossible "idx_bin_op_type ()"
                  | IBLe => raise Impossible "idx_bin_op_type ()"
                  | IBGe => raise Impossible "idx_bin_op_type ()"
                  | IBAdd => raise Impossible "idx_bin_op_type ()"
                  | IBMult => raise Impossible "idx_bin_op_type ()"
                  | IBMod => raise Impossible "idx_bin_op_type ()"
                  | IBBoundedMinus => raise Impossible "idx_bin_op_type ()"
                  | IBMinus => raise Impossible "idx_bin_op_type()/MinusI"
                  | IBUnion => (BSSState, BSSState, BSSState)
            in
              case opr of
                  IBApp =>
                  let
                    (* val () = println $ U.str_i (names ctx) i *)
                    val (i1, bs) = get_basic_sort (ctx, i1)
                    val (bs1, bs2) = match_BSArrow gctx ctx (get_region_i i1) bs
                    val i2 = check_basic_sort (ctx, i2, bs1)
                  in
                    (IBinOp (opr, i1, i2), bs2)
                  end
                | IBAdd => overloaded [BSSNat, BSSTime] NONE
                | IBBoundedMinus => overloaded [BSSNat, BSSTime] NONE
                | IBExpN => overloaded [BSSNat, BSSTime] NONE
                | IBMinus => overloaded [BSSNat, BSSTime] NONE
                | IBMult => overloaded [BSSNat, BSSTime] NONE
                | IBMod => overloaded [BSSNat] NONE
                | IBMax => overloaded [BSSNat, BSSTime] NONE
                | IBMin => overloaded [BSSNat, BSSTime] NONE
                | IBEq => overloaded [BSSNat, BSSBool, BSSUnit] (SOME BSSBool)
                | IBLt => overloaded [BSSNat, BSSTime(* , BSSBool, UnitSort *)] (SOME BSSBool)
                | IBGt => overloaded [BSSNat, BSSTime(* , BSSBool, UnitSort *)] (SOME BSSBool)
                | IBLe => overloaded [BSSNat, BSSTime(* , BSSBool, UnitSort *)] (SOME BSSBool)
                | IBGe => overloaded [BSSNat, BSSTime(* , BSSBool, UnitSort *)] (SOME BSSBool)
                | _ =>
                  let
                    val (arg1type, arg2type, rettype) = idx_bin_op_type opr
                  in
                    (IBinOp (opr,
                             check_basic_sort (ctx, i1, BSBase arg1type),
                             check_basic_sort (ctx, i2, BSBase arg2type)),
                     BSBase rettype)
                  end
            end
          | i_all as U.IIte (i, i1, i2, r) =>
            let
              val i = check_basic_sort (ctx, i, BSBool)
              val (i1, bs1) = get_basic_sort (ctx, i1)
              val (i2, bs2) = get_basic_sort (ctx, i2)
              val () = unify_bs (U_get_region_i i_all) (bs1, bs2)
            in
              (IIte (i, i1, i2, r), bs1)
            end
          | U.IAbs (bs1, Bind ((name, r1), i), r) =>
            let
              val bs1 = is_wf_basic_sort bs1
              (* todo: check monotonicity of argument variable in function body *)
              val (i, bs) = open_close add_sorting (name, SBasic (bs1, r1)) ctx (fn ctx => get_basic_sort (ctx, i))
            in
              (IAbs (bs1, Bind ((name, r1), i), r), BSArrow (bs1, bs))
                (* case bs of *)
                (*     BSBase (TimeFun arity) => *)
                (*     (IAbs ((name, r1), i, r), BSBase (TimeFun (arity + 1))) *)
                (*   | _ => raise Error (get_region_i i, "Sort of time funtion body should be time function" :: indent ["want: time function", "got: " ^ str_bs bs]) *)
            end
          | U.IUVar data => get_basic_sort_IUVar gctx ctx data
          | U.IState st =>
            (IState $ StMap.map (fn i => check_basic_sort (ctx, i, BSNat)) st, BSState)
      val ret = main ()
                handle
                Error (r, msg) =>
                raise Error (r, msg @ ["when sort-checking index "] @ indent [U_str_i (gctx_names gctx) (sctx_names ctx) i])
                (* raise Error (r, msg @ [sprintf "when sort-checking index $ in context $" [U.str_i (gctx_names gctx) (sctx_names ctx) i, str_ls (fn (name, sort) => sprintf "\n$: $" [name, sort]) $ str_sctx (gctx_names gctx) ctx]]) *)
      (* val () = println $ sprintf "get_basic_sort() result: $ : $" [str_i (gctx_names gctx) (sctx_names ctx) (fst ret), str_bs (snd ret)] *)
    in
      ret
    end

and check_basic_sort gctx (ctx, i : U.idx, bs : basic_sort) : idx =
    let 
      (* val () = println $ sprintf "check_basic_sort $ against $" [U_str_i (gctx_names gctx) (sctx_names ctx) i, str_bs bs] *)
      val (i, bs') = get_basic_sort gctx (ctx, i)
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
    val (i, bs') = get_basic_sort gctx (ctx, i)
    val r = get_region_i i
    val s = normalize_s s
    exception UnifySAppFailed
    fun unify_SApp_SUVar s =
      let
        val ((x, _), _) = is_SApp_SUVar s !! (fn () => raise UnifySAppFailed)
        val (_, ctx) = get_uvar_info x !! (fn () => raise Impossible "check_sort()/unify_SApp_UVar(): x should be Fresh")
        val s = SBasic (bs', r)
        val s = SAbs_Many (rev ctx, s, r)
        val () = refine x s
      in
        ()
      end
    fun main s =
      case s of
	  SSubset ((bs, _), Bind ((name, _), p), _) =>
          let
	    val () = unify_bs r (bs', bs)
            val r = get_region_i i
            val (i, is_admit) =
                case i of
                    IConst (ICAdmit, r) => (ITT r, true)
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
	| SBasic (bs, _) => 
	  unify_bs r (bs', bs)
        | SUVar _ => raise Impossible "check_sort()/main(): s should be SUVar"
        | SAbs _ => raise Impossible "check_sort()/main(): s shouldn't be SAbs"
        | SApp _ => raise Impossible "check_sort()/main(): s shouldn't be SApp"
    val () =
        unify_SApp_SUVar s
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
