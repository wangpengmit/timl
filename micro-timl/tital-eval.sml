(* TiTAL evaluator (i.e. simulator) *)

structure TiTALEval = struct

open MicroTiMLExUtil
open MicroTiMLExLongId
open TiTAL
open TiTALVisitor

infixr 0 $
       
fun adapt f d x v env = f (d + env) (x + env) v
fun subst_i_insts d x v = subst_i_insts_fn (adapt substx_i_i d x v, adapt subst_i_t d x v)
fun subst0_i_insts a = subst_i_insts 0 0 a
fun adapt f d x v env b =
  let
    fun add_depth (di, dt) (di', dt') = (idepth_add (di, di'), tdepth_add (dt, dt'))
  in
    f (add_depth d env) (x + unTDepth (snd env)) v b
  end
fun subst_t_insts d x v = subst_t_insts_fn (adapt subst_t_t d x v)
fun subst0_t_insts a = subst_t_insts (IDepth 0, TDepth 0) 0 a

fun subst0_its_insts itargs b =
  let
    val (len_i, len_t) = foldl
                           (fn (v, (ni, nt)) =>
                               case v of
                                   inl _ => (ni+1, nt)
                                 | inr _ => (ni, nt+1)
                           ) (0, 0) itargs
    val b = fst $ foldl
                (fn (v, (b, (ni, nt))) =>
                    case v of
                        inl v => (subst_i_insts (ni-1) (ni-1) v b, (ni-1, nt))
                      | inr v => (subst_t_insts (IDepth ni, TDepth (nt-1)) (nt-1) v b, (ni, nt-1))
                ) (b, (len_i, len_t)) itargs
  in
    b
  end
                    
infixr 5 @::
infixr 5 @@
infix  6 @+
infix  9 @!
       
(* word values *)
datatype ('idx, 'ty) wordv =
         WVLabel of label
         | WVConst of Operators.expr_const
         | WVUninit
         (* | WVBuiltin of 'ty *)
         (* | WVNever of 'ty *)
         | WVAppT of ('idx, 'ty) wordv * 'ty
         | WVAppI of ('idx, 'ty) wordv * 'idx
         | WVPack of 'ty * 'ty * ('idx, 'ty) wordv
         | WVPackI of 'ty * 'idx * ('idx, 'ty) wordv
         | WVFold of 'ty * ('idx, 'ty) wordv
                                       
(* heap value *)
datatype ('idx, 'sort, 'kind, 'ty) heapv =
         HVCode of ('idx, 'sort, 'kind, 'ty) hval
         | HVPair of ('idx, 'ty) wordv * ('idx, 'ty) wordv
         | HVInj of injector * ('idx, 'ty) wordv
         | HVArray of ('idx, 'ty) wordv list

fun assert_SOME a = case a of SOME v => v | NONE => raise Impossible "assert_SOME()"

fun must_find (m, _) k = assert_SOME $ Rctx.find (m, k)
                                       
infix  9 @!!
fun m @!! k = must_find m k

fun add (m, max_k) (k, v) = (m @+ (k, v), max max_k k)
fun m @+ p = add m p

fun fresh_key (_, max_k) = max_k + 1

val fresh_label = fresh_key
                  
fun read_v R v =
  case v of
      VReg r => R @!! r
    | VWord w =>
      (case w of
           WLabel l => WVLabel l
         | WConst c => WVConst c
         | WUninit t => WVUninit
         | WBuiltin _ => raise Impossible "WBuiltin is not a legal word value"
         | WNever _ => raise Impossible "WNever is not a legal word value"
      )
      | VAppI (v, i) => WVAppI (read_v R v, i)
      | VAppT (v, t) => WVAppT (read_v R v, t)
      | VPack (t', t, v) => WVPack (t', t, read_v R v)
      | VPackI (t', i, v) => WVPackI (t', i, read_v R v)
      | VFold (t, v) => WVFold (t, read_v R v)
      | VAscType (v, t) => read_v R v

infix  9 @^
fun R @^ v = read_v R v                               

fun collect_WVAppIT_rev t =
  let
    val self = collect_WVAppIT_rev
  in
    case t of
        WVAppI (t, i) =>
        let
          val (t, args) = self t
        in
          (t, inl i :: args)
        end
      | WVAppT (t, t') =>
        let
          val (t, args) = self t
        in
          (t, inr t' :: args)
        end
      | _ => (t, [])
  end
fun collect_WVAppIT t = mapSnd rev $ collect_WVAppIT_rev t

fun assert_fail msg = Impossible $ "Assert failed: " ^ msg
                             
fun assert_VAscType t =
  case t of
      VAscType a => a
    | _ => raise assert_fail "assert_VAscType"

fun assert_WVLabel t =
  case t of
      WVLabel a => a
    | _ => raise assert_fail "assert_WVLabel"

fun assert_WVPack t =
  case t of
      WVPack a => a
    | _ => raise assert_fail "assert_WVPack"

fun assert_WVPackI t =
  case t of
      WVPackI a => a
    | _ => raise assert_fail "assert_WVPackI"

fun assert_WVFold t =
  case t of
      WVFold a => a
    | _ => raise assert_fail "assert_WVFold"

fun WVInt n = WVConst $ ECInt n
fun assert_WVInt t =
  case t of
      WVConst (ECInt a) => a
    | _ => raise assert_fail "assert_WVInt"

fun WVNat n = WVConst $ ECNat n
fun assert_WVNat t =
  case t of
      WVConst (ECNat a) => a
    | _ => raise assert_fail "assert_WVNat"

val WVTT = WVConst ECTT
fun assert_WVTT t =
  case t of
      WVConst ECTT => ()
    | _ => raise assert_fail "assert_WVTT"

fun assert_HVCode t =
  case t of
      HVCode a => a
    | _ => raise assert_fail "assert_HVCode"

fun assert_HVPair t =
  case t of
      HVPair a => a
    | _ => raise assert_fail "assert_HVPair"

fun assert_HVInj t =
  case t of
      HVInj a => a
    | _ => raise assert_fail "assert_HVInj"

fun assert_HVArray t =
  case t of
      HVArray a => a
    | _ => raise assert_fail "assert_HVArray"

fun choose_update proj (b1, b2) new =
  case proj of
      ProjFst => (new, b2)
    | ProjSnd => (b1, new)

fun interp_prim_expr_bin_op opr (a, b) =
  case opr of
      PEBIntAdd => WVInt $ assert_WVInt a + assert_WVInt b
    | PEBIntMult => WVInt $ assert_WVInt a * assert_WVInt b
fun nat_add (a, b) = WVNat $ assert_WVNat a + assert_WVNat b

fun upd n v ls = update n (const_fun v) ls
                                                           
fun get_code (H, R) v =
  let
    val w = R @^ v
    val (w, itargs) = collect_WVAppIT w
    val l = assert_WVLabel w
    val c = assert_HVCode $ H @!! l
    val (itbinds, (_, I')) = unBind c
    val itbinds = unTeles itbinds
    val () = assert_b "#itargs = #itbinds" $ length itargs = length itbinds
    val I' = subst0_its_insts itargs I'
  in
    I'
  end
    
fun step (H, R, I) =
  case I of
      ISHalt _ => raise Impossible "can't step() on ISHalt"
    | ISJmp v =>
      let
      in
        (H, R, get_code (H, R) v)
      end
    | ISDummy _ => raise Impossible "can't step() on ISDummy"
    | ISCons bind =>
      let
        val (inst, I') = unBind bind
      in
        case inst of
            IUnOp (IUBr, r, v) =>
            let
              val (inj, w) = assert_HVInj $ must_find H $ assert_WVLabel $ R @!! r
            in
              case inj of
                  InjInl => (H, R @+ (r, w), I')
                | InjInr => (H, R @+ (r, w), get_code (H, R) $ unInner v)
            end
          | IUnOp (IUMov, rd, v) =>
            (H, R @+ (rd, R @^ unInner v), I')
          | IUnOp (IUUnfold, rd, v) =>
            let
              val (t, w) = assert_WVFold $ R @^ unInner v
            in
              (H, R @+ (rd, w), I')
            end
          | IBinOp (IBPrim opr, rd, rs, v) =>
            (H, R @+ (rd, interp_prim_expr_bin_op opr (R @!! rs, R @^ unInner v)), I')
          | IBinOp (IBNatAdd, rd, rs, v) =>
            (H, R @+ (rd, nat_add (R @!! rs, R @^ unInner v)), I')
          | IMallocPair (rd, (v1, v2)) =>
            let
              (* val (v1, t1) = assert_VAscType $ unInner v1 *)
              (* val (v2, t2) = assert_VAscType $ unInner v2 *)
              val l = fresh_label H
            in
              (H @+ (l, HVPair (WVUninit, WVUninit)), R @+ (rd, WVLabel l), I')
            end
          | ILd (rd, (rs, proj)) =>
            (H, R @+ (rd, flip choose proj $ assert_HVPair $ must_find H $ assert_WVLabel $ R @!! rs), I')
          | ISt ((rd, proj), rs) =>
            let
              val l = assert_WVLabel $ R @!! rd
              val pair = assert_HVPair $ H @!! l
              val pair = choose_update proj pair $ R @!! rs
            in
              (H @+ (l, HVPair pair), R, I')
            end
          | IUnpack (name, rd, v) =>
            let
              val (_, t, w) = assert_WVPack $ R @^ unOuter v
            in
              (H, R @+ (rd, w), subst0_t_insts t I')
            end
          | IUnpackI (name, rd, v) =>
            let
              val (_, i, w) = assert_WVPackI $ R @^ unOuter v
            in
              (H, R @+ (rd, w), subst0_i_insts i I')
            end
          | IBinOp (IBNew, rd, rs, v) =>
            let
              val n = assert_WVNat $ R @!! rs
              val l = fresh_label H
            in
              (H @+ (l, HVArray $ repeat n $ R @^ unInner v), R @+ (rd, WVLabel l), I')
            end
          | IBinOp (IBRead, rd, rs, v) =>
            let
              val l = assert_WVLabel $ R @!! rs
              val n = assert_WVNat $ R @^ unInner v
              val ls = assert_HVArray $ H @!! l
              val () = assert_b "step()/IRead/n<#ls" $ n < length ls
              val w = List.nth (ls, n)
            in
              (H, R @+ (rd, w), I')
            end
          | IBinOp (IBWrite, rd, rs, v) =>
            let
              val l = assert_WVLabel $ R @!! rd
              val n = assert_WVNat $ R @!! rs
              val v = R @^ unInner v
              val ls = assert_HVArray $ H @!! l
              val () = assert_b "step()/IWrite/n<#ls" $ n < length ls
            in
              (H @+ (l, HVArray $ upd n v ls), R @+ (rd, WVTT), I')
            end
          | IInj (rd, inj, v, t_other) =>
            let
              val l = fresh_label H
            in
              (H @+ (l, HVInj (inj, R @^ unInner v)), R @+ (rd, WVLabel l), I')
            end
          | IAscTime _ => (H, R, I')
      end

fun eval (P as (H, R, I)) =
  case I of
      ISHalt t => trace "" $ R @!! 1
    | _ => eval $ trace_noln "." $ step P
                
end