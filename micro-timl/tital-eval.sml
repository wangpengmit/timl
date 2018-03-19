(* TiTAL evaluator (i.e. simulator) *)

structure TiTALEval = struct

(* word values *)
datatype 'ty wordv =
         WVLabel of label
         | WVConst of Operators.expr_const
         | WVUninit of 'ty
         (* | WVBuiltin of 'ty *)
         (* | WVNever of 'ty *)
         | WVAppT of ('idx, 'ty) value * 'ty
         | WVAppI of ('idx, 'ty) value * 'idx
         | WVPack of 'ty * 'ty * ('idx, 'ty) value
         | WVPackI of 'ty * 'idx * ('idx, 'ty) value
         | WVFold of 'ty * ('idx, 'ty) value

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
         | WUninit t => WVUninit t
         | WBuiltin => raise Impossible "WBuiltin is not a legal word value"
         | WNever => raise Impossible "WNever is not a legal word value"
      )
      | VAppI (v, i) => WVAppI (read_v R v, i)
      | VAppT (v, t) => WVAppT (read_v R v, t)
      | VPack (t', t, v) => WVPack (t', t, read_v R v)
      | VPackI (t', i, v) => WVPackI (t', i, read_v R v)
      | VFold (t, v) => WVFold (t, read_v R v)

infix  9 @^
fun R @^ v = read_v R v                               

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
                      | inr v => (subst_i_insts (IDepth ni, TDepth (nt-1)) (nt-1) v b, (ni, nt-1))
                ) (b, (len_i, len_t)) itargs
  in
    b
  end
                    
fun get_code (H, R) v =
  let
    val w = R @^ v
    val (w, itargs) = collect_WVAppIT w
    val l = assert_WVLabel w
    val c = assert_HVCode $ H @!! l
    val (itbinds, (_, I')) = unBind h
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
            IBinOp (IBPrim opr, rd, rs, v) =>
            (H, R @+ (rd, interp_prim_expr_bin_op opr (R @!! rs, R @^ v)), I')
          | IUnOp (IUBr, r, v) =>
            (case assert_HVInj $ must_find H $ assert_WVLabel $ R @!! r of
                inl w => (H, R @+ (r, w), I')
              | inr w => (H, R @+ (r, w), get_code (H, R) v))
          | ILd (rd, (rs, proj)) =>
            (H, R @+ (rd, flip choose proj $ assert_HVPair $ must_find H $ assert_WVLabel $ R @!! rs), I')
          | IMallocPair (rd, (v1, v2)) =>
            let
              val (v1, t1) = assert_VAscType v1
              val (v2, t2) = assert_VAscType v2
              val l = fresh_label H
            in
              (H @+ (l, HVPair (WVUninit t1, WVUninit t2)), R @+ (rd, WVLabel l), I')
            end
          | IUnOp (IUMov, rd, v) =>
            (H, R @+ (rd, R @^ v), I')
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
              val (_, t, w) = assert_VWPack $ R @^ v
            in
              (H, R @+ (rd, w), subst0_t_insts t I')
            end
      end


end
