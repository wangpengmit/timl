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
