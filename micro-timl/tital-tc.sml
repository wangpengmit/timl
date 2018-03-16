(* TiTAL typechecking *)

structure TiTALTypecheck = struct

open MicroTiMLTypecheck
open TiTAL
       
fun tc_w (ctx as (hctx, itctx as (ictx, tctx))) w =
  case w of
      WLabel l =>
      (case hctx @! l of
           SOME t => t
         | NONE => raise Impossible $ "unbound label " ^ str_int l
      )
    | WConst c => get_expr_const_type c
    | WUninit t => kc_against_kind itctx (t, KType)
    | WBuiltin t => kc_against_kind itctx (t, KType)
    | WNever t => kc_against_kind itctx (t, KType)

fun tc_v (ctx as (hctx, itctx as (ictx, tctx), rctx)) v =
  case v of
      VReg r =>
      (case rctx @! r of
           SOME t => t
         | NONE => raise Impossible $ "unbound reg " ^ str_int r
      )
    | VWord w => tc_w (hctx, itctx) w
    | VAppT (v, t) =>
      let
        val t_v = tc_v ctx v
        val t_v = whnf itctx t_v
        val (k, (_, t2)) = assert_TForall t_v
        val t = kc_against_kind itctx (t, k)
      in
        subst0_t_t t t2
      end
    | VPack (t_pack, t, v) =>
      let
        val t_pack = kc_against_kind itctx (t_pack, KType)
        val t_pack = whnf itctx t_pack
        val (k, (_, t')) = assert_TForall t_pack
        val t = kc_against_kind itctx (t, k)
        val t_v = subst0_t_t t t'
        val () = tc_v_against_ty ctx (v, t_v)
      in
        t_pack
      end
      
fun tc_insts (ctx as (hctx, itctx as (ictx, tctx), rctx)) insts =
  case insts of
      ISHalt t =>
      let
        val t = kc_against_kind itctx (t, KType)
        val () = tc_v_against_ty ctx (VReg 1, t)
      in
        T1
      end
    | ISJmp v =>
      let
        val t = tc_v ctx v
        val t = whnf itctx t
        val (rctx', i) = assert_TArrowTAL t
        val () = is_sub_rctx itctx (rctx, rctx')
      in
        i %+ T1
      end
    | ISCons bind =>
      let
        val (inst, I) = unBind bind
      in
        case inst of
            IBinOp (IBPrim opr, rd, rs, v) =>
            let
              val t1 = get_prim_expr_bin_op_arg1_ty opr
              val t2 = get_prim_expr_bin_op_arg2_ty opr
              val () = tc_v_against_ty ctx (VReg rs, t1)
              val () = tc_v_against_ty ctx (unInner v, t2)
              val t = get_prim_expr_bin_op_res_ty opr
              val i = tc_insts (add_r (rd, t) ctx) I
            in
              i %+ T1
            end
          | IUnOp (IUBr, r, v) =>
            let
              val t = tc_v ctx $ VReg r
              val t_v = tc_v ctx $ unInner v
              val t = whnf itctx t
              val (t1, t2) = assert_TSum t
              val t_v = whnf itctx t_v
              val (rctx', i2) = assert_TArrowTAL t_v
              val i1 = tc_insts (add_r (r, t1) ctx) I
              val () = is_sub_rctx itctx (rctx @+ (r, t2), rctx')
            in
              T1 %+ TMax (i1, i2)
            end
          | ILd (rd, (rs, proj)) =>
            let
              val t_rs = tc_v ctx $ VReg rs
              val t_rs = whnf itctx t_rs
              val pair = assert_TProdEx t_rs
              val (t, b) = choose pair proj
              val () = assert_b $ b
              val i = tc_insts (add_r (rd, t) ctx) I
            in
              i %+ T1
            end
          | IMallocPair (rd, (v1, v2)) =>
            let
              val t1 = tc_v ctx $ unInner v1
              val t2 = tc_v ctx $ unInner v2
              val t = TProdEx ((t1, false), (t2, false))
              val i = tc_insts (add_r (rd, t) ctx) I
            in
              i %+ T1
            end
          | IUnOp (IUMov, rd, v) =>
            let
              val t = tc_v ctx $ unInner v
              val i = tc_insts (add_r (rd, t) ctx) I
            in
              i %+ T1
            end
          | ISt ((rd, proj), rs) =>
            let
              val t_rd = tc_v ctx $ VReg rd
              val t_rd = whnf itctx t_rd
              val ((t1, b1), (t2, b2)) = assert_TProdEx t_rd
              val t_rs = choose (t1, t2) proj
              val () = tc_v_against_ty (VReg rs, t_rs)
              val (b1, b2) = choose_update (b1, b2) proj
              val t = ((t1, b1), (t2, b2))
              val i = tc_insts (add_r (rd, t) ctx) I
            in
              i %+ T1
            end
          | IUnpack (name, rd, v) =>
            let
              val t_v = tc_v ctx $ unOuter v
              val t_v = whnf itctx t_v
              val (k, (_, t)) = assert_TExists t_v
              val i = tc_insts (add_r (rd, t) $ add_kinding_full (binder2str name, k) ctx) I
            in
              i %+ T1
            end
      end

fun tc_hval hctx h =
  let
    val (itbinds, ((rctx, i), insts)) = unBind h
    val itbinds = unTeles itbinds
    val itctx as (ictx, tctx) =
        foldl
          (fn (bind, (ictx, tctx)) =>
              case bind of
                  inl (name, s) => ((binder2str name, is_wf_sort ictx $ unOuter s) :: ictx, tctx)
                | inr (name, k) => (ictx, (binder2str name, k) :: tctx)
          ) ([], []) itbinds
    val rctx = Rctx.map (fn t => kc_against_kind itctx (t, KType)) rctx
    val i = sc_against_sort ictx (i, STime)
    val i' = tc_insts (hctx, itctx, rctx) insts
    val () = check_prop ictx (i' %<= i)
  in
    ()
  end

fun tc_prog (H, I) =
  let
    val hctx = get_hctx H
    val () = app (fn (_, h) => tc_hval hctx h) H
    val i = tc_insts (hctx, ([], []), Rctx.empty) I
  in
    i
  end
    
fun tital_typecheck P =
  let
    val ret = runWriter (fn () => tc_prog P) ()
  in
    ret
  end

end
