(* TiTAL typechecking *)

structure TiTALTypechecking = struct

fun tc_insts (ctx as (hctx, itctx as (ictx, tctx), rctx)) insts =
  case insts of
      ISHalt t =>
      let
        val t = tc_against_kind itctx (t, KType)
        val () = tc_v_against_ty ctx (VReg 1, t)
      in
        T1
      end
    | ISJmp v =>
      let
        val t = tc_v ctx v
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
              val () = tc_v_against_ty ctx (v, t2)
              val t = get_prim_expr_bin_op_res_ty opr
              val i = tc_insts (add_r (rd, t) ctx) I
            in
              i %+ T1
            end
          | IUnOp (IUBr, r, v) =>
            let
              val t = tc_v ctx $ VReg r
              val t_v = tc_v ctx v
              val (t1, t2) = assert_TSum t
              val (rctx', i2) = assert_TArrowTAL t_v
              val i1 = tc_insts (add_r (r, t1) ctx) I
              val () = is_sub_rctx itctx (rctx @+ (r, t2), rctx')
            in
              T1 %+ TMax (i1, i2)
            end
          | ILd (rd, (rs, proj)) =>
            let
              val t_rs = tc_v ctx $ VReg rs
              val pair = assert_TProdEx t_rs
              val (t, b) = choose pair proj
              val () = assert_b $ b
              val i = tc_insts (add_r (rd, t) ctx) I
            in
              i %+ T1
            end
          | IMallocPair (rd, (v1, v2)) =>
            let
              val t1 = tc_v ctx v1
              val t2 = tc_v ctx v2
              val t = TProdEx ((t1, false), (t2, false))
              val i = tc_insts (add_r (rd, t) ctx) I
            in
              i %+ T1
            end
          | IUnOp (IUMov, rd, v) =>
            let
              val t = tc_v ctx v
              val i = tc_insts (add_r (rd, t) ctx) I
            in
              i %+ T1
            end
          | ISt ((rd, proj), rs) =>
            let
              val t_rd = tc_v ctx $ VReg rd
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
              val t_v = tc_v ctx v
              val (k, (_, t)) = assert_TExists t_v
              val i = tc_insts (add_r (rd, t) $ add_kinding_full (fst name, k) ctx) I
            in
              i %+ T1
            end
      end

end
