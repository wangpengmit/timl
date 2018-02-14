(* Closure Conversion *)

structure CC = struct

fun cc_t t =
  case t of
      TArrow _ =>
      cc_t_arrow t
    | TQuan (Forall, _) =>
      cc_t_arrow t
    | TQuanI (Forall, _) =>
      cc_t_arrow t
    | TVar _ => t
    | TConst _ => t
    | TBinOp (opr, t1, t2) => TBinOp (opr, cc_t t1, cc_t t2)
    | _ => raise Unimpl

and cc_t_arrow t =
    let
      val (binds, t) = open_collect_Forall_ForallI t
      val (t1, i, t2) = assert_TArrow t
      val t1 = cc_t t1
      val t2 = cc_t t2
      val alpha = fresh_tvar ()
      val t = TArrow (TProd (TV alpha, t1), i, t2)
      val t = close_combine_Forall_ForallI (binds, t)
      val t = TProd (t, TV alpha)
      val t = TExists $ close_t_t_anno ((alpha, "'a", KType), t)
    in
      t
    end

infixr 0 %$
fun a %$ b = EApp (a, b)

fun cc e =
    case e of
        EBinOp (EBApp, e1, e2) =>
        let
          val (e1, itargs) = collect_EAppIT e1
          (* val (e1, t_e1) = assert_EAscType e1 *)
          (* val t_e1 = cc_t t_e1 *)
          (* val (_, t_pair) = assert_TExists t_e1 *)
          (* val (t_code, _) = assert_TProd t_pair *)
          val gamma = fresh_tvar ()
          val z = fresh_evar ()
          val z_code = fresh_evar ()
          val z_env = fresh_evar ()
          val e = EAppIT (e1, map (map_inr cc_t) itargs) %$ EPair (EV z_env, cc e2)
          val e = ELetManyClose ([(z_code, "z_code", EFst $ EV z), (z_env, "z_env", ESnd $ EV z)], e)
          val e = EUnpackClose (cc e1, (gamma, "'c"), (z, "z"), e)
        in
          e
        end
      | EAbsT _ => cc_abs e
      | EAbsI _ => cc_abs e
      | EAbs _ => cc_abs e
      | ERec _ => cc_abs e
      | _ => raise Umimpl

and cc_abs e_all =
    let
      val (binds, e) = open_collect_EAbsIT e_all
    in
      case e of
          ERec bind => cc_ERec e_all binds bind
        | EAbs bind => cc_EAbs e_all binds bind
    end

and cc_ERec e_all outer_binds bind =
    let
      val (t_x, (name_x, e)) = unBindAnnoName bind
      val x = fresh_evar ()
      val e = open0_e_e x e
      val (inner_binds, e) = open_collect_EAbsIT e
      val (t_z, (name_z, e)) = assert_EAbs e
      val z = fresh_evar ()
      val e = open0_e_e z e
      val (_, t_arrow) = assert_TForallIT_open t_x
      val (_, i, _) = assert_TArrow t_arrow
      val (ys, sigmas) = unzip $ free_vars_with_anno e_all
      val betas = free_tvars e_all
      val t_env = cc_t $ TRecord sigmas
      val t_z = cc_t t_z
      val t_arrow = TArrow (TProd (t_env, t_z), i, TUnit)
      val t_rawcode = TForallITClose (betas @ outer_binds @ inner_binds, t_arrow)
      val t_code = TForallITClose (outer_binds @ inner_binds, t_arrow)
      val z_env = fresh_evar ()
      val len_ys = length ys
      val ys_defs = mapi (fn (i, y) => (y, "y" ^ str_int (1+i), ERecordProj (len_ys, i) $ EV z_env)) ys
      val e_x = EPack (cc_t t_x, t_env, EPair (EV z_code, EV z_env))
      val e = ELetManyClose ((x, "x", e_x) :: ys_defs, cc e)
      val e = EAbsPairClose ((z_env, "z_env", t_env), (z, "z", t_z), e)
      val z_code = fresh_evar ()
      val e = ERec $ close0_e_e_anno ((z_code, "z_code", t_code), e)
      val v_code = EAbsITClose (betas @ outer_binds, e)
      val v_env = ERecord ys
      val e = EPack (cc_t $ TForallIT (outer_binds, t_x), t_env, EPair (EAppIT (v_code, betas), v_env))
    in
      e
    end

end
