(* TiTAL typechecking *)

structure TiTALTypecheck = struct

open MicroTiMLTypecheck
open CompilerUtil
open TiTAL

infixr 0 $

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

infixr 5 @::
infixr 5 @@
infix  6 @+
infix  9 @!

fun assert_TProdEx t =
  case t of
      TProdEx a => a
    | _ => raise assert_fail "assert_TProdEx"
fun assert_TArrowTAL t =
  case t of
      TArrowTAL a => a
    | _ => raise assert_fail "assert_TArrowTAL"
fun assert_TArr t =
  case t of
      TArr a => a
    | _ => raise assert_fail $ "assert_TArr; got: " ^ (ExportPP.pp_t_to_string NONE $ ExportPP.export_t NONE ([], []) t)
fun assert_TNat t =
  case t of
      TNat a => a
    | _ => raise assert_fail $ "assert_TNat; got: " ^ (ExportPP.pp_t_to_string NONE $ ExportPP.export_t NONE ([], []) t)

fun add_sorting_full new (hctx, (ictx, tctx), rctx) = (hctx, (new :: ictx, tctx), Rctx.map (* lazy_ *)shift01_i_t rctx)
fun add_kinding_full new (hctx, (ictx, tctx), rctx) = (hctx, (ictx, new :: tctx), Rctx.map (* lazy_ *)shift01_t_t rctx)
fun add_r p (hctx, itctx, rctx) = (hctx, itctx, rctx @+ p)

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

fun is_sub_rctx ctx (rctx, rctx_abs) =
  assert_sub_map (fn () => Impossible "is_sub_rctx()") (fn (t_abs, t) => is_eq_ty ctx (t, t_abs)) (rctx_abs, rctx)
  
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
        val ((_, k), t2) = assert_TForall t_v
        val t = kc_against_kind itctx (t, k)
      in
        subst0_t_t t t2
      end
    | VAppI (v, i) =>
      let
        val t_v = tc_v ctx v
        val t_v = whnf itctx t_v
        val ((_, s), t2) = assert_TForallI t_v
        val s = sc_against_sort ictx (i, s)
      in
        subst0_i_t i t2
      end
    | VPack (t_pack, t, v) =>
      let
        val t_pack = kc_against_kind itctx (t_pack, KType)
        val t_pack = whnf itctx t_pack
        val ((_, k), t') = assert_TForall t_pack
        val t = kc_against_kind itctx (t, k)
        val t_v = subst0_t_t t t'
        val () = tc_v_against_ty ctx (v, t_v)
      in
        t_pack
      end
    | VPackI (t_pack, i, v) =>
      let
        val t_pack = kc_against_kind itctx (t_pack, KType)
        val t_pack = whnf itctx t_pack
        val ((_, s), t') = assert_TForallI t_pack
        val i = sc_against_sort ictx (i, s)
        val t_v = subst0_i_t i t'
        val () = tc_v_against_ty ctx (v, t_v)
      in
        t_pack
      end
    | VFold (t_fold, v) =>
      let
        val t_fold = kc_against_kind itctx (t_fold, KType)
        val t_fold = whnf itctx t_fold
        val (t, args) = collect_TAppIT t_fold
        val ((_, k), t1) = assert_TRec t
        val t = TAppITs (subst0_t_t t t1) args
        val () = tc_v_against_ty ctx (v, t) 
      in
        t_fold
      end

and tc_v_against_ty (ctx as (hctx, itctx as (ictx, tctx), rctx)) (v, t) =
    let
      val t' = tc_v ctx v
      val () = is_eq_ty (ictx, tctx) (t', t)
    in
      ()
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
    | ISDummy _ => T0
    | ISCons bind =>
      let
        val (inst, I) = unBind bind
      in
        case inst of
            IUnOp (IUBr, r, v) =>
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
              T1 %+ IMax (i1, i2)
            end
          | IUnOp (IUMov, rd, v) =>
            let
              val t = tc_v ctx $ unInner v
              val i = tc_insts (add_r (rd, t) ctx) I
            in
              i %+ T1
            end
          | IUnOp (IUUnfold, rd, v) =>
            let
              val t_v = tc_v ctx $ unInner v
              val t_v = whnf itctx t_v
              val (t, args) = collect_TAppIT t_v
              val ((_, k), t1) = assert_TRec t
              val t = TAppITs (subst0_t_t t t1) args
              val i = tc_insts (add_r (rd, t) ctx) I
            in
              i %+ T1
            end
          | IBinOp (IBPrim opr, rd, rs, v) =>
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
          | IBinOp (IBNatAdd, rd, rs, v) =>
            let
              val t1 = tc_v ctx $ VReg rs
              val i1 = assert_TNat t1
              val t2 = tc_v ctx $ unInner v
              val i2 = assert_TNat t2
              val t = TNat $ i1 %+ i2
              val i = tc_insts (add_r (rd, t) ctx) I
            in
              i %+ T1
            end
          | IBinOp (IBNew, rd, rs, v) =>
            let
              val t1 = tc_v ctx $ VReg rs
              val i1 = assert_TNat t1
              val t2 = tc_v ctx $ unInner v
              val t = TArr (t2, i1)
              val i = tc_insts (add_r (rd, t) ctx) I
            in
              i %+ T1
            end
          | IBinOp (IBRead, rd, rs, v) =>
            let
              val t1 = tc_v ctx $ VReg rs
              val (t, i1) = assert_TArr t1
              val t2 = tc_v ctx $ unInner v
              val i2 = assert_TNat t2
              val () = check_prop ictx (i2 %< i1)
              val i = tc_insts (add_r (rd, t) ctx) I
            in
              i %+ T1
            end
          | IBinOp (IBWrite, rd, rs, v) =>
            let
              val t1 = tc_v ctx $ VReg rd
              val (t1, i1) = assert_TArr t1
              val t2 = tc_v ctx $ VReg rs
              val i2 = assert_TNat t2
              val () = check_prop ictx (i2 %< i1)
              val () = tc_v_against_ty ctx (unInner v, t1)
              val t = TUnit
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
          | ILd (rd, (rs, proj)) =>
            let
              val t_rs = tc_v ctx $ VReg rs
              val t_rs = whnf itctx t_rs
              val pair = assert_TProdEx t_rs
              val (t, b) = choose pair proj
              val () = assert_b "tc()/ILd" $ b
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
              val () = tc_v_against_ty ctx (VReg rs, t_rs)
              val (b1, b2) = choose_update (b1, b2) proj
              val t = TProdEx ((t1, b1), (t2, b2))
              val i = tc_insts (add_r (rd, t) ctx) I
            in
              i %+ T1
            end
          | IUnpack (name, rd, v) =>
            let
              val t_v = tc_v ctx $ unOuter v
              val t_v = whnf itctx t_v
              val ((_, k), t) = assert_TExists t_v
              val i = tc_insts (add_r (rd, t) $ add_kinding_full (binder2str name, k) ctx) I
            in
              i %+ T1
            end
          | IUnpackI (name, rd, v) =>
            let
              val t_v = tc_v ctx $ unOuter v
              val t_v = whnf itctx t_v
              val ((_, s), t) = assert_TExistsI t_v
              val name = binder2str name
              val i = tc_insts (add_r (rd, t) $ add_sorting_full (name, s) ctx) I
              val i = forget01_i_i i
                       handle ForgetError (r, m) => raise ForgetError (r, m ^ " when forgetting time: " ^ (ToString.SN.strn_i $ ExportPP.export_i (name :: map fst ictx) i))
            in
              i %+ T1
            end
          | IInj (rd, inj, v, t_other) =>
            let
              val t_other = kc_against_kind itctx (unInner t_other, KType)
              val t = tc_v ctx $ unInner v
              val t = TSum $ choose_pair_inj (t, t_other) inj
              val i = tc_insts (add_r (rd, t) ctx) I
            in
              i %+ T1
            end
          | IAscTime i =>
            let
              val i = sc_against_sort ictx (unInner i, STime)
              val i' = tc_insts ctx I
              val () = check_prop ictx (i' %<= i)
            in
              i
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
    fun get_hval_type h =
      let
        val (itbinds, ((rctx, i), _)) = unBind h
        val itbinds = unTeles itbinds
        val itbinds = map (map_inl_inr (mapPair' unBinderName unOuter) (mapFst unBinderName)) itbinds
        val t = TForallITs (itbinds, TArrowTAL (rctx, i))
      in
        t
      end
    fun get_hctx H = RctxUtil.fromList $ map (mapPair' fst get_hval_type) H
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
