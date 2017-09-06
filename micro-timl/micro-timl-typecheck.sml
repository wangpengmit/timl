structure MicroTiMLTypecheck = struct

fun get_ty_const_kind c =
  case c of
      TCUnit => KType
    | TCInt => KType
    | TCEmpty => KType

fun get_ty_bin_op_arg1_kind opr =
  case opr of
      TBProd => KType
    | TBSum => KType
                 
fun get_ty_bin_op_arg2_kind opr =
  case opr of
      TBProd => KType
    | TBSum => KType
                 
fun get_ty_bin_op_res_kind opr =
  case opr of
      TBProd => KType
    | TBSum => KType
                 
fun kc (ctx as (ictx, tctx)) t =
  case t of
      TVar x =>
      (case nth_error tctx x of
           SOME k => k
         | NONE => raise Error "unbound type variable"
      )
    | TConst c => get_ty_const_kind c
    | TBinOp (opr, t1, t2) =>
      let
        val () = kc_against_kind ctx (t1, get_ty_bin_op_arg1_kind opr)
        val () = kc_against_kind ctx (t2, get_ty_bin_op_arg2_kind opr)
      in
        get_ty_bin_op_res_kind opr
      end
    | TArrow (t1, i, t2) =>
      let
        val () = kc_against_kind ctx (t1, KType)
        val () = sc_against_sort ictx (i, STime)
        val () = kc_against_kind ctx (t2, KType)
      in
        KType
      end
    | TAbsI data =>
      let
        val (b, (name, t)) = unTAbsI data
        val k = kc (add_sorting_it (name, Basic b) ctx) t
      in
        KArrow (b, k)
      end
    | TAppI (t, i) =>
      let
        val k' = kc ctx t
        val (b, k) = case k' of
                         KArrow data => data
                       | _ => raise Error "TAppI"
        val () = sc_against_sort ictx (i, Basic b)
      in
        k
      end
    | TAbsT data =>
      let
        val (k1, (name, t)) = unTAbsT data
        val k2 = kc (add_kinding_it (name, k1) ctx) t
      in
        KArrowT (k1, k2)
      end
    | TAppT (t1, t2) =>
      let
        val k' = kc ctx t1
        val (k1, k2) = case k' of
                         KArrowT data => data
                       | _ => raise Error "TAppT"
        val () = kc_against_kind ictx (t2, k1)
      in
        k2
      end
    | TQuanI (_, data) =>
      let
        val (s, (name, t)) = unTQuanI data
        val () = kc_against_kind (add_sorting_it (name, s) ctx) (t, KType)
      in
        KType
      end
    | TQuan (_, data) =>
      let
        val (k, (name, t)) = unTQuan data
        val () = kc_against_kind (add_kinding_it (name, k) ctx) (t, KType)
      in
        KType
      end
    | TRec data =>
      let
        val (k, (name, t)) = unTRec data
        val () = kc_against_kind (add_kinding_it (name, k) ctx) (t, k)
      in
        k
      end
    | TNat i =>
      let
        val () = sc_against_sort ictx (i, SNat)
      in
        KType
      end
    | TArr (t, i) =>
      let
        val () = kc_against_kind ctx (t, KType)
        val () = sc_against_sort ictx (i, SNat)
      in
        KType
      end
      
fun get_expr_const_type c =
  case c of
      ECTT => TUnit
    | ECNat n => TNat $ INat n
    | ECInt _ => TInt

fun get_prim_expr_bin_opr_arg1_ty opr =
  case opr of
      PEBIntAdd => TInt
    | PEBIntMult => TInt
      
fun get_prim_expr_bin_opr_arg2_ty opr =
  case opr of
      PEBIntAdd => TInt
    | PEBIntMult => TInt
      
fun get_prim_expr_bin_opr_res_ty opr =
  case opr of
      PEBIntAdd => TInt
    | PEBIntMult => TInt
      
fun tc (ctx as ((itectx as (ictx, tctx, ectx)), hctx)) e =
  case e of
      Evar x =>
      (case nth_error ectx x of
           SOME t => (t, T0)
         | NONE => raise Error "unbound term variable"
      )
    | EConst c => (get_expr_const_type c, T0)
    | ELoc l =>
      (case get m l of
           SOME (t, i) => (MakeTArr (t, i), T0)
         | NONE => raise Error "unbound location"
      )
    | EUnOp (EUProj proj, e) =>
      let
        val (t, i) = tc ctx e
        val (t1, t2) = case t of
                           TBinOp (TBProd, t1, t2) => (t1, t2)
                         | _ => raise Error "EProj"
        fun choose (t1, t2) proj =
          case proj of
              ProjFst => t1
            | ProjSnd => t2
      in
        (choose (t1, t2) proj, i)
      end
    | EUnOp (EUInj (inj, t'), e) =>
      let
        val (t, i) = tc ctx e
        fun inject (t, t') inj =
          case inj of
              InjInl => (t, t')
            | InjInr => (t', t)
      in
        (TSum $ inject (t, t') inj, i)
      end
    | EUnOp (EUFold t', e) =>
      let
        val (t, args) = collect_TAppI_TAppT t'
        val (k, (_, t1)) = case t of
                               TRec data => unTRec data
                             | _ => raise Error "EFold"
        val i = tc_against_ty ctx (e, TAppIT (subst0 t t1) args) 
      in
        (t', i)
      end
    | EUnOp (EUUnfold, e) =>
      let
        val (t', i) = tc ctx e
        val (t, args) = collect_TAppI_TAppT t'
        val (k, (_, t1)) = case t of
                               TRec data => unTRec data
                             | _ => raise Error "EUnfold"
      in
        (TAppIT (subst0_t_t t t1) args, i)
      end
    | EBinOp (EBPrim opr, e1, e2) =>
      let
        val (t1, i1) = tc ctx e1
        val () = is_eq_ty itctx (t1, get_prim_expr_bin_op_arg1_ty opr)
        val (t2, i2) = tc ctx e2
        val () = is_eq_ty itctx (t2, get_prim_expr_bin_op_arg2_ty opr)
      in
        (get_prim_expr_bin_op_res_ty opr, i1 %+ i2)
      end
    | EBinOp (EBApp, e1, e2) =>
      let
        val (t, i1) = tc ctx e1
        val (t1, i, t2) = case t of
                              TArrow data => data
                            | _ => raise Error "EApp"
        val i2 = tc_against_ty ctx (e2, t1)
      in
        (t2, i1 %+ i2 %+ T1 %+ i)
      end
    | EBinOp (EBPair, e1, e2) =>
      let
        val (t1, i1) = tc ctx e1
        val (t2, i2) = tc ctx e2
      in
        (TProd (t1, t2), i1 %+ i2)
      end
    | EBinOp (EBNew, e1, e2) =>
      let
        val (t1, j1) = tc ctx e1
        val i = case t1 of
                    TNat i => i
                  | _ => raise Error "ENew"
        val (t, j2) = tc ctx e2
      in
        (TArr (t, i), j1 %+ j2)
      end
    | EBinOp (EBRead, e1, e2) =>
      let
        val (t1, j1) = tc ctx e1
        val (t, i1) = case t1 of
                    TArr data => data
                  | _ => raise Error "ERead 1"
        val (t2, j2) = tc ctx e2
        val i2 = case t2 of
                     TNat i => i
                   | _ => raise Error "ERead 2"
        val () = check_prop ictx (i2 %< i1)
      in
        (t, j1 %+ j2)
      end
    | EBinOp (EBNatAdd, e1, e2) =>
      let
        val (t1, j1) = tc ctx e1
        val i1 = case t1 of
                    TNat i => i
                  | _ => raise Error "ENatAdd 1"
        val (t2, j2) = tc ctx e2
        val i2 = case t2 of
                     TNat i => i
                   | _ => raise Error "ENatAdd 2"
      in
        (TNat (i1 %+ i2), j1 %+ j2)
      end
    | EWrite (e1, e2, e3) =>
      let
        val (t1, j1) = tc ctx e1
        val (t, i1) = case t1 of
                    TArr data => data
                  | _ => raise Error "ERead 1"
        val (t2, j2) = tc ctx e2
        val i2 = case t2 of
                     TNat i => i
                   | _ => raise Error "ERead 2"
        val () = check_prop ictx (i2 %< i1)
        val j3 = tc_against_ty ctx (e3, t)
      in
        (TUnit, j1 %+ j2 %+ j3)
      end
    | ECase data =>
      let
        val (e, (name1, e1), (name2, e2)) = unECase data
        val (t, i) = tc ctx e
        val (t1, t2) = case e of
                           TBinOp (TBSum, t1, t2) => (t1, t2)
                         | _ => raise Error "ECase"
        val (t1, i1) = tc (add_typing_full (name1, t1) ctx) e1
        val (t2, i2) = tc (add_typing_full (name2, t2) ctx) e2
        val () = is_eq_ty itctx (t1, t2)
      in
        (t1, i %+ Tmax (i1, i2))
      end
    | EAbs data =>
      let
        val (t1, (name, e)) = unEAbs data
        val () = kc_against_kind itctx (t1, KType)
        val (t2, i) = tc (add_typing_full (name, t1) ctx) e
      in
        (TArrow (t1, i, t2), T0)
      end
    | ERec data =>
      let
        val (t, (name, e)) = unERec data
        val (_, e') = collect_EAbsI_EAbsT e
        val () = case e' of
                     EAbs _ => ()
                   | _ => raise Error "ERec"
        val () = kc_against_kind itctx (t, KType)
        val () = tc_against_ty_time (add_typing_full (name, t) ctx) (e, t, T0)
      in
        (t, T0)
      end
    | EAbsT data =>
      let
        val (k, (name, e)) = unEAbsT data
        val () = assert "EAbsT" $ is_value e
        val t = tc_against_time (add_kinding_full (name, k) ctx) (e, T0)
      in
        (MakeTForall (k, t), T0)
      end
    | EAppT (e, t1) =>
      let
        val (t', i) = tc ctx e
        val (_, (_, t)) = case t' of
                              TQuan (Forall, data) => unTQuan data
                            | _ => raise Error "EAppT"
        val () = kc_against_kind itctx (t1, KType)
      in
        (subst0_t_t t1 t, i)
      end
    | EAbsI data =>
      let
        val (s, (name, e)) = unEAbsI data
        val () = is_wf_sort ictx s
        val () = assert "EAbsI" $ is_value e
        val t = tc_against_time (add_sorting_full (name, k) ctx) (e, T0)
      in
        (MakeTForallI (s, t), T0)
      end
    | EAppI (e, i) =>
      let
        val (t', j) = tc ctx e
        val (_, (_, t)) = case t' of
                              TQuanI (Forall, data) => unTQuanI data
                            | _ => raise Error "EAppT"
        val () = sc_against_sort ictx (i, s)
      in
        (subst0_i_t i t, j)
      end
    | EPack (t', t1, e) =>
      let
        val () = kc_against_kind itctx (t', KType)
        val (k, (_, t)) = case t' of
                              TQuan (Exists, data) => UnTQuan data
                            | _ => raise Error "EPack"
        val () = kc_against_kind itctx (t1, k)
        val i = tc_against_ty ctx (e, subst0_t_t t1 t)
      in
        (t', i)
      end
    | EUnpack data =>
      let
        val (e1, (tname, ename, e2)) = unEUnpack data
        val (t', i1) = tc ctx e1
        val (k, (_, t)) = case t' of
                              TQuan (Exists, data) => UnTQuan data
                            | _ => raise Error "EUnpack"
        val (t2, i2) = tc (add_typing_full (ename, t) $ add_kinding_full (tname, k) ctx) e2
        val t2 = forget0_t_t t2
      in
        (t2, i1 %+ i2)
      end
    | EPackI (t', i, e) =>
      let
        val () = kc_against_kind itctx (t', KType)
        val (s, (_, t)) = case t' of
                              TQuanI (Exists, data) => UnTQuanI data
                            | _ => raise Error "EPackI"
        val () = sc_against_sort ictx (i, s)
        val j = tc_against_ty ctx (e, subst0_i_t i t)
      in
        (t', j)
      end
    | EUnpackI data =>
      let
        val (e1, (iname, ename, e2)) = unEUnpack data
        val (t', i1) = tc ctx e1
        val (s, (_, t)) = case t' of
                              TQuanI (Exists, data) => UnTQuanI data
                            | _ => raise Error "EUnpackI"
        val (t2, i2) = tc (add_typing_full (ename, t) $ add_sorting_full (iname, s) ctx) e2
        val t2 = forget0_i_t t2
        val i2 = forget0_i_i i2
      in
        (t2, i1 %+ i2)
      end
    | EAscTime (e, i2) =>
      let
        val (t, i1) = tc ctx e
        val () = sc_against_sort (i2, STime)
        val () = check_prop ictx (i1 %<= i2)
      in
        (t, i2)
      end
    | EAscType (e, t2) =>
      let
        val (t1, i) = tc ctx e
        val () = kc_against_kind (t2, KType)
        val () = is_eq_ty itctx (t1, t2)
      in
        (t2, i)
      end
    | ENever t => (t, T0)
    | EBuiltin t => (t, T0)
    | ELet data =>
      let
        val (e1, (name, e2)) = unELet data
        val (t1, i1) = tc ctx e1
        val (t2, i2) = tc (add_typing_full (name, t1) ctx) e2
      in
        (t2, i1 %+ i2)
      end
    | _ => raise Impossible "tc"

end
