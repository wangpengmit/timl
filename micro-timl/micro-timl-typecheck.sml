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
      (case nth ectx x of
           SOME t => (t, T0)
         | NONE => raise Error "unbound var"
      )
    | EConst c =>
      (get_expr_const_type c, T0)
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
        val (t1, i1) = tc (add_typing_iteh (name1, t1) ctx) e1
        val (t2, i2) = tc (add_typing_iteh (name2, t2) ctx) e2
        val () = is_eq_ty itctx (t1, t2)
      in
        (t1, i %+ Tmax (i1, i2))
      end
    | EAbs data =>
      let
        val (t1, (name, e)) = unEAbs data
        val () = kc_against_kd itctx (t1, KType)
        val (t2, i) = tc (add_typing_iteh (name, t1) ctx) e
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
        val () = kc_against_kd itctx (t, KType)
        val () = tc_against_ty_time (add_typing_iteh (name, t) ctx) (e, t, T0)
      in
        (t, T0)
      end
    | EAbsT data =>
      let
        val (k, (name, e)) = unEAbsT data
        val () = assert "EAbsT" $ is_value e
        val t = tc_against_time (add_kinding_iteh (name, k) ctx) (e, T0)
      in
        (MakeTForall (k, t), T0)
      end
    | EAppT (e, t1) =>
      let
        val (t', i) = tc ctx e
        val (_, (_, t)) = case t' of
                              TQuan (Forall, data) => unTQuan data
                            | _ => raise Error "EAppT"
        val () = kc_against_kd itctx (t1, KType)
      in
        (subst0_t_t t1 t, i)
      end
    | EAbsI data =>
      let
        val (s, (name, e)) = unEAbsI data
        val () = is_wf_sort ictx s
        val () = assert "EAbsI" $ is_value e
        val t = tc_against_time (add_sorting_iteh (name, k) ctx) (e, T0)
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
        
