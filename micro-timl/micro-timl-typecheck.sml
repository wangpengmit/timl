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
      
fun tc (ctx as ((iectx as (ictx, ectx)), hctx)) e =
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
        (TAppIT (subst0 t t1) args, i)
      end
    | EBinOp (EBPrim opr, e1, e2) =>
      let
        val (t1, i1) = tc ctx e1
        val () = is_eq_ty ictx t1 (get_prim_expr_bin_op_arg1_ty opr)
        val (t2, i2) = tc ctx e2
        val () = is_eq_ty ictx t2 (get_prim_expr_bin_op_arg2_ty opr)
      in
        (get_prim_expr_bin_op_res_ty opr, i1 %+ i2)
      end
    | EBinOp (EBApp, e1, e2) =>
      let
        val (t, i1) = tc ctx e1
        val (t1, i, t2) = case t of
                              TArrow data => data
                            | _ => "EApp"
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
                  | _ => "ENew"
        val (t, j2) = tc ctx e2
      in
        (TArr (t, i), j1 %+ j2)
      end
    | EBinOp (EBRead, e1, e2) =>
      let
        val (t1, j1) = tc ctx e1
        val (t, i1) = case t1 of
                    TArr data => data
                  | _ => "ERead 1"
        val (t2, j2) = tc ctx e2
        val i2 = case t2 of
                     TNat i => i
                   | _ => "ERead 2"
        val () = check_prop ictx (i2 %< i1)
      in
        (t, j1 %+ j2)
      end
    | EBinOp (EBNatAdd, e1, e2) =>
      let
        val (t1, j1) = tc ctx e1
        val i1 = case t1 of
                    TNat i => i
                  | _ => "ENatAdd 1"
        val (t2, j2) = tc ctx e2
        val i2 = case t2 of
                     TNat i => i
                   | _ => "ENatAdd 2"
      in
        (TNat (i1 %+ i2), j1 %+ j2)
      end
    | EBinOp (EBWrite, e1, e2, e3) =>
      let
        val (t1, j1) = tc ctx e1
        val (t, i1) = case t1 of
                    TArr data => data
                  | _ => "ERead 1"
        val (t2, j2) = tc ctx e2
        val i2 = case t2 of
                     TNat i => i
                   | _ => "ERead 2"
        val () = check_prop ictx (i2 %< i1)
        val j3 = tc_against_ty ctx (e3, t)
      in
        (TUnit, j1 %+ j2 %+ j3)
      end
