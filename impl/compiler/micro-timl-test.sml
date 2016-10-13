structure MicroTiMLTest =
struct
  open Util

  infixr 0 $

  structure DerivTransformers = DerivTransformers(
  struct
    type time_type = int

    val Time0 = 0
    val Time1 = 1

    val str_time = str_int
  end)

  fun main(prog_name : string, args : string list) : int =
    let
    in
      0
    end
  (*open Util
  open MicroTiML

  fun test_len () =
    let
      val list_cstr = CstrRec (KdArrow (KdProper, KdArrow (KdNat, KdProper)), CstrAbs (KdProper, CstrAbs (KdNat, CstrSum (CstrExists (KdSubset (KdUnit, PrBinRel (PrRelEq, CstrVar 1, CstrNat 0)), CstrTypeUnit), CstrExists (KdSubset (KdNat, PrBinRel (PrRelEq, CstrVar 1, CstrBinOp (CstrBopAdd, CstrVar 0, CstrNat 1))), CstrProd (CstrVar 2, CstrApp (CstrApp (CstrVar 3, CstrVar 2), CstrVar 0)))))))
      val c1 = CstrExists (KdSubset (KdUnit, PrBinRel (PrRelEq, CstrVar 1, CstrNat 0)), CstrTypeUnit)
      val ct1 = [BdKind KdNat, BdKind KdProper, BdKind (KdArrow (KdProper, KdArrow (KdNat, KdProper)))]
      val d1 = KdDerivExists ((ct1, c1, KdProper), KdWfDerivSubset ((ct1, KdSubset (KdUnit, PrBinRel (PrRelEq, CstrVar 1, CstrNat 0))), KdWfDerivUnit (ct1, KdUnit), PrWfDerivBinRel ((BdKind KdUnit :: ct1, PrBinRel (PrRelEq, CstrVar 1, CstrNat 0)), KdDerivVar (BdKind KdUnit :: ct1, CstrVar 1, KdNat), KdDerivNat (BdKind KdUnit :: ct1, CstrNat 0, KdNat))), KdDerivTypeUnit (BdKind (KdSubset (KdUnit, PrBinRel (PrRelEq, CstrVar 1, CstrNat 0))) :: ct1, CstrTypeUnit, KdProper))
      val c2 = CstrExists (KdSubset (KdNat, PrBinRel (PrRelEq, CstrVar 1, CstrBinOp (CstrBopAdd, CstrVar 0, CstrNat 1))), CstrProd (CstrVar 2, CstrApp (CstrApp (CstrVar 3, CstrVar 2), CstrVar 0)))
      val ct2 = ct1
      val d2 = KdDerivExists ((ct2, c2, KdProper), KdWfDerivSubset ((ct2, KdSubset (KdNat, PrBinRel (PrRelEq, CstrVar 1, CstrBinOp (CstrBopAdd, CstrVar 0, CstrNat 1)))), KdWfDerivNat (ct2, KdNat), PrWfDerivBinRel ((BdKind KdNat :: ct2, PrBinRel (PrRelEq, CstrVar 1, CstrBinOp (CstrBopAdd, CstrVar 0, CstrNat 1))), KdDerivVar (BdKind KdNat :: ct2, CstrVar 1, KdNat), KdDerivBinOp ((BdKind KdNat :: ct2, CstrBinOp (CstrBopAdd, CstrVar 0, CstrNat 1), KdNat), KdDerivVar (BdKind KdNat :: ct2, CstrVar 0, KdNat), KdDerivNat (BdKind KdNat :: ct2, CstrNat 1, KdNat)))), KdDerivProd ((BdKind (KdSubset (KdNat, PrBinRel (PrRelEq, CstrVar 1, CstrBinOp (CstrBopAdd, CstrVar 0, CstrNat 1)))) :: ct2, CstrProd (CstrVar 2, CstrApp (CstrApp (CstrVar 3, CstrVar 2), CstrVar 0)), KdProper), KdDerivVar (BdKind (KdSubset (KdNat, PrBinRel (PrRelEq, CstrVar 1, CstrBinOp (CstrBopAdd, CstrVar 0, CstrNat 1)))) :: ct2, CstrVar 2, KdProper), KdDerivApp ((BdKind (KdSubset (KdNat, PrBinRel (PrRelEq, CstrVar 1, CstrBinOp (CstrBopAdd, CstrVar 0, CstrNat 1)))) :: ct2, CstrApp (CstrApp (CstrVar 3, CstrVar 2), CstrVar 0), KdProper), KdDerivApp ((BdKind (KdSubset (KdNat, PrBinRel (PrRelEq, CstrVar 1, CstrBinOp (CstrBopAdd, CstrVar 0, CstrNat 1)))) :: ct2, CstrApp (CstrVar 3, CstrVar 2), KdArrow (KdNat, KdProper)), KdDerivVar (BdKind (KdSubset (KdNat, PrBinRel (PrRelEq, CstrVar 1, CstrBinOp (CstrBopAdd, CstrVar 0, CstrNat 1)))) :: ct2, CstrVar 3, KdArrow (KdProper, KdArrow (KdNat, KdProper))), KdDerivVar (BdKind (KdSubset (KdNat, PrBinRel (PrRelEq, CstrVar 1, CstrBinOp (CstrBopAdd, CstrVar 0, CstrNat 1)))) :: ct2, CstrVar 2, KdProper)), KdDerivBase ((BdKind (KdSubset (KdNat, PrBinRel (PrRelEq, CstrVar 1, CstrBinOp (CstrBopAdd, CstrVar 0, CstrNat 1)))) :: ct2, CstrVar 0, KdNat), KdDerivVar (BdKind (KdSubset (KdNat, PrBinRel (PrRelEq, CstrVar 1, CstrBinOp (CstrBopAdd, CstrVar 0, CstrNat 1)))) :: ct2, CstrVar 0, KdSubset (KdNat, PrBinRel (PrRelEq, CstrVar 2, CstrBinOp (CstrBopAdd, CstrVar 0, CstrNat 1))))))))
      val c3 = CstrSum (c1, c2)
      val ct3 = ct2
      val d3 = KdDerivSum ((ct3, c3, KdProper), d1, d2)
      val c4 = CstrAbs (KdNat, c3)
      val ct4 = tl ct3
      val d4 = KdDerivAbs ((ct4, c4, KdArrow (KdNat, KdProper)), KdWfDerivNat (ct4, KdNat), d3)
      val c5 = CstrAbs (KdProper, c4)
      val ct5 = tl ct4
      val d5 = KdDerivAbs ((ct5, c5, KdArrow (KdProper, KdArrow (KdNat, KdProper))), KdWfDerivProper (ct5, KdProper), d4)
      val c6 = CstrRec (KdArrow (KdProper, KdArrow (KdNat, KdProper)), c5)
      val ct6 = tl ct5
      val d6 = KdDerivRec ((ct6, c6, KdArrow (KdProper, KdArrow (KdNat, KdProper))), KdWfDerivArrow ((ct6, KdArrow (KdProper, KdArrow (KdNat, KdProper))), KdWfDerivProper (ct6, KdProper), KdWfDerivArrow ((ct6, KdArrow (KdNat, KdProper)), KdWfDerivNat (ct6, KdNat), KdWfDerivProper (ct6, KdProper))), d5)
      val list_cstr_body = CstrAbs (KdProper, CstrAbs (KdNat, CstrSum (CstrExists (KdSubset (KdUnit, PrBinRel (PrRelEq, CstrVar 1, CstrNat 0)), CstrTypeUnit), CstrExists (KdSubset (KdNat, PrBinRel (PrRelEq, CstrVar 1, CstrBinOp (CstrBopAdd, CstrVar 0, CstrNat 1))), CstrProd (CstrVar 2, CstrApp (CstrApp (CstrVar 3, CstrVar 2), CstrVar 0))))))
      fun unfold_list_cstr ty n =
        let
          val tmp1 = Passes.TermSubstConstr.subst_constr_in_constr_top list_cstr list_cstr_body
          val (_, body1) = extract_cstr_abs tmp1
          val tmp2 = Passes.TermSubstConstr.subst_constr_in_constr_top ty body1
          val (_, body2) = extract_cstr_abs tmp2
          val tmp3 = Passes.TermSubstConstr.subst_constr_in_constr_top n body2
        in
          tmp3
        end
      val plus_ty = CstrForall (KdNat, CstrForall (KdNat, CstrArrow (CstrProd (CstrTypeNat (CstrVar 1), CstrTypeNat (CstrVar 0)), CstrTypeNat (CstrBinOp (CstrBopAdd, CstrVar 1, CstrVar 0)), CstrTime "1.0")))
      val len_ty = CstrForall (KdProper, CstrForall (KdNat, CstrArrow (CstrApp (CstrApp (list_cstr, CstrVar 1), CstrVar 0), CstrTypeNat (CstrVar 0), CstrBinOp (CstrBopMult, CstrTime "3.0", CstrUnOp (CstrUopNat2Time, CstrVar 0)))))
      val c7 = CstrBinOp (CstrBopMult, CstrTime "3.0", CstrUnOp (CstrUopNat2Time, CstrVar 0))
      val ct7 = [BdKind KdNat, BdKind KdProper]
      val d7 = KdDerivBinOp ((ct7, c7, KdTimeFun 0), KdDerivTime (ct7, CstrTime "3.0", KdTimeFun 0), KdDerivUnOp ((ct7, CstrUnOp (CstrUopNat2Time, CstrVar 0), KdTimeFun 0), KdDerivVar (ct7, CstrVar 0, KdNat)))
      val c8 = CstrApp (CstrApp (list_cstr, CstrVar 1), CstrVar 0)
      val ct8 = ct7
      val d8 = KdDerivApp ((ct8, c8, KdProper), KdDerivApp ((ct8, CstrApp (list_cstr, CstrVar 1), KdArrow (KdNat, KdProper)), DerivationPasses.TypingDerivationShift.shift_kinding_derivation_above ct8 0 d6, KdDerivVar (ct8, CstrVar 1, KdProper)), KdDerivVar (ct8, CstrVar 0, KdNat))
      val c9 = CstrArrow (c8, CstrTypeNat (CstrVar 0), c7)
      val ct9 = ct8
      val d9 = KdDerivArrow ((ct9, c9, KdProper), d8, KdDerivTypeNat ((ct9, CstrTypeNat (CstrVar 0), KdProper), KdDerivVar (ct9, CstrVar 0, KdNat)), d7)
      val c10 = CstrForall (KdProper, CstrForall (KdNat, c9))
      val ct10 = tl (tl ct9)
      val d10 = KdDerivForall ((ct10, c10, KdProper), KdWfDerivProper (ct10, KdProper), KdDerivForall ((tl ct9, CstrForall (KdNat, c9), KdProper), KdWfDerivNat (tl ct9, KdNat), d9))
      fun app_type_fun ty1 cstr2 =
        let
          val (_, body1) = extract_cstr_forall ty1
          val tmp1 = Passes.TermSubstConstr.subst_constr_in_constr_top cstr2 body1
        in
          tmp1
        end
      val tm1 = TmNat 0
      val tm1_ctx = [BdType (CstrExists (KdSubset (KdUnit, PrBinRel (PrRelEq, CstrVar 2, CstrNat 0)), CstrTypeUnit)), BdType (CstrApp (CstrApp (list_cstr, CstrVar 1), CstrVar 0)), BdKind KdNat, BdKind KdProper, BdType len_ty, BdType plus_ty]
      val tm1_ty = CstrTypeNat (CstrNat 0)
      val tm1_ti = CstrTime "0.0"
      val tm1_rel = (tm1_ctx, tm1, tm1_ty, tm1_ti)
      val tm1_deriv = TyDerivNat tm1_rel
      val tm1_5_rel = (tm1_ctx, tm1, CstrTypeNat (CstrVar 2), CstrTime "0.0")
      val tm1_5_deriv = TyDerivSub (tm1_5_rel, tm1_deriv, TyEqDerivAssume (tm1_ctx, tm1_ty, #3 tm1_5_rel), PrDerivAdmit (tm1_ctx, PrBinRel (PrRelLe, #4 tm1_rel, #4 tm1_5_rel)))
      val tm2 = TmNat 1
      val tm2_ctx = [BdType (CstrProd (CstrVar 4, CstrApp (CstrApp (list_cstr, CstrVar 4), CstrVar 0))), BdKind (KdSubset (KdNat, PrBinRel (PrRelEq, CstrVar 3, CstrBinOp (CstrBopAdd, CstrVar 0, CstrNat 1)))), BdType (CstrExists (KdSubset (KdNat, PrBinRel (PrRelEq, CstrVar 2, CstrBinOp (CstrBopAdd, CstrVar 0, CstrNat 1))), CstrProd (CstrVar 3, CstrApp (CstrApp (list_cstr, CstrVar 3), CstrVar 0))))] @ (tl tm1_ctx)
      val tm2_ty = CstrTypeNat (CstrNat 1)
      val tm2_ti = CstrTime "0.0"
      val tm2_rel = (tm2_ctx, tm2, tm2_ty, tm2_ti)
      val tm2_deriv = TyDerivNat tm2_rel
      val tm3 = TmVar 6
      val tm3_ctx = tm2_ctx
      val tm3_ty = len_ty
      val tm3_ti = CstrTime "0.0"
      val tm3_rel = (tm3_ctx, tm3, tm3_ty, tm3_ti)
      val tm3_deriv = TyDerivVar tm3_rel
      val cstr1 = CstrVar 5
      val cstr1_ctx = tm3_ctx
      val cstr1_kd = KdProper
      val cstr1_rel = (cstr1_ctx, cstr1, cstr1_kd)
      val cstr1_deriv = KdDerivVar cstr1_rel
      val tm4 = TmCstrApp (tm3, cstr1)
      val tm4_ctx = tm3_ctx
      val tm4_ty = app_type_fun tm3_ty cstr1
      val tm4_ti = tm3_ti
      val tm4_rel = (tm4_ctx, tm4, tm4_ty, tm4_ti)
      val tm4_deriv = TyDerivCstrApp (tm4_rel, tm3_deriv, cstr1_deriv)
      val cstr2 = CstrVar 1
      val cstr2_ctx = tm4_ctx
      val cstr2_kd = KdNat
      val cstr2_rel = (cstr2_ctx, cstr2, cstr2_kd)
      val cstr2_deriv = KdDerivBase (cstr2_rel, KdDerivVar (cstr2_ctx, cstr2, KdSubset (KdNat, PrBinRel (PrRelEq, CstrVar 5, CstrBinOp (CstrBopAdd, CstrVar 0, CstrNat 1)))))
      val tm5 = TmCstrApp (tm4, cstr2)
      val tm5_ctx = cstr2_ctx
      val tm5_ty = app_type_fun tm4_ty cstr2
      val tm5_ti = tm4_ti
      val tm5_rel = (tm5_ctx, tm5, tm5_ty, tm5_ti)
      val tm5_deriv = TyDerivCstrApp (tm5_rel, tm4_deriv, cstr2_deriv)
      val tm6 = TmVar 0
      val tm6_ctx = tm5_ctx
      val tm6_ty = CstrProd (CstrVar 5, CstrApp (CstrApp (list_cstr, CstrVar 5), CstrVar 1))
      val tm6_ti = CstrTime "0.0"
      val tm6_rel = (tm6_ctx, tm6, tm6_ty, tm6_ti)
      val tm6_deriv = TyDerivVar tm6_rel
      val tm7 = TmSnd tm6
      val tm7_ctx = tm6_ctx
      val tm7_ty = CstrApp (CstrApp (list_cstr, CstrVar 5), CstrVar 1)
      val tm7_ti = tm6_ti
      val tm7_rel = (tm7_ctx, tm7, tm7_ty, tm7_ti)
      val tm7_deriv = TyDerivSnd (tm7_rel, tm6_deriv)
      val tm8 = TmApp (tm5, tm7)
      val tm8_ctx = tm7_ctx
      val tm8_ty = #2 (extract_cstr_arrow tm5_ty)
      val tm8_ti = CstrBinOp (CstrBopAdd, CstrBinOp (CstrBopAdd, CstrBinOp (CstrBopAdd, tm5_ti, tm7_ti), CstrTime "1.0"), #3 (extract_cstr_arrow tm5_ty))
      val tm8_rel = (tm8_ctx, tm8, tm8_ty, tm8_ti)
      val tm8_deriv = TyDerivApp (tm8_rel, tm5_deriv, tm7_deriv)
      val tm9 = TmPair (tm2, tm8)
      val tm9_ctx = tm8_ctx
      val tm9_ty = CstrProd (tm2_ty, tm8_ty)
      val tm9_ti = CstrBinOp (CstrBopAdd, tm2_ti, tm8_ti)
      val tm9_rel = (tm9_ctx, tm9, tm9_ty, tm9_ti)
      val tm9_deriv = TyDerivPair (tm9_rel, tm2_deriv, tm8_deriv)
      val cstr3 = CstrNat 1
      val cstr3_ctx = tm9_ctx
      val cstr3_kd = KdNat
      val cstr3_rel = (cstr3_ctx, cstr3, cstr3_kd)
      val cstr3_deriv = KdDerivNat cstr3_rel
      val tm10 = TmVar 7
      val tm10_ctx = cstr3_ctx
      val tm10_ty = plus_ty
      val tm10_ti = CstrTime "0.0"
      val tm10_rel = (tm10_ctx, tm10, tm10_ty, tm10_ti)
      val tm10_deriv = TyDerivVar tm10_rel
      val tm11 = TmCstrApp (tm10, cstr3)
      val tm11_ctx = tm10_ctx
      val tm11_ty = app_type_fun tm10_ty cstr3
      val tm11_ti = tm10_ti
      val tm11_rel = (tm11_ctx, tm11, tm11_ty, tm11_ti)
      val tm11_deriv = TyDerivCstrApp (tm11_rel, tm10_deriv, cstr3_deriv)
      val tm12 = TmCstrApp (tm11, cstr2)
      val tm12_ctx = tm11_ctx
      val tm12_ty = app_type_fun tm11_ty cstr2
      val tm12_ti = tm11_ti
      val tm12_rel = (tm12_ctx, tm12, tm12_ty, tm12_ti)
      val tm12_deriv = TyDerivCstrApp (tm12_rel, tm11_deriv, cstr2_deriv)
      val tm13 = TmApp (tm12, tm9)
      val tm13_ctx = tm12_ctx
      val tm13_ty = #2 (extract_cstr_arrow tm12_ty)
      val tm13_ti = CstrBinOp (CstrBopAdd, CstrBinOp (CstrBopAdd, CstrBinOp (CstrBopAdd, tm12_ti, tm9_ti), CstrTime "1.0"), #3 (extract_cstr_arrow tm12_ty))
      val tm13_rel = (tm13_ctx, tm13, tm13_ty, tm13_ti)
      val tm13_deriv = TyDerivApp (tm13_rel, tm12_deriv, tm9_deriv)
      val tm13_5_rel = (tm13_ctx, tm13, CstrTypeNat (CstrVar 4), CstrBinOp (CstrBopMult, CstrTime "3.0", CstrUnOp (CstrUopNat2Time, CstrVar 4)))
      val tm13_5_deriv = TyDerivSub (tm13_5_rel, tm13_deriv, TyEqDerivAssume (tm13_ctx, tm13_ty, #3 tm13_5_rel), PrDerivAdmit (tm13_ctx, PrBinRel (PrRelLe, #4 tm13_rel, #4 tm13_5_rel)))
      val tm14 = TmVar 0
      val tm14_ctx = tl (tl tm13_ctx)
      val tm14_ty = CstrExists (KdSubset (KdNat, PrBinRel (PrRelEq, CstrVar 3, CstrBinOp (CstrBopAdd, CstrVar 0, CstrNat 1))), CstrProd (CstrVar 4, CstrApp (CstrApp (list_cstr, CstrVar 4), CstrVar 0)))
      val tm14_ti = CstrTime "0.0"
      val tm14_rel = (tm14_ctx, tm14, tm14_ty, tm14_ti)
      val tm14_deriv = TyDerivVar tm14_rel
      val tm15 = TmUnpack (tm14, tm13)
      val tm15_ctx = tm14_ctx
      val tm15_ty = CstrTypeNat (CstrVar 2)
      val tm15_ti = CstrBinOp (CstrBopAdd, tm14_ti, CstrBinOp (CstrBopMult, CstrTime "3.0", CstrUnOp (CstrUopNat2Time, CstrVar 2)))
      val tm15_rel = (tm15_ctx, tm15, tm15_ty, tm15_ti)
      val tm15_deriv = TyDerivUnpack (tm15_rel, tm14_deriv, tm13_5_deriv)
      val tm16 = TmVar 0
      val tm16_ctx = tl tm15_ctx
      val tm16_ty = CstrApp (CstrApp (list_cstr, CstrVar 2), CstrVar 1)
      val tm16_ti = CstrTime "0.0"
      val tm16_rel = (tm16_ctx, tm16, tm16_ty, tm16_ti)
      val tm16_deriv = TyDerivVar tm16_rel
      val tm17 = TmUnfold tm16
      val tm17_ctx = tm16_ctx
      val tm17_ty = unfold_list_cstr (CstrVar 2) (CstrVar 1)
      val tm17_ti = tm16_ti
      val tm17_rel = (tm17_ctx, tm17, tm17_ty, tm17_ti)
      val tm17_deriv = TyDerivUnfold (tm17_rel, tm16_deriv)
      val tm18 = TmCase (tm17, tm1, tm15)
      val tm18_ctx = tm17_ctx
      val tm18_ty = CstrTypeNat (CstrVar 1)
      val tm18_ti = CstrBinOp (CstrBopAdd, tm17_ti, CstrBinOp (CstrBopMax, CstrTime "0.0", CstrBinOp (CstrBopAdd, CstrTime "0.0", CstrBinOp (CstrBopMult, CstrTime "3.0", CstrUnOp (CstrUopNat2Time, CstrVar 1)))))
      val tm18_rel = (tm18_ctx, tm18, tm18_ty, tm18_ti)
      val tm18_deriv = TyDerivCase (tm18_rel, tm17_deriv, tm1_5_deriv, tm15_deriv)
      val tm18_5_rel = (tm18_ctx, tm18, tm18_ty, CstrBinOp (CstrBopMult, CstrTime "3.0", CstrUnOp (CstrUopNat2Time, CstrVar 1)))
      val tm18_5_deriv = TyDerivSub (tm18_5_rel, tm18_deriv, TyEqDerivAssume (tm18_ctx, tm18_ty, #3 tm18_5_rel), PrDerivAdmit (tm18_ctx, PrBinRel (PrRelLe, #4 tm18_rel, #4 tm18_5_rel)))
      val tm19 = TmAbs (CstrApp (CstrApp (list_cstr, CstrVar 1), CstrVar 0), tm18)
      val tm19_ctx = tl tm18_ctx
      val tm19_ty = CstrArrow (CstrApp (CstrApp (list_cstr, CstrVar 1), CstrVar 0), CstrTypeNat (CstrVar 0), CstrBinOp (CstrBopMult, CstrTime "3.0", CstrUnOp (CstrUopNat2Time, CstrVar 0)))
      val tm19_ti = CstrTime "0.0"
      val tm19_rel = (tm19_ctx, tm19, tm19_ty, tm19_ti)
      val tm19_deriv = TyDerivAbs (tm19_rel, KdDerivApp ((tm19_ctx, CstrApp (CstrApp (list_cstr, CstrVar 1), CstrVar 0), KdProper), KdDerivApp ((tm19_ctx, CstrApp (list_cstr, CstrVar 1), KdArrow (KdNat, KdProper)), DerivationPasses.TypingDerivationShift.shift_kinding_derivation_above tm19_ctx 0 d6, KdDerivVar (tm19_ctx, CstrVar 1, KdProper)), KdDerivVar (tm19_ctx, CstrVar 0, KdNat)), tm18_5_deriv)
      val tm20 = TmCstrAbs (KdNat, tm19)
      val tm20_ctx = tl tm19_ctx
      val tm20_ty = CstrForall (KdNat, tm19_ty)
      val tm20_ti = CstrTime "0.0"
      val tm20_rel = (tm20_ctx, tm20, tm20_ty, tm20_ti)
      val tm20_deriv = TyDerivCstrAbs (tm20_rel, KdWfDerivNat (tm20_ctx, KdNat), tm19_deriv)
      val tm21 = TmCstrAbs (KdProper, tm20)
      val tm21_ctx = tl tm20_ctx
      val tm21_ty = CstrForall (KdProper, tm20_ty)
      val tm21_ti = CstrTime "0.0"
      val tm21_rel = (tm21_ctx, tm21, tm21_ty, tm21_ti)
      val tm21_deriv = TyDerivCstrAbs (tm21_rel, KdWfDerivProper (tm21_ctx, KdProper), tm20_deriv)
      val tm22 = TmRec (len_ty, tm21)
      val tm22_ctx = tl tm21_ctx
      val tm22_ty = len_ty
      val tm22_ti = CstrTime "0.0"
      val tm22_rel = (tm22_ctx, tm22, tm22_ty, tm22_ti)
      val tm22_deriv = TyDerivRec (tm22_rel, DerivationPasses.TypingDerivationShift.shift_kinding_derivation_above tm22_ctx 0 d10, tm21_deriv)
      val _ = println (str_bool (MicroTiMLChecker.check_typing_derivation tm22_deriv))
      val tm22_deriv_new = DerivationPasses.ANF.normalize_derivation tm22_deriv
      val _ = println (str_bool (MicroTiMLChecker.check_typing_derivation tm22_deriv_new))
      val tm22_deriv_clo = #1 (DerivationPasses.CloConv.transform_typing_derivation (tm22_deriv_new, ()))
      (*val _ = println (snd (Passes.Printer.transform_term (#2 (extract_tyrel tm22_deriv_new), ["plus"])))
      val _ = println (snd (Passes.Printer.transform_term (#2 (extract_tyrel tm22_deriv_clo), ["plus"])))*)
    in
      tm22_deriv
    end

  fun test_fac () =
    let
      val bool_cstr = CstrAbs (KdBool, CstrSum (CstrExists (KdSubset (KdUnit, PrBinRel (PrRelEq, CstrVar 1, CstrTrue)), CstrTypeUnit), CstrExists (KdSubset (KdUnit, PrBinRel (PrRelEq, CstrVar 1, CstrFalse)), CstrTypeUnit)))
      val bool_cstr_body = CstrSum (CstrExists (KdSubset (KdUnit, PrBinRel (PrRelEq, CstrVar 1, CstrTrue)), CstrTypeUnit), CstrExists (KdSubset (KdUnit, PrBinRel (PrRelEq, CstrVar 1, CstrFalse)), CstrTypeUnit))
      val is_zero_ty = CstrForall (KdNat, CstrArrow (CstrTypeNat (CstrVar 0), Passes.TermSubstConstr.subst_constr_in_constr_top (CstrBinOp (CstrBopEq, CstrVar 0, CstrNat 0)) bool_cstr_body, CstrTime "1.0"))
      val minus_ty = CstrForall (KdNat, CstrForall (KdNat, CstrArrow (CstrProd (CstrTypeNat (CstrVar 1), CstrTypeNat (CstrVar 0)), CstrTypeNat (CstrBinOp (CstrBopDiff, CstrVar 1, CstrVar 0)), CstrTime "1.0")))
      val mult_ty = CstrArrow (CstrProd (CstrExists (KdNat, CstrTypeNat (CstrVar 0)), CstrExists (KdNat, CstrTypeNat (CstrVar 0))), CstrExists (KdNat, CstrTypeNat (CstrVar 0)), CstrTime "1.0")
      val fac_ty = CstrForall (KdNat, CstrArrow (CstrTypeNat (CstrVar 0), CstrExists (KdNat, CstrTypeNat (CstrVar 0)), CstrBinOp (CstrBopMult, CstrTime "7.0", CstrUnOp (CstrUopNat2Time, CstrVar 0))))
      val tm1 = TmPack (CstrNat 1, TmNat 1)
      val tm1_ctx = [BdType (CstrExists (KdSubset (KdUnit, PrBinRel (PrRelEq, CstrBinOp (CstrBopEq, CstrVar 2, CstrNat 0), CstrTrue)), CstrTypeUnit)), BdType (CstrTypeNat (CstrVar 0)), BdKind KdNat, BdType fac_ty, BdType mult_ty, BdType minus_ty, BdType is_zero_ty]
      val tm1_rel = (tm1_ctx, tm1, CstrExists (KdNat, CstrTypeNat (CstrVar 0)), CstrTime "0.0")
      val tm1_deriv = TyDerivPack (tm1_rel, KdDerivExists ((tm1_ctx, CstrExists (KdNat, CstrTypeNat (CstrVar 0)), KdProper), KdWfDerivNat (tm1_ctx, KdNat), KdDerivTypeNat ((BdKind KdNat :: tm1_ctx, CstrTypeNat (CstrVar 0), KdProper), KdDerivVar (BdKind KdNat :: tm1_ctx, CstrVar 0, KdNat))), KdDerivNat (tm1_ctx, CstrNat 1, KdNat), TyDerivNat (tm1_ctx, TmNat 1, CstrTypeNat (CstrNat 1), CstrTime "0.0"))
      val tm2 = TmPair (TmVar 1, TmNat 1)
      val tm2_ctx = [BdType (CstrExists (KdSubset (KdUnit, PrBinRel (PrRelEq, CstrBinOp (CstrBopEq, CstrVar 2, CstrNat 0), CstrFalse)), CstrTypeUnit)), BdType (CstrTypeNat (CstrVar 0)), BdKind KdNat, BdType fac_ty, BdType mult_ty, BdType minus_ty, BdType is_zero_ty]
      val tm2_rel = (tm2_ctx, tm2, CstrProd (CstrTypeNat (CstrVar 2), CstrTypeNat (CstrNat 1)), CstrBinOp (CstrBopAdd, CstrTime "0.0", CstrTime "0.0"))
      val tm2_deriv = TyDerivPair (tm2_rel, TyDerivVar (tm2_ctx, TmVar 1, CstrTypeNat (CstrVar 2), CstrTime "0.0"), TyDerivNat (tm2_ctx, TmNat 1, CstrTypeNat (CstrNat 1), CstrTime "0.0"))
      val tm3 = TmCstrApp (TmCstrApp (TmVar 5, CstrVar 2), CstrNat 1)
      val tm3_ctx = tm2_ctx
      val tm3_rel = (tm3_ctx, tm3, CstrArrow (CstrProd (CstrTypeNat (CstrVar 2), CstrTypeNat (CstrNat 1)), CstrTypeNat (CstrBinOp (CstrBopDiff, CstrVar 2, CstrNat 1)), CstrTime "1.0"), CstrTime "0.0")
      val tm3_deriv = TyDerivCstrApp (tm3_rel, TyDerivCstrApp ((tm3_ctx, TmCstrApp (TmVar 5, CstrVar 2), CstrForall (KdNat, CstrArrow (CstrProd (CstrTypeNat (CstrVar 3), CstrTypeNat (CstrVar 0)), CstrTypeNat (CstrBinOp (CstrBopDiff, CstrVar 3, CstrVar 0)), CstrTime "1.0")), CstrTime "0.0"), TyDerivVar (tm3_ctx, TmVar 5, minus_ty, CstrTime "0.0"), KdDerivVar (tm3_ctx, CstrVar 2, KdNat)), KdDerivNat (tm3_ctx, CstrNat 1, KdNat))
      val tm4 = TmApp (tm3, tm2)
      val tm4_ctx = tm3_ctx
      val tm4_rel = (tm4_ctx, tm4, CstrTypeNat (CstrBinOp (CstrBopDiff, CstrVar 2, CstrNat 1)), CstrBinOp (CstrBopAdd, CstrBinOp (CstrBopAdd, CstrBinOp (CstrBopAdd, CstrTime "0.0", CstrBinOp (CstrBopAdd, CstrTime "0.0", CstrTime "0.0")), CstrTime "1.0"), CstrTime "1.0"))
      val tm4_deriv = TyDerivApp (tm4_rel, tm3_deriv, tm2_deriv)
      val tm5 = TmCstrApp (TmVar 3, CstrBinOp (CstrBopDiff, CstrVar 2, CstrNat 1))
      val tm5_ctx = tm4_ctx
      val tm5_rel = (tm5_ctx, tm5, CstrArrow (CstrTypeNat (CstrBinOp (CstrBopDiff, CstrVar 2, CstrNat 1)), CstrExists (KdNat, CstrTypeNat (CstrVar 0)), CstrBinOp (CstrBopMult, CstrTime "7.0", CstrUnOp (CstrUopNat2Time, CstrBinOp (CstrBopDiff, CstrVar 2, CstrNat 1)))), CstrTime "0.0")
      val tm5_deriv = TyDerivCstrApp (tm5_rel, TyDerivVar (tm5_ctx, TmVar 3, fac_ty, CstrTime "0.0"), KdDerivBinOp ((tm5_ctx, CstrBinOp (CstrBopDiff, CstrVar 2, CstrNat 1), KdNat), KdDerivVar (tm5_ctx, CstrVar 2, KdNat), KdDerivNat (tm5_ctx, CstrNat 1, KdNat)))
      val tm6 = TmApp (tm5, tm4)
      val tm6_ctx = tm5_ctx
      val tm6_rel = (tm6_ctx, tm6, CstrExists (KdNat, CstrTypeNat (CstrVar 0)), CstrBinOp (CstrBopAdd, CstrBinOp (CstrBopAdd, CstrBinOp (CstrBopAdd, CstrTime "0.0", CstrBinOp (CstrBopAdd, CstrBinOp (CstrBopAdd, CstrBinOp (CstrBopAdd, CstrTime "0.0", CstrBinOp (CstrBopAdd, CstrTime "0.0", CstrTime "0.0")), CstrTime "1.0"), CstrTime "1.0")), CstrTime "1.0"), CstrBinOp (CstrBopMult, CstrTime "7.0", CstrUnOp (CstrUopNat2Time, CstrBinOp (CstrBopDiff, CstrVar 2, CstrNat 1)))))
      val tm6_deriv = TyDerivApp (tm6_rel, tm5_deriv, tm4_deriv)
      val tm7 = TmPack (CstrVar 2, TmVar 1)
      val tm7_ctx = tm6_ctx
      val tm7_rel = (tm7_ctx, tm7, CstrExists (KdNat, CstrTypeNat (CstrVar 0)), CstrTime "0.0")
      val tm7_deriv = TyDerivPack (tm7_rel, KdDerivExists ((tm7_ctx, CstrExists (KdNat, CstrTypeNat (CstrVar 0)), KdProper), KdWfDerivNat (tm7_ctx, KdNat), KdDerivTypeNat ((BdKind KdNat :: tm7_ctx, CstrTypeNat (CstrVar 0), KdProper), KdDerivVar (BdKind KdNat :: tm7_ctx, CstrVar 0, KdNat))), KdDerivVar (tm7_ctx, CstrVar 2, KdNat), TyDerivVar (tm7_ctx, TmVar 1, CstrTypeNat (CstrVar 2), CstrTime "0.0"))
      val tm8 = TmPair (tm7, tm6)
      val tm8_ctx = tm7_ctx
      val tm8_rel = (tm8_ctx, tm8, CstrProd (CstrExists (KdNat, CstrTypeNat (CstrVar 0)), CstrExists (KdNat, CstrTypeNat (CstrVar 0))), CstrBinOp (CstrBopAdd, CstrTime "0.0", CstrBinOp (CstrBopAdd, CstrBinOp (CstrBopAdd, CstrBinOp (CstrBopAdd, CstrTime "0.0", CstrBinOp (CstrBopAdd, CstrBinOp (CstrBopAdd, CstrBinOp (CstrBopAdd, CstrTime "0.0", CstrBinOp (CstrBopAdd, CstrTime "0.0", CstrTime "0.0")), CstrTime "1.0"), CstrTime "1.0")), CstrTime "1.0"), CstrBinOp (CstrBopMult, CstrTime "7.0", CstrUnOp (CstrUopNat2Time, CstrBinOp (CstrBopDiff, CstrVar 2, CstrNat 1))))))
      val tm8_deriv = TyDerivPair (tm8_rel, tm7_deriv, tm6_deriv)
      val tm9 = TmApp (TmVar 4, tm8)
      val tm9_ctx = tm8_ctx
      val tm9_rel = (tm9_ctx, tm9, CstrExists (KdNat, CstrTypeNat (CstrVar 0)), CstrBinOp (CstrBopAdd, CstrBinOp (CstrBopAdd, CstrBinOp (CstrBopAdd, CstrTime "0.0", CstrBinOp (CstrBopAdd, CstrTime "0.0", CstrBinOp (CstrBopAdd, CstrBinOp (CstrBopAdd, CstrBinOp (CstrBopAdd, CstrTime "0.0", CstrBinOp (CstrBopAdd, CstrBinOp (CstrBopAdd, CstrBinOp (CstrBopAdd, CstrTime "0.0", CstrBinOp (CstrBopAdd, CstrTime "0.0", CstrTime "0.0")), CstrTime "1.0"), CstrTime "1.0")), CstrTime "1.0"), CstrBinOp (CstrBopMult, CstrTime "7.0", CstrUnOp (CstrUopNat2Time, CstrBinOp (CstrBopDiff, CstrVar 2, CstrNat 1)))))), CstrTime "1.0"), CstrTime "1.0"))
      val tm9_deriv = TyDerivApp (tm9_rel, TyDerivVar (tm9_ctx, TmVar 4, mult_ty, CstrTime "0.0"), tm8_deriv)
      val tm10 = TmCstrApp (TmVar 5, CstrVar 1)
      val tm10_ctx = List.tl tm9_ctx
      val tm10_rel = (tm10_ctx, tm10, CstrArrow (CstrTypeNat (CstrVar 1), Passes.TermSubstConstr.subst_constr_in_constr_top (CstrBinOp (CstrBopEq, CstrVar 1, CstrNat 0)) bool_cstr_body, CstrTime "1.0"), CstrTime "0.0")
      val tm10_deriv = TyDerivCstrApp (tm10_rel, TyDerivVar (tm10_ctx, TmVar 5, is_zero_ty, CstrTime "0.0"), KdDerivVar (tm10_ctx, CstrVar 1, KdNat))
      val tm11 = TmApp (tm10, TmVar 0)
      val tm11_ctx = tm10_ctx
      val tm11_rel = (tm11_ctx, tm11, Passes.TermSubstConstr.subst_constr_in_constr_top (CstrBinOp (CstrBopEq, CstrVar 1, CstrNat 0)) bool_cstr_body, CstrBinOp (CstrBopAdd, CstrBinOp (CstrBopAdd, CstrBinOp (CstrBopAdd, CstrTime "0.0", CstrTime "0.0"), CstrTime "1.0"), CstrTime "1.0"))
      val tm11_deriv = TyDerivApp (tm11_rel, tm10_deriv, TyDerivVar (tm11_ctx, TmVar 0, CstrTypeNat (CstrVar 1), CstrTime "0.0"))
      val tm12 = TmCase (tm11, tm1, tm9)
      val tm12_ctx = tm11_ctx
      val tm12_rel = (tm12_ctx, tm12, CstrExists (KdNat, CstrTypeNat (CstrVar 0)), CstrBinOp (CstrBopAdd, CstrBinOp (CstrBopAdd, CstrBinOp (CstrBopAdd, CstrBinOp (CstrBopAdd, CstrTime "0.0", CstrTime "0.0"), CstrTime "1.0"), CstrTime "1.0"), CstrBinOp (CstrBopMax, CstrTime "0.0", CstrBinOp (CstrBopAdd, CstrBinOp (CstrBopAdd, CstrBinOp (CstrBopAdd, CstrTime "0.0", CstrBinOp (CstrBopAdd, CstrTime "0.0", CstrBinOp (CstrBopAdd, CstrBinOp (CstrBopAdd, CstrBinOp (CstrBopAdd, CstrTime "0.0", CstrBinOp (CstrBopAdd, CstrBinOp (CstrBopAdd, CstrBinOp (CstrBopAdd, CstrTime "0.0", CstrBinOp (CstrBopAdd, CstrTime "0.0", CstrTime "0.0")), CstrTime "1.0"), CstrTime "1.0")), CstrTime "1.0"), CstrBinOp (CstrBopMult, CstrTime "7.0", CstrUnOp (CstrUopNat2Time, CstrBinOp (CstrBopDiff, CstrVar 1, CstrNat 1)))))), CstrTime "1.0"), CstrTime "1.0"))))
      val tm12_deriv = TyDerivCase (tm12_rel, tm11_deriv, tm1_deriv, tm9_deriv)
      val tm125_rel = (tm12_ctx, tm12, #3 tm12_rel, CstrBinOp (CstrBopMult, CstrTime "7.0", CstrUnOp (CstrUopNat2Time, CstrVar 1)))
      val tm125_deriv = TyDerivSub (tm125_rel, tm12_deriv, TyEqDerivAssume (tm12_ctx, #3 tm12_rel, #3 tm125_rel), PrDerivAdmit (tm12_ctx, PrBinRel (PrRelLe, #4 tm12_rel, #4 tm125_rel)))
      val tm13 = TmAbs (CstrTypeNat (CstrVar 0), tm12)
      val tm13_ctx = List.tl tm12_ctx
      val tm13_rel = (tm13_ctx, tm13, CstrArrow (CstrTypeNat (CstrVar 0), CstrExists (KdNat, CstrTypeNat (CstrVar 0)), CstrBinOp (CstrBopMult, CstrTime "7.0", CstrUnOp (CstrUopNat2Time, CstrVar 0))), CstrTime "0.0")
      val tm13_deriv = TyDerivAbs (tm13_rel, KdDerivTypeNat ((tm13_ctx, CstrTypeNat (CstrVar 0), KdProper), KdDerivVar (tm13_ctx, CstrVar 0, KdNat)), tm125_deriv)
      val tm14 = TmCstrAbs (KdNat, tm13)
      val tm14_ctx = List.tl tm13_ctx
      val tm14_rel = (tm14_ctx, tm14, fac_ty, CstrTime "0.0")
      val tm14_deriv = TyDerivCstrAbs (tm14_rel, KdWfDerivNat (tm14_ctx, KdNat), tm13_deriv)
      val tm15 = TmRec (fac_ty, tm14)
      val tm15_ctx = List.tl tm14_ctx
      val tm15_rel = (tm15_ctx, tm15, fac_ty, CstrTime "0.0")
      val tm15_deriv = TyDerivRec (tm15_rel, KdDerivForall ((tm15_ctx, fac_ty, KdProper), KdWfDerivNat (tm15_ctx, KdNat), KdDerivArrow ((BdKind KdNat :: tm15_ctx, CstrArrow (CstrTypeNat (CstrVar 0), CstrExists (KdNat, CstrTypeNat (CstrVar 0)), CstrBinOp (CstrBopMult, CstrTime "7.0", CstrUnOp (CstrUopNat2Time, CstrVar 0))), KdProper), KdDerivTypeNat ((BdKind KdNat :: tm15_ctx, CstrTypeNat (CstrVar 0), KdProper), KdDerivVar (BdKind KdNat :: tm15_ctx, CstrVar 0, KdNat)), KdDerivExists ((BdKind KdNat :: tm15_ctx, CstrExists (KdNat, CstrTypeNat (CstrVar 0)), KdProper), KdWfDerivNat (BdKind KdNat :: tm15_ctx, KdNat), KdDerivTypeNat ((BdKind KdNat :: BdKind KdNat :: tm15_ctx, CstrTypeNat (CstrVar 0), KdProper), KdDerivVar (BdKind KdNat :: BdKind KdNat :: tm15_ctx, CstrVar 0, KdNat))), KdDerivBinOp ((BdKind KdNat :: tm15_ctx, CstrBinOp (CstrBopMult, CstrTime "7.0", CstrUnOp (CstrUopNat2Time, CstrVar 0)), KdTimeFun 0), KdDerivTime (BdKind KdNat :: tm15_ctx, CstrTime "7.0", KdTimeFun 0), KdDerivUnOp ((BdKind KdNat :: tm15_ctx, CstrUnOp (CstrUopNat2Time, CstrVar 0), KdTimeFun 0), KdDerivVar (BdKind KdNat :: tm15_ctx, CstrVar 0, KdNat))))), tm14_deriv)
      val _ = println (str_bool (MicroTiMLChecker.check_typing_derivation tm15_deriv))
      val tm15_deriv_new = DerivationPasses.ANF.normalize_derivation tm15_deriv
      val _ = println (str_bool (MicroTiMLChecker.check_typing_derivation tm15_deriv_new))
      (*val tm15_deriv_clo = #1 (DerivationPasses.CloConv.transform_typing_derivation (tm15_deriv, ()))*)
    in
      tm15_deriv
    end

  fun main (prog : string, args : string list) =
    let
      val _ = test_len ()
      val _ = test_fac ()
    in
      0
    end*)
end
