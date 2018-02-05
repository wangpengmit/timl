structure MicroTiMLExUtil = struct

open Util
open Binders
open MicroTiMLEx

infixr 0 $

fun KArrows bs k = foldr KArrow k bs
fun KArrowTs ks k = foldr KArrowT k ks
fun KArrowTypes n k = KArrowTs (repeat n KType) k
                          
fun TForallI bind = TQuanI (Forall, bind)
fun TForall bind = TQuan (Forall, bind)
fun TExistsI bind = TQuanI (Exists (), bind)
fun TExistsI_Many (ctx, t) = foldr (TExistsI o BindAnno) t ctx
fun MakeTExistsI (name, s, t) = TExistsI $ IBindAnno ((name, s), t)
fun TAbsI_Many (ctx, t) = foldr (TAbsI o BindAnno) t ctx
fun TAbsT_Many (ctx, t) = foldr (TAbsT o BindAnno) t ctx
fun TUni bind = TQuan (Forall, bind)
fun MakeTUni (name, k, t) = TUni $ TBindAnno ((name, k), t)
fun TUniKind (name, t) = MakeTUni (name, KType, t)
fun TUniKind_Many (names, t) = foldr TUniKind t names
                  
val TUnit = TConst TCUnit
val TEmpty = TConst TCEmpty
fun TSum (t1, t2) = TBinOp (TBSum, t1, t2)
fun TProd (t1, t2) = TBinOp (TBProd, t1, t2)
fun TAppIs (t, is) = foldl (swap TAppI) t is
fun TAppTs (t, ts) = foldl (swap TAppT) t ts
         
fun EPair (e1, e2) = EBinOp (EBPair, e1, e2)
fun EFst e = EUnOp (EUProj ProjFst, e)
fun ESnd e = EUnOp (EUProj ProjSnd, e)
fun EInlInr (opr, t, e) = EUnOp (EUInj (opr, t), e)
fun EInl (t, e) = EInlInr (InjInl, t, e)
fun EInr (t, e) = EInlInr (InjInr, t, e)
fun EFold (t, e) = EUnOp (EUFold t, e)
fun EUnfold e = EUnOp (EUUnfold, e)
fun EApp (e1, e2) = EBinOp (EBApp, e1, e2)

fun EProj (proj, e) = EUnOp (EUProj proj, e)
fun EInj (inj, t, e) = EUnOp (EUInj (inj, t), e)
fun EBinOpPrim (opr, e1, e2) = EBinOp (EBPrim opr, e1, e2)
fun ENew (e1, e2) = EBinOp (EBNew, e1, e2)
fun ERead (e1, e2) = EBinOp (EBRead, e1, e2)
fun ENatAdd (e1, e2) = EBinOp (EBNatAdd, e1, e2)
                                      
fun MakeEAbs (name, t, e) = EAbs $ EBindAnno ((name, t), e)
fun MakeEAbsI (name, s, e) = EAbsI $ IBindAnno ((name, s), e)
fun MakeEUnpack (e1, tname, ename, e2) = EUnpack (e1, TBind (tname, EBind (ename, e2)))
fun MakeEAbsT (name, k, e) = EAbsT $ TBindAnno ((name, k), e)
fun MakeERec (name, t, e) = ERec $ EBindAnno ((name, t), e)
fun MakeEUnpackI (e1, iname, ename, e2) = EUnpackI (e1, IBind (iname, EBind (ename, e2)))
fun MakeELet (e1, name, e2) = ELet (e1, EBind (name, e2))
fun MakeELetIdx (i, name, e) = ELetIdx (i, IBind (name, e))
fun MakeELetType (t, name, e) = ELetType (t, TBind (name, e))
fun MakeELetConstr (e1, name, e2) = ELetConstr (e1, CBind (name, e2))
fun MakeEAbsConstr (tnames, inames, ename, e) = EAbsConstr $ Bind ((map TBinder tnames, map IBinder inames, EBinder ename), e)
fun MakeECase (e, (name1, e1), (name2, e2)) = ECase (e, EBind (name1, e1), EBind (name2, e2))
fun MakeTQuanI (q, s, name, t) = TQuanI (q, IBindAnno ((name, s), t))
fun MakeTQuan (q, k, name, t) = TQuan (q, TBindAnno ((name, k), t))
fun MakeTForallI (s, name, t) = MakeTQuanI (Forall, s, name, t)
fun MakeTForall (s, name, t) = MakeTQuan (Forall, s, name, t)
fun EAbsTKind (name, e) = MakeEAbsT (name, KType, e) 
fun EAbsTKind_Many (names, e) = foldr EAbsTKind e names

fun assert_b msg b = Util.assert (fn () => b) msg

fun choose (t1, t2) proj =
  case proj of
      ProjFst => t1
    | ProjSnd => t2
                                 
fun choose_inj (t1, t2) inj =
  case inj of
      InjInl => t1
    | InjInr => t2
                                 
fun unBindSimp t =
  let
    val (Binder name, t) = unBind t
  in
    (name, t)
  end
    
fun collect_EAscType_rev e =
  let
    val self = collect_EAscType_rev
  in
    case e of
        EAscType (e, t) =>
        let
          val (e, args) = self e
        in
          (e, t :: args)
        end
      | _ => (e, [])
  end
fun collect_EAscType e = mapSnd rev $ collect_EAscType_rev e
                                
fun collect_EAscTime_rev e =
  let
    val self = collect_EAscTime_rev
  in
    case e of
        EAscTime (e, i) =>
        let
          val (e, args) = self e
        in
          (e, i :: args)
        end
      | _ => (e, [])
  end
fun collect_EAscTime e = mapSnd rev $ collect_EAscTime_rev e
                                
fun EAscTypes (e, ts) = foldl (swap EAscType) e ts
fun EAscTimes (e, is) = foldl (swap EAscTime) e is
                              
end
                                 
