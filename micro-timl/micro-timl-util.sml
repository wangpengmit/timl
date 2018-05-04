structure MicroTiMLUtil = struct

open Util
open Binders
open MicroTiML

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

(* val TCString = TCTiML BaseTypes.String *)
val TCInt = TCTiML BaseTypes.Int
val TCBool = TCTiML BaseTypes.Bool
val TCByte = TCTiML BaseTypes.Byte
val TUnit = TConst TCUnit
val TEmpty = TConst TCEmpty
(* val TString = TConst TCString *)
val TInt = TConst TCInt
val TBool = TConst TCBool
val TByte = TConst TCByte
fun TSum (t1, t2) = TBinOp (TBSum, t1, t2)
fun TProd (t1, t2) = TBinOp (TBProd, t1, t2)
fun TAppIs (t, is) = foldl (swap TAppI) t is
fun TAppTs (t, ts) = foldl (swap TAppT) t ts
fun TMemTuplePtr (ts, i) = TTuplePtr (ts, i, false)
fun TStorageTuplePtr (ts, i) = TTuplePtr (ts, i, true)
         
fun EPair (e1, e2) = EBinOp (EBPair, e1, e2)
fun EProj (proj, e) = EUnOp (EUTiML $ EUProj proj, e)
fun EFst e = EProj (ProjFst, e)
fun ESnd e = EProj (ProjSnd, e)
fun EInj (inj, t, e) = EUnOp (EUInj (inj, t), e)
fun EInl (t, e) = EInj (InjInl, t, e)
fun EInr (t, e) = EInj (InjInr, t, e)
fun EFold (t, e) = EUnOp (EUFold t, e)
fun EUnfold e = EUnOp (EUUnfold, e)
fun EApp (e1, e2) = EBinOp (EBApp, e1, e2)

fun EBinOpPrim (opr, e1, e2) = EBinOp (EBPrim opr, e1, e2)
val EBNatAdd = EBNat EBNAdd
fun ENatAdd (e1, e2) = EBinOp (EBNatAdd, e1, e2)
fun ENew (e1, e2) = EBinOp (EBNew, e1, e2)
fun ERead (e1, e2) = EBinOp (EBRead, e1, e2)
fun EWrite (e1, e2, e3) = ETriOp (ETWrite, e1, e2, e3)
                                      
fun MakeEAbs (i, name, t, e) = EAbs (i, EBindAnno ((name, t), e))
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

fun choose (t1, t2) proj =
  case proj of
      ProjFst => t1
    | ProjSnd => t2
                                 
fun choose_update (b1, b2) proj =
  case proj of
      ProjFst => (true, b2)
    | ProjSnd => (b1, true)
                   
fun choose_inj (t1, t2) inj =
  case inj of
      InjInl => t1
    | InjInr => t2
                                 
fun choose_pair_inj (t, t_other) inj =
  case inj of
      InjInl => (t, t_other)
    | InjInr => (t_other, t)
                  
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

val unEAbsI = unBindAnnoName
val unEAbsT = unBindAnnoName
                
fun collect_EAbsI e =
  case e of
      EAbsI data =>
      let
        val (s, (name, e)) = unEAbsI data
        val (binds, e) = collect_EAbsI e
      in
        ((name, s) :: binds, e)
      end
    | _ => ([], e)

fun EAbsIs (binds, b) = foldr (EAbsI o IBindAnno) b binds
fun TForallIs (binds, b) = foldr (TForallI o IBindAnno) b binds
                               
fun collect_EAbsIT e =
  case e of
      EAbsI data =>
      let
        val (s, (name, e)) = unEAbsI data
        val (binds, e) = collect_EAbsIT e
      in
        (inl (name, s) :: binds, e)
      end
    | EAbsT data =>
      let
        val (k, (name, e)) = unEAbsT data
        val (binds, e) = collect_EAbsIT e
      in
        (inr (name, k) :: binds, e)
      end
    | _ => ([], e)

fun collect_TAbsIT b =
  case b of
      TAbsI data =>
      let
        val (s, (name, b)) = unBindAnnoName data
        val (binds, b) = collect_TAbsIT b
      in
        (inl (name, s) :: binds, b)
      end
    | TAbsT data =>
      let
        val (k, (name, b)) = unBindAnnoName data
        val (binds, b) = collect_TAbsIT b
      in
        (inr (name, k) :: binds, b)
      end
    | _ => ([], b)

fun eq_t a = MicroTiMLVisitor2.eq_t_fn (curry Equal.eq_var, Equal.eq_bs, Equal.eq_i, Equal.eq_s) a
                     
fun collect_ELet e =
  case e of
      ELet (e1, bind) =>
      let
        val (name, e) = unBindSimpName bind
        val (decls, e) = collect_ELet e
      in
        ((name, e1) :: decls, e)
      end
    | _ => ([], e)
fun ELets (decls, e) = foldr (fn ((name, e1), e) => ELet (e1, EBind (name, e))) e decls

fun collect_EAppI e =
  case e of
      EAppI (e, i) =>
      let 
        val (e, is) = collect_EAppI e
      in
        (e, is @ [i])
      end
    | _ => (e, [])
fun EAppIs (f, args) = foldl (swap EAppI) f args
                             
fun make_exists name s = TExistsI $ IBindAnno (((name, dummy), s), TUnit)
                             
fun TSumbool (s1, s2) =
  let
    val name = "__p"
  in
    TSum (make_exists name s1, make_exists name s2)
  end
                  
fun assert_fail msg = Impossible $ "Assert failed: " ^ msg
                             
fun assert_TiBool t =
  case t of
      TiBool a => a
    | _ => raise assert_fail $ "assert_TiBool"

end
                                 
