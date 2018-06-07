functor ExprUtilFn (Expr : EXPR) = struct

open Pattern
open Expr
open Operators
open Util
open Bind

infixr 0 $

val EUFst = EUProj (ProjFst ())
val EUSnd = EUProj (ProjSnd ())
(* val EUInt2Str = EUPrim EUPInt2Str *)
val EBAdd = EBPrim (EBPIntAdd ())
val EBNatAdd = EBNat (EBNAdd ())
                   
fun ETT r = EConst (ECTT (), r)
fun EConstInt (n, r) = EConst (ECInt n, r)
fun EConstNat (n, r) = EConst (ECNat n, r)
(* fun EConstString (n, r) = EConst (ECString n, r) *)
fun EByte (c, r) = EConst (ECByte c, r)
val EChar = EByte
val EConstByte = EByte
val EConstChar = EByte
fun EFst (e, r) = EUnOp (EUFst, e, r)
fun ESnd (e, r) = EUnOp (EUSnd, e, r)
fun EApp (e1, e2) = EBinOp (EBApp (), e1, e2)
fun EPair (e1, e2) = EBinOp (EBPair (), e1, e2)
fun EAppI (e, i) = EEI (EEIAppI (), e, i)
fun EAppIs (f, args) = foldl (swap EAppI) f args
fun EAppT (e, i) = EET (EETAppT (), e, i)
fun EAppTs (f, args) = foldl (swap EAppT) f args
fun EAsc (e, t) = EET (EETAsc (), e, t)
fun EAscTime (e, i) = EEI (EEIAscTime (), e, i)
fun EAscSpace (e, i) = EEI (EEIAscSpace (), e, i)
fun ENever (t, r) = ET (ETNever (), t, r)
fun EBuiltin (name, t, r) = ET (ETBuiltin name, t, r)
fun ENew (e1, e2) = EBinOp (EBNew (), e1, e2)
fun ERead (e1, e2) = EBinOp (EBRead (), e1, e2)
fun EWrite (e1, e2, e3) = ETriOp (ETWrite (), e1, e2, e3)
fun EEmptyArray (t, r) = ENewArrayValues (t, [], r)
fun EVectorGet (e1, e2) = EBinOp (EBVectorGet (), e1, e2)
fun EVectorPushBack (e1, e2) = EBinOp (EBVectorPushBack (), e1, e2)
fun EVectorSet (e1, e2, e3) = ETriOp (ETVectorSet (), e1, e2, e3)
fun EMapPtr (e1, e2) = EBinOp (EBMapPtr (), e1, e2)
fun EStorageSet (e1, e2) = EBinOp (EBStorageSet (), e1, e2)
fun EStorageGet (e, r) = EUnOp (EUStorageGet (), e, r)
fun EAnno (e, a, r) = EUnOp (EUAnno a, e, r)
fun EAnnoLiveVars (e, n, r) = EAnno (e, EALiveVars n, r)
fun EAnnoBodyOfRecur (e, r) = EAnno (e, EABodyOfRecur (), r)
  
fun collect_Pair e =
  case e of
      EBinOp (EBPair (), e1, e2) =>
      collect_Pair e1 @ [e2]
    | _ => [e]
             
fun collect_EAppI e =
  case e of
      EEI (opr, e, i) =>
      (case opr of
           EEIAppI () =>
             let 
               val (e, is) = collect_EAppI e
             in
               (e, is @ [i])
             end
         | _ => (e, [])
      )
    | _ => (e, [])

fun collect_EAppT e =
  case e of
      EET (opr, e, i) =>
      (case opr of
           EETAppT () =>
           let 
             val (e, is) = collect_EAppT e
           in
             (e, is @ [i])
           end
         | _ => (e, [])
      )
    | _ => (e, [])

fun MakePnAnno (pn, t) = PnAnno (pn, Outer t)
fun MakeEAbs (st, pn, e) = EAbs (st, Binders.Bind (pn, e))
fun MakeEAbsI (name, s, e, r) = EAbsI (IBindAnno ((name, s), e), r)
fun MakeDIdxDef (name, s, i) = DIdxDef (IBinder name, Outer s, Outer i)
fun MakeDVal (ename, tnames, e, r) = DVal (EBinder ename, Outer $ Unbound.Bind (map TBinder tnames, e), r)
fun MakeDTypeDef (name, t) = DTypeDef (TBinder name, Outer t)

fun assert_EAnnoLiveVars err e =
  case e of
      EUnOp (EUAnno (EALiveVars n), e, _) => (e, n)
    | _ => err ()
               
end
