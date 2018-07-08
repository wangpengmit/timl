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
val EInt = EConstInt
val ENat = EConstNat
(* fun EConstString (n, r) = EConst (ECString n, r) *)
fun EByte (c, r) = EConst (ECByte c, r)
val EChar = EByte
val EConstByte = EByte
val EConstChar = EByte
fun EBool (b, r) = EConst (ECBool b, r)
fun ETrue r = EBool (true, r)
fun EFalse r = EBool (false, r)
fun EFst (e, r) = EUnOp (EUFst, e, r)
fun ESnd (e, r) = EUnOp (EUSnd, e, r)
fun EApp (e1, e2) = EBinOp (EBApp (), e1, e2)
fun EIntAdd (e1, e2) = EBinOp (EBAdd, e1, e2)
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
fun EAnnoConstr (e, r) = EAnno (e, EAConstr (), r)
fun EHalt (e, t) = EET (EETHalt (), e, t)
fun EPtrProj (e, proj, r) = EUnOp (EUPtrProj proj, e, r)
fun EMapPtrProj (e1, (e2, path)) =
  foldl (fn ((proj, r), acc) => EPtrProj (acc, (proj, NONE), r)) (EMapPtr (e1, e2)) path
fun ENatCellGet (e, r) = EUnOp (EUNatCellGet (), e, r)
fun ENatCellSet (e1, e2) = EBinOp (EBNatCellSet (), e1, e2)

infix 0 %:
infix 0 |>
infix 0 |#
infix 0 %~
infix 0 |>#
        
fun a %: b = EAsc (a, b)
fun a |> b = EAscTime (a, b)
fun a |# b = EAscSpace (a, b)
fun EAscTimeSpace (e, (i, j)) = e |> i |# j
fun a |># b = EAscTimeSpace (a, b)
                               
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
fun MakeEAbs (st, pn, e) = EAbs (st, Binders.Bind (pn, e), NONE)
fun MakeEAbsWithAnno (st, pn, e, i) = EAbs (st, Binders.Bind (pn, e), i)
fun MakeEAbsI (name, s, e, r) = EAbsI (IBindAnno ((name, s), e), r)
fun MakeDIdxDef (name, s, i) = DIdxDef (IBinder name, Outer s, Outer i)
fun MakeDVal (ename, tnames, e, r) = DVal (EBinder ename, Outer $ Unbound.Bind (map (mapPair' TBinder Outer) tnames, e), r)
fun MakeDTypeDef (name, t) = DTypeDef (TBinder name, Outer t)

fun assert_EAnnoLiveVars err e =
  case e of
      EUnOp (EUAnno (EALiveVars n), e, _) => (e, n)
    | _ => err ()
fun is_rec_body e =
  case e of
      EUnOp (EUAnno (EABodyOfRecur ()), e, _) => (true, e)
    | _ => (false, e)
               
fun collect_EAbsI e =
  case e of
      EAbsI (data, _) =>
      let
        val (s, (name, e)) = unBindAnnoName data
        val (binds, e) = collect_EAbsI e
      in
        ((name, s) :: binds, e)
      end
    | _ => ([], e)
             
fun is_tail_call e =
  case e of
      EBinOp (EBApp (), _, _) => true
    | EET (EETAppT (), _, _) => true
    | EEI (EEIAppI (), _, _) => true
    | ECase (_, _, binds, _) =>
      let
        val len = length binds
      in
        if len >= 2 then
          true 
        else if len = 1 then
          is_tail_call $ snd $ Unbound.unBind $ hd binds
        else true
      end        
    (* | ECaseSumbool _ => true *)
    | EIfi _ => true
    | ETriOp (ETIte (), _, _, _) => true
    | EUnOp (EUAnno _, e, _) => is_tail_call e
    | EEI (EEIAscTime (), e, _) => is_tail_call e
    | EEI (EEIAscSpace (), e, _) => is_tail_call e
    | EET (EETAsc (), e, _) => is_tail_call e
    | ELet (_, bind, _) => is_tail_call $ snd $ Unbound.unBind bind
    (* | _ => false *)

end
