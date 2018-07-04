functor IdxGetRegionFn (structure Idx : IDX where type region = Region.region
                      val get_region_var : Idx.var -> Region.region
                      val set_region_var : Idx.var -> Region.region -> Idx.var
                     ) = struct

open Idx
open Region
open Util

infixr 0 $
         
fun get_region_i i =
  case i of
      IVar (x, _) => get_region_var x
    | IConst (_, r) => r
    | IUnOp (_, _, r) => r
    | IBinOp (_, i1, i2) => combine_region (get_region_i i1) (get_region_i i2)
    | IIte (_, _, _, r) => r
    | IAbs (_, _, r) => r
    | IUVar (_, r) => r
    | IState _ => dummy

fun set_region_i i r =
  case i of
      IVar (x, anno) => IVar (set_region_var x r, anno)
    | IConst (a, _) => IConst (a, r)
    | IUnOp (opr, i, _) => IUnOp (opr, i, r)
    | IBinOp (opr, i1, i2) => IBinOp (opr, set_region_i i1 r, set_region_i i2 r)
    | IIte (i1, i2, i3, _) => IIte (i1, i2, i3, r)
    | IAbs (name, i, _) => IAbs (name, i, r)
    | IUVar (a, _) => IUVar (a, r)
    | IState _ => i

fun get_region_p p = 
  case p of
      PTrueFalse (_, r) => r
    | PNot (_, r) => r
    | PBinConn (_, p1, p2) => combine_region (get_region_p p1) (get_region_p p2)
    | PBinPred (_, i1, i2) => combine_region (get_region_i i1) (get_region_i i2)
    | PQuan (_, _, _, r) => r

fun set_region_p p r = 
  case p of
      PTrueFalse (b, _) => PTrueFalse (b, r)
    | PNot (p, _) => PNot (p, r)
    | PBinConn (opr, p1, p2) => PBinConn (opr, set_region_p p1 r, set_region_p p2 r)
    | PBinPred (opr, i1, i2) => PBinPred (opr, set_region_i i1 r, set_region_i i2 r)
    | PQuan (q, bs, bind, _) => PQuan (q, bs, bind, r)

fun get_region_s s = 
  case s of
      SBasic (_, r) => r
    | SSubset (_, _, r) => r
    | SUVar (_, r) => r
    | SAbs (_, _, r) => r
    | SApp (s, i) => combine_region (get_region_s s) (get_region_i i)

end

functor TypeGetRegionFn (structure Type : TYPE where type region = Region.region
                       val get_region_var : Type.var -> Region.region
                       val get_region_i : Type.idx -> Region.region
                       val get_region_s : Type.sort -> Region.region
                      ) = struct

open Type
open Region
open Util

infixr 0 $
         
fun get_region_mt t = 
  case t of
      TArrow ((_, t1), d, (_, t2)) => combine_region (get_region_mt t1) (get_region_mt t2)
    | TNat (_, r) => r
    | TiBool (_, r) => r
    | TArray (t, i) => combine_region (get_region_mt t) (get_region_i i)
    | TUnit r => r
    | TProd (t1, t2) => combine_region (get_region_mt t1) (get_region_mt t2)
    | TUniI (_, _, r) => r
    | TVar y => get_region_var y
    | TApp (t1, t2) => combine_region (get_region_mt t1) (get_region_mt t2)
    | TAbs (_, _, r) => r
    | TAppI (t, i) => combine_region (get_region_mt t) (get_region_i i)
    | TAbsI (_, _, r) => r
    | TBase (_, r) => r
    | TUVar (_, r) => r
    | TDatatype (_, r) => r
    | TSumbool (s1, s2) => combine_region (get_region_s s1) (get_region_s s2)
    | TMap t => get_region_mt t
    | TVector t => get_region_mt t
    | TState (_, r) => r
    | TTuplePtr (_, _, r) => r

fun get_region_t t = 
  case t of
      PTMono t => get_region_mt t
    | PTUni (_, _, r) => r

end

functor ExprGetRegionFn (structure Expr : EXPR
                                            where type mod_id = string * Region.region
                         val get_region_var : Expr.var -> Region.region
                         val get_region_cvar : Expr.cvar -> Region.region
                         val get_region_i : Expr.idx -> Region.region
                         val get_region_mt : Expr.mtype -> Region.region
                        ) = struct

open Pattern
open Expr
open Unbound

infixr 0 $
         
fun get_region_binder (Binder (_, (_, r))) = r
                                             
fun get_region_pn pn = 
  case pn of
      PnConstr (_, _, _, r) => r
    | PnVar name => get_region_binder name
    | PnPair (pn1, pn2) => combine_region (get_region_pn pn1) (get_region_pn pn2)
    | PnTT r => r
    | PnAlias (_, _, r) => r
    | PnAnno (pn, Outer t) => combine_region (get_region_pn pn) (get_region_mt t)

fun get_region_bind fp ft bind =
  let
    val (p, t) = Unbound.unBind bind
  in
    combine_region (fp p) (ft t)
  end
    
fun get_region_e e = 
  case e of
      EVar (x, _) => get_region_var x
    | EConst (_, r) => r
    | EState (_, r) => r
    | EUnOp (_, _, r) => r
    | EBinOp (_, e1, e2) => combine_region (get_region_e e1) (get_region_e e2)
    | ETriOp (_, e1, _, e3) => combine_region (get_region_e e1) (get_region_e e3)
    | EEI (_, e, i) => combine_region (get_region_e e) (get_region_i i)
    | EET (_, e, t) => combine_region (get_region_e e) (get_region_mt t)
    | ET (_, _, r) => r
    | ENewArrayValues (_, _, r) => r
    | EAbs (_, bind, _) => get_region_bind get_region_pn get_region_e bind
    | EAbsI (_, r) => r
    | EAppConstr ((x, _), _, _, e, _) => combine_region (get_region_cvar x) (get_region_e e)
    | ECase (_, _, _, r) => r
    | EIfi (_, _, _, r) => r
    | ECaseSumbool (_, _, _, r) => r
    | ELet (_, _, r) => r
    | ESetModify (_, _, _, _, r) => r
    | EGet (_, _, r) => r
    | EMsg (_, r) => r
                                              
fun get_region_rule (pn, e) = combine_region (get_region_pn pn) (get_region_e e)

fun get_region_dec dec =
  case dec of
      DVal (_, _, r) => r
    | DValPtrn (_, _, r) => r
    | DRec (_, _, r) => r
    | DIdxDef (name, _, Outer i) => combine_region (get_region_binder name) (get_region_i i)
    | DAbsIdx2 (name, _, Outer i) => combine_region (get_region_binder name) (get_region_i i)
    | DAbsIdx (_, _, r) => r
    | DTypeDef (name, Outer t) => combine_region (get_region_binder name) (get_region_mt t)
    | DConstrDef (name, Outer x) => combine_region (get_region_binder name) (get_region_cvar x)
    | DOpen (x, _) => snd $ unInner x

fun get_region_sig (_, r) = r

fun get_region_m m =
  case m of
      ModComponents (_, r) => r
    | ModSeal (m, sg) => combine_region (get_region_m m) (get_region_sig sg)
    | ModTransparentAsc (m, sg) => combine_region (get_region_m m) (get_region_sig sg)

end
