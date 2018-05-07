(* Utilities for MicroTiML specialized to Expr *)

structure MicroTiMLUtilTiML = struct

open Expr
open MicroTiMLLongId
open MicroTiMLUtil

infixr 0 $
       
infix 9 %@
infix 8 %^
infix 7 %*
infix 6 %+ 
infix 4 %<=
infix 4 %<
infix 4 %>=
infix 4 %>
infix 4 %=
infixr 3 /\
infixr 2 \/
infixr 1 -->
infix 1 <->

infix 8 %**
fun a %** b = BinOpI (ExpNI, a, b)
                   
val unTAbsT = unBindAnnoName
                
fun whnf ctx t =
    case t of
        TAppT (t1, t2) =>
        let
          val t1 = whnf ctx t1
        in
          case t1 of
              TAbsT data =>
              let
                val (_, (_, t1)) = unTAbsT data
              in
                whnf ctx $ subst0_t_t t2 t1
              end
            | _ => TAppT (t1, t2)
        end
      | TAppI (t, i) =>
        let
          val t = whnf ctx t
        in
          case t of
              TAbsI data =>
              let
                val (_, (_, t)) = unTAbsT data
              in
                whnf ctx $ subst0_i_t i t
              end
            | _ => TAppI (t, i)
        end
      | TVar x => TVar x (* todo: look up type aliasing in ctx *)
      | _ => t

fun MakeSubset (name, s, p) = Subset ((s, dummy), Bind.Bind ((name, dummy), p), dummy)
local
  fun IV n = VarI (ID (n, dummy), [])
in
fun TSomeNat_packed () = TExistsI $ IBindAnno ((("__VC", dummy), MakeSubset ("__VC", BSUnit, True dummy)), TNat $ IV 1)
fun TSomeNat_packed2 () = TExistsI $ IBindAnno ((("n", dummy), MakeSubset ("n", BSNat, IV 0 %< ConstIN (2, dummy) %** ConstIN (256, dummy))), TSomeNat_packed ())
fun TSomeNat () = TRec $ TBindAnno ((("some_nat", dummy), KType), TSomeNat_packed2 ())
end
           
val Itrue = TrueI dummy
val Ifalse = FalseI dummy
                 
fun INat c = ConstIN (c, dummy)
fun ITime c = ConstIT (c, dummy)
fun IBool c = IConst (ICBool c, dummy)
                     
fun TiBoolConst b = TiBool $ IBool b
                           
val SState = Basic (Base BSState, dummy)
                                
fun assert_TArrow t =
  case t of
      TArrow a => a
    | _ => raise assert_fail $ "assert_TArrow; got: " ^ (ExportPP.pp_t_to_string NONE $ ExportPP.export_t NONE ([], []) t)
                                                          
infix 6 @++
fun m @++ m' = StMapU.union m m'
                            
infix 6 @%++
val op@%++ = ISet.union
         
fun decompose_state i =
  let
    val is = collect_IUnion i
    val (vars_info, maps) = partitionSum
                              (fn i =>
                                  case i of
                                      VarI (ID (n, _), ls) => inl (n, ls)
                                    | IState m => inr m
                              ) is
    val m = foldl (fn (m, acc) => acc @++ m) StMap.empty maps
    val vars = ISetU.to_set $ map fst vars_info
    val vars_info = IMapU.fromList vars_info
  in
    (vars, vars_info, m)
  end
    
fun compose_state (vars, vars_info, m) =
  combine_IUnion (IState m) $ map (fn n => VarI (ID (n, dummy), IMapU.must_find vars_info n)) $ ISetU.to_list vars
                 
fun IUnion_simp (i1, i2) =
  let
    val (vars1, vars_info1, map1) = decompose_state i1
    val (vars2, vars_info2, map2) = decompose_state i2
  in
    compose_state (vars1 @%++ vars2, IMapU.union vars_info1 vars_info2, map1 @++ map2)
  end
    
end
