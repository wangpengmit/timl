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
fun a %** b = ExpI (a, b)
                   
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
fun TSomeNat_packed () = TExistsI $ IBindAnno ((("__VC", dummy), MakeSubset ("__VC", BSUnit, True dummy)), TNat $ IV 0)
fun TSomeNat_packed2 () = TExistsI $ IBindAnno ((("n", dummy), MakeSubset ("n", BSNat, IV 0 %< ConstIN (2, dummy) %** ("256", dummy))), TSomeNat_packed ())
fun TSomeNat () = TRec $ TBindAnno ((("some_nat", dummy), KType), TSomeNat_packed2 ())
end
           
val Itrue = TrueI dummy
val Ifalse = FalseI dummy
                 
end
