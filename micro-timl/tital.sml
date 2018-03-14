(* Timed and Typed Assembly Language *)

structure TiTAL = struct

open MicroTiMLEx
open Binders

type idx = Expr.idx
type sort = Expr.sort
type bsort = Expr.bsort
type kind = bsort kind
type ty = (Expr.var, bsort, idx, sort) ty
     
type reg = int
type label = int

(* word values *)
datatype word =
         WLabel of label
         | WConst of Operators.expr_const
         | WUninit of ty
         | WAppT of word * ty
         | WAppI of word * idx
         | WPack of ty * ty * word
         | WPackI of ty * idx * word
         | WFold of ty * word
         | WBuiltin of ty
         | WNever of ty
           
(* small values *)
datatype value =
         VReg of reg
         | VWordVal of word
         | VAppT of value * ty
         | VAppI of value * idx
         | VPack of ty * ty * value
         | VPackI of ty * idx * value
         | VFold of ty * value
         
datatype inst =
         IBinOpPrim of prim_expr_bin_op * reg * reg * value inner
         | IBr of reg * value inner
         | ILd of reg * (reg * projector)
         | IMallocPair of reg * (value inner * value inner)
         | IMov of reg * value inner
         | ISt of (reg * projector) * reg
         | IUnpack of tbinder * reg * value outer
         | IUnpackI of ibinder * reg * value outer
         | IInj of reg * injector * value inner
         | IAscTime of idx inner

datatype insts =
         ISCons of (inst, insts) bind
         | ISJmp of value
         | ISHalt of ty

type 'v rctx = 'v IntBinaryMap.map
                  
type hval = ((ibinder * sort outer, tbinder * kind) sum tele, (ty rctx * idx) * insts) bind

infixr 0 $
         
fun VConst c = VWordVal $ WConst c
fun VLabel l = VWordVal $ WLabel l

fun VAppIT (e, arg) =
    case arg of
        inl i => VAppI (e, i)
      | inr t => VAppT (e, t)
fun VAppITs (f, args) = foldl (swap VAppIT) f args
                     
infixr 5 @::
infixr 5 @@
         
fun a @:: b = ISCons $ Bind (a, b)
fun ls @@ b = foldr (op@::) b ls 
                        
fun HCode' (binds, body) : hval =
  Bind (Teles $ map (map_inl_inr (fn (name, s) => (IBinder name, Outer s)) (fn (name, k) => (TBinder name, k))) binds, body)

fun IBinOpPrim' (opr, rd, rs, v) = IBinOpPrim (opr, rd, rs, Inner v)
fun IBr' (r, v) = IBr (r, Inner v)
fun IMov' (r, v) = IMov (r, Inner v)
fun IMallocPair' (r, (v1, v2)) = IMallocPair (r, (Inner v1, Inner v2))
fun IUnpack' (name, r, v) = IUnpack (TBinder name, r, Outer v)
fun IUnpackI' (name, r, v) = IUnpackI (IBinder name, r, Outer v)
fun IInj' (r, inj, v) = IInj (r, inj, Inner v)
fun IAscTime' i = IAscTime (Inner i)
                               
end
