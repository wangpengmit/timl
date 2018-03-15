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

(* atomic word values *)
datatype word =
         WLabel of label
         | WConst of Operators.expr_const
         | WUninit of ty
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

datatype inst_un_op =
         IUMov
         | IUBr
         | IUUnfold
             
datatype inst_bin_op =
         IBPrim of prim_expr_bin_op
         | IBNatAdd
         | IBNew
         | IBRead
         | IBWrite
             
datatype inst =
         IBinOp of inst_bin_op * reg * reg * value inner
         | IUnOp of inst_un_op * reg * value inner
         | IMallocPair of reg * (value inner * value inner)
         | ILd of reg * (reg * projector)
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
         
fun VConst a = VWordVal $ WConst a
fun VLabel a = VWordVal $ WLabel a
fun VNever a = VWordVal $ WNever a
fun VBuiltin a = VWordVal $ WBuiltin a

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

fun IBinOp' (opr, rd, rs, v) = IBinOp (opr, rd, rs, Inner v)
fun IMov' (r, v) = IUnOp (IUMov, r, Inner v)
fun IBr' (r, v) = IUnOp (IUBr, r, Inner v)
fun IUnfold' (r, v) = IUnOp (IUUnfold, r, Inner v)
fun IMallocPair' (r, (v1, v2)) = IMallocPair (r, (Inner v1, Inner v2))
fun IUnpack' (name, r, v) = IUnpack (TBinder name, r, Outer v)
fun IUnpackI' (name, r, v) = IUnpackI (IBinder name, r, Outer v)
fun IInj' (r, inj, v) = IInj (r, inj, Inner v)
fun IAscTime' i = IAscTime (Inner i)
                               
end
