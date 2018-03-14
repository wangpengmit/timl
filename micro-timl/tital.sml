(* Timed and Typed Assembly Language *)

structure TiTAL = struct

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
         | IUnpack of name tbinder * reg * value outer
         | IUnpackI of name ibinder * reg * value outer
         | IInj of reg * injector * value inner
         | IAscTime of idx inner

datatype insts =
         ISCons of (inst, insts) bind
         | ISJmp of value
         | ISHalt of ty

type 'v rctx = 'v IntBinaryMap.map
                  
type hval = (((name ibinder * sort outer, name tbinder * kind) sum) tele, (ty rctx * idx) * insts) bind

fun VConst c = VWordVal $ WConst c
                        
end
