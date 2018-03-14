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
         | WPack of ty * ty * word
         | WFold of ty * word
           
(* small values *)
datatype value =
         VReg of reg
         | VWordVal of word
         | VAppT of value * ty
         | VPack of ty * ty * value
         | VFold of ty * value
         
datatype inst =
         IBinOpPrim of prim_expr_bin_op * reg * reg * value
         | IBr of reg * value
         | ILd of reg * (reg * projector)
         | IMallocPair of reg * (value * value)
         | IMov of reg * value
         | ISt of (reg * projector) * reg
         | IUnpack of value * name tbinder * reg
         | IInj of reg * injector * value
         | IAscTime of idx

datatype insts =
         ISCons of inst * insts rebind
         | ISJmp of value
         | ISHalt of ty

fun VConst c = VWordVal $ WConst c
                        
end
