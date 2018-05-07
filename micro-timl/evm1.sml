(* A higher-level EVM *)

structure EVM1 = struct

open MicroTiML
open Binders
       
type nat = int
type label = int

datatype word_const =
         WCTT
         | WCNat of nat
         | WCInt of int
         | WCBool of bool
         | WCByte of Char.char
         | WCiBool of bool
         | WCLabel of label

(* atomic word values *)
datatype 'ty word =
         WConst of word_const
         | WUninit of 'ty
         | WBuiltin of string * 'ty
         | WNever of 'ty
           
datatype ('idx, 'ty) inst =
         ADD
         | MUL
         | SUB
         | DIV
         | SDIV
         | MOD
         | LT
         | GT
         | SLT
         | SGT
         | EQ
         | ISZERO
         | AND
         | OR
         | BYTE
         | SHA3
         | POP
         | MLOAD
         | MSTORE
         | MSTORE8
         | SLOAD
         | SSTORE
         | JUMPI
         (* | JUMPI_i *)
         | JUMPDEST
         | PUSH of int * 'ty word inner
         | DUP of int
         | SWAP of int
         | LOG of int
         (* extensions (noops) *)
         | VALUE_AppT of 'ty inner
         | VALUE_AppI of 'idx inner
         | VALUE_Pack of 'ty inner * 'ty inner
         | VALUE_PackI of 'ty inner * 'idx inner
         | VALUE_Fold of 'ty inner
         | VALUE_AscType of 'ty inner
         | UNPACK of tbinder
         | UNPACKI of ibinder
         | UNFOLD
         | NAT2INT
         | INT2NAT
         | BYTE2INT
         (* | PRINTC *)
         (* | PACK_SUM of injector * 'ty inner *)
         | ASCTIME of 'idx inner
         | MARK_PreArray2ArrayPtr
         | MARK_PreTuple2TuplePtr
         (* | MARK_inj of 'ty inner *)
         | MACRO_init_free_ptr of int
         | MACRO_tuple_malloc of 'ty list inner
         | MACRO_tuple_assign
         | MACRO_printc
         | MACRO_array_malloc of 'ty inner * bool(* is init direction upward *)
         | MACRO_array_init_assign
         | MACRO_array_init_len
         | MACRO_int2byte
         | MACRO_inj of 'ty inner
         | MACRO_br_sum
         | MACRO_map_ptr
         | MACRO_vector_ptr
         | MACRO_vector_push_back

datatype ('idx, 'ty) insts =
         ISCons of (('idx, 'ty) inst, ('idx, 'ty) insts) bind
         | JUMP
         | RETURN
         (* only for debug/printing purpose *)
         | ISDummy of string
         | MACRO_halt of 'ty

type 'v rctx = 'v IntBinaryMap.map
                  
type ('idx, 'sort, 'kind, 'ty) hval = ((ibinder * 'sort outer, tbinder * 'kind) sum tele, ('idx * 'ty rctx * 'ty list * 'idx) * ('idx, 'ty) insts) bind

infixr 0 $

fun WInt a = WConst $ WCInt a
fun WNat a = WConst $ WCNat a
fun WiBool a = WConst $ WCiBool a
fun WLabel a = WConst $ WCLabel a
val WTT = WConst WCTT
      
infixr 5 @::
infixr 5 @@
infix  6 @+
infix  9 @!
         
fun a @:: b = ISCons $ Bind (a, b)
fun ls @@ b = foldr (op@::) b ls 
fun m @+ a = Rctx.insert' (a, m)
fun m @! k = Rctx.find (m, k)
                        
fun HCode' (binds, body) =
  Bind (Teles $ map (map_inl_inr (fn (name, s) => (IBinder name, Outer s)) (fn (name, k) => (TBinder name, k))) binds, mapSnd (fn code => JUMPDEST @:: code) body)

fun PUSH1 w = PUSH (1, Inner w)
fun PUSH1nat n = PUSH1 $ WNat n
fun PUSH32 w = PUSH (32, Inner w)
val DUP1 = DUP 1
val DUP2 = DUP 2
val DUP3 = DUP 3
val SWAP1 = SWAP 1
val SWAP2 = SWAP 2
val LOG0 = LOG 0

(* small values *)
datatype ('idx, 'ty) value =
         VWord of 'ty word
         | VAppT of ('idx, 'ty) value * 'ty
         | VAppI of ('idx, 'ty) value * 'idx
         | VPack of 'ty * 'ty * ('idx, 'ty) value
         | VPackI of 'ty * 'idx * ('idx, 'ty) value
         | VFold of 'ty * ('idx, 'ty) value
         | VAscType of ('idx, 'ty) value * 'ty

fun VConst a = VWord $ WConst a
fun VLabel a = VWord $ WLabel a
fun VNever a = VWord $ WNever a
fun VBuiltin a = VWord $ WBuiltin a

fun VAppIT (e, arg) =
    case arg of
        inl i => VAppI (e, i)
      | inr t => VAppT (e, t)
fun VAppITs (f, args) = foldl (swap VAppIT) f args
                     
fun PUSH_value v =
  case v of
      VWord w => [PUSH (32, Inner w)]
    | VAppT (v, t) => PUSH_value v @ [VALUE_AppT $ Inner t]
    | VAppI (v, i) => PUSH_value v @ [VALUE_AppI $ Inner i]
    | VPack (t', t, v) => PUSH_value v @ [VALUE_Pack (Inner t', Inner t)]
    | VPackI (t', i, v) => PUSH_value v @ [VALUE_PackI (Inner t', Inner i)]
    | VFold (t, v) => PUSH_value v @ [VALUE_Fold $ Inner t]
    | VAscType (v, t) => PUSH_value v @ [VALUE_AscType $ Inner t]

structure RctxUtil = MapUtilFn (Rctx)

end
