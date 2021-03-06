(* A higher-level EVM *)

structure EVM1 = struct

open MicroTiML
open Binders
       
type nat = int
type label = int

datatype word_const =
         WCTT of unit
         | WCInt of LargeInt.int
         | WCNat of nat
         | WCBool of bool
         | WCiBool of bool
         | WCByte of Char.char
         | WCLabel of label
         | WCState of int

(* atomic word values *)
datatype 'ty word =
         WConst of word_const
         | WUninit of 'ty (* todo: no longer needed? *)
         | WBuiltin of string * 'ty
         | WNever of 'ty
           
datatype ('idx, 'ty) inst =
         ADD of unit
         | MUL of unit
         | SUB of unit
         | DIV of unit
         | SDIV of unit
         | MOD of unit
         | SMOD of unit
         | EXP of unit
         | LT of unit
         | GT of unit
         | SLT of unit
         | SGT of unit
         | EQ of unit
         | ISZERO of unit
         | AND of unit
         | OR of unit
         | XOR of unit
         | NOT of unit
         | BYTE of unit
         | SHA3 of unit
         | ORIGIN of unit
                       
         | ADDRESS of unit
         | BALANCE of unit
         | CALLER of unit
         | CALLVALUE of unit
         | CALLDATASIZE of unit
         | CODESIZE of unit
         | GASPRICE of unit
         | COINBASE of unit
         | TIMESTAMP of unit
         | NUMBER of unit
         | DIFFICULTY of unit
         | GASLIMIT of unit
                         
         | POP of unit
         | MLOAD of unit
         | MSTORE of unit
         | MSTORE8 of unit
         | SLOAD of unit
         | SSTORE of unit
         | JUMPI of unit
         | JUMPDEST of unit
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
         | UNFOLD of unit
         | NAT2INT of unit
         | INT2NAT of unit
         | BYTE2INT of unit
         (* | PRINTC of unit *)
         (* | PACK_SUM of injector * 'ty inner *)
         | InstRestrictPtr of int
         | ASCTIME of 'idx inner
         | ASCSPACE of 'idx inner
         | MARK_PreArray2ArrayPtr of unit
         | MARK_PreTuple2TuplePtr of unit
         (* | MARK_inj of 'ty inner *)
         | MACRO_init_free_ptr of int
         | MACRO_tuple_malloc of 'ty list inner
         | MACRO_tuple_assign of unit
         | MACRO_printc of unit
         | MACRO_array_malloc of int * 'ty inner * bool(* is init direction upward *)
         | MACRO_array_init_assign of int
         | MACRO_array_init_len of unit
         | MACRO_int2byte of unit
         | MACRO_int2bool of unit
         | MACRO_inj of 'ty inner
         | MACRO_br_sum of unit
         | MACRO_map_ptr of unit
         | MACRO_vector_ptr of unit
         | MACRO_vector_push_back of unit
         | Dispatch of (LargeInt.int(*function signature*) * 'ty inner(*argument type*) * 'ty inner(*return type*) * int(*reg for function closure*)) list
         | DebugLog of 'ty inner
         | CALLDATALOAD of unit
         | CALLDATACOPY of unit
         | InstJUMP of unit
         | InstRETURN of unit
         | InstREVERT of unit

datatype ('idx, 'ty) insts =
         ISCons of (('idx, 'ty) inst, ('idx, 'ty) insts) bind
         | JUMP of unit
         | RETURN of unit
         | REVERT of unit
         (* only for debug/printing purpose *)
         | ISDummy of string
         | MACRO_halt of bool(*successful?*) * 'ty

type 'v rctx = 'v IntBinaryMap.map
                  
type ('idx, 'sort, 'ty, 'kind) hval = ((ibinder * 'sort outer, tbinder * 'kind outer) sum tele, ('idx * 'ty rctx * 'ty list * ('idx * 'idx)) * ('idx, 'ty) insts) bind

infixr 0 $

fun WInt a = WConst $ WCInt a
fun WNat a = WConst $ WCNat a
fun WiBool a = WConst $ WCiBool a
fun WLabel a = WConst $ WCLabel a
val WTT = WConst (WCTT ())
      
infixr 5 @::
infixr 5 @@
infix  6 @+
infix  9 @!
         
fun a @:: b = ISCons $ Bind (a, b)
fun ls @@ b = foldr (op@::) b ls 
fun m @+ a = Rctx.insert' (a, m)
fun m @! k = Rctx.find (m, k)
                        
fun HCode' (binds, body) =
  Bind (Teles $ map (map_inl_inr (fn (name, s) => (IBinder name, Outer s)) (fn (name, k) => (TBinder name, Outer k))) binds, mapSnd (fn code => JUMPDEST () @:: code) body)

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
fun VState a = VConst $ WCState a

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
