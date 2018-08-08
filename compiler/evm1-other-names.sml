structure EVM1OtherNames = struct

open Util
open EVM1

infixr 0 $
       
fun TupleMalloc ts = MACRO_tuple_malloc $ Inner ts
val Swap = SWAP
val Swap1 = SWAP 1
val Swap2 = SWAP 2
val Swap3 = SWAP 3
val Dup = DUP
val Dup1 = DUP 1
val Dup2 = DUP 2
val Dup3 = DUP 3
val Dup4 = DUP 4
fun Push n = PUSH32 $ WNat n
fun Push_l l = PUSH32 $ WLabel l
fun PushN_large n i = PUSH (n, Inner $ WInt i)
fun Push_large i = PushN_large 32 i
val Add = ADD ()
val Sub = SUB ()
val Mul = MUL ()
(* val Div = DIV () *)
val Mod = MOD ()
val MStore = MSTORE ()
val MLoad = MLOAD ()
val Pop = POP ()
fun ArrayMalloc (w, t, b) = MACRO_array_malloc (w, Inner t, b)
val ArrayInitLen = MACRO_array_init_len ()
val CallDataLoad = CALLDATALOAD ()
val CallDataCopy = CALLDATACOPY ()
val CallDataSize = CALLDATASIZE ()
val Eq = EQ ()
val Lt = LT ()
val Jumpi = JUMPI ()
val Jump = InstJUMP ()
val Return = InstRETURN ()
val Revert = InstREVERT ()
val JumpDest = JUMPDEST ()
       
end
