structure MicroTiMLCosts = struct

open EVMCosts
open Operators

val C_Var = C_PUSH
val C_Const = C_PUSH
val C_Let = C_set_reg
val C_Proj = C_PUSH + C_ADD + C_MLOAD
val C_Printc = 5 * C_PUSH + C_MSTORE + C_ADD + C_LOG 0 + C_logdata
fun C_UPrim opr =
  case opr of
      EUPIntNeg () => C_PUSH + C_SUB
    | EUPBoolNeg () => C_ISZERO
    | EUPInt2Byte () => C_PUSH + C_BYTE
    | EUPByte2Int () => 0
fun C_BPrim opr =
  case opr of
       EBPIntAdd () => C_ADD
     | EBPIntMult () => C_MUL
     | EBPIntMinus () => C_SWAP + C_SUB
     | EBPIntDiv () => C_SWAP + C_SDIV
     | EBPIntMod () => C_SWAP + C_MOD
     | EBPIntLt () => C_SWAP + C_LT
     | EBPIntGt () => C_SWAP + C_GT
     | EBPIntLe () => C_GT + C_ISZERO
     | EBPIntGe () => C_LT + C_ISZERO
     | EBPIntEq () => C_EQ
     | EBPIntNEq () => C_EQ + C_ISZERO
     | EBPBoolAnd () => C_AND
     | EBPBoolOr () => C_OR

val C_ArrayLen = C_PUSH + C_SWAP + C_SUB + C_MLOAD
val C_Nat2Int = 0
val C_Int2Nat = 0
val C_StorageGet = C_SLOAD
val C_tuple_malloc = 3 * C_PUSH + C_MLOAD + C_DUP + C_ADD + C_LOG 0 + C_MSTORE
val C_Inj = 2 * C_PUSH + C_tuple_malloc + 2 * C_SWAP + 2 * C_DUP + 2 * C_MSTORE + C_ADD
val C_Fold = 0
val C_Unfold = 0
val C_Unpack = C_set_reg
val C_tuple_assign = C_DUP + C_MSTORE
val C_Pair = C_tuple_malloc + C_PUSH + C_ADD + 2 * (C_PUSH + 2 * C_SWAP + C_SUB + C_tuple_assign) + C_MARK_PreTuple2TuplePtr
val C_array_malloc = C_PUSH + C_MLOAD + C_PUSH + C_ADD + C_DUP + C_SWAP + C_PUSH + C_MUL + C_ADD + C_PUSH + C_MSTORE
val C_array_init_len = C_DUP + C_PUSH + C_SWAP + C_SUB + C_MSTORE
val C_array_ptr = C_PUSH + C_MUL + C_ADD
val C_Read = C_array_ptr + C_MLOAD
val C_map_ptr = C_PUSH + C_MSTORE + C_PUSH + C_MSTORE + C_PUSH + C_PUSH + C_SHA3
val C_MapPtr = C_map_ptr
val C_vector_ptr = C_PUSH + C_MSTORE + C_PUSH + C_PUSH + C_SHA3 + C_ADD
val C_VectorGet = C_SWAP + C_vector_ptr + C_SLOAD
val C_vector_push_back = C_DUP * 2 + C_SLOAD + C_SWAP + C_DUP + C_PUSH + C_ADD + C_SWAP + C_SSTORE + C_SWAP * 2 + C_vector_ptr + C_SSTORE
val C_VectorPushBack = C_vector_push_back + C_PUSH
val C_VectorLen = C_SLOAD
val C_VectorClear = C_PUSH + C_SWAP + C_SSTORE + C_PUSH
val C_VectorSet = C_SWAP + C_vector_ptr + C_SSTORE + C_PUSH
val C_StorageSet = C_SWAP + C_SSTORE + C_PUSH
val C_State = C_PUSH
fun C_Nat opr =
  case opr of
      EBNAdd () => C_ADD
    | EBNMult () => C_MUL
    | EBNDiv () => C_SWAP + C_DIV
    | EBNBoundedMinus () => C_SWAP + C_SUB
fun C_NatCmp opr =
    case opr of
      NCLt () => C_GT
    | NCGt () => C_LT
    | NCLe () => C_LT + C_ISZERO
    | NCGe () => C_GT + C_ISZERO
    | NCEq () => C_EQ
    | NCNEq () => C_EQ + C_ISZERO
val C_Write = C_SWAP * 2 + C_array_ptr
val C_br_sum = C_DUP + C_MLOAD + C_SWAP + C_JUMPI
val C_Case_branch_prelude = C_PUSH + C_ADD + C_MLOAD + C_set_reg
val C_Case = C_PUSH + C_br_sum + C_Case_branch_prelude
val C_Ite = C_ISZERO + C_PUSH + C_JUMPI
val C_Ifi_branch_prelude = C_set_reg
val C_Ifi = C_ISZERO + C_PUSH + C_SWAP + C_PUSH + C_JUMPI + C_Ifi_branch_prelude
fun C_NewArrayValues n = C_PUSH + C_DUP + C_array_malloc + C_SWAP + C_array_init_len + C_PUSH + n * (C_SWAP * 2 + C_array_init_assign + C_SWAP + C_POP + C_SWAP + C_PUSH + C_ADD) + C_POP + C_MARK_PreArray2ArrayPtr
val C_Halt = C_PUSH + C_SWAP + C_DUP + C_MSTORE + C_PUSH + C_SWAP + C_RETURN
                 
end
