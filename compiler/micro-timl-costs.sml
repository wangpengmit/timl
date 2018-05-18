structure MicroTiMLCost = struct

val C_Proj = G_PUSH + G_ADD + G_MLOAD
val C_Printc = 5 * G_PUSH + G_MSTORE + G_ADD + G_LOG 0 + G_logdata
fun C_UPrim opr =
    case opr of
        EUPIntNeg () => G_PUSH + G_SUB
      | EUPBoolNeg () => G_ISZERO
      | EUPInt2Byte () => G_PUSH + G_BYTE
      | EUPByte2Int () => 0
val C_ArrayLen = G_PUSH + G_SWAP + G_SUB + G_MLOAD
val C_Nat2Int = 0
val C_Int2Nat = 0
val C_StorageGet = G_SLOAD
val C_tuple_malloc = 3 * G_PUSH + G_MLOAD + G_DUP + G_ADD + G_LOG 0 + G_MSTORE
val C_Inj = 2 * G_PUSH + C_tuple_malloc + 2 * G_SWAP + 2 * G_DUP + 2 * G_MSTORE + G_ADD
val C_Fold = 0
val C_Unfold = 0
val C_set_reg = G_PUSH + G_MSTORE
    
end
