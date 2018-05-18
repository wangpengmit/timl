structure EVMCosts = struct

val C_base = 2
val C_verylow = 3
val C_low = 5
val C_mid = 8
val C_high = 10
val C_sset = 20000
val C_logtopic = 375
val C_logdata = 8
val C_sha3word = 6
val C_memory = 3
                   
val C_POP = C_base
              
val C_ADD = C_verylow
val C_SUB = C_verylow
val C_LT = C_verylow
val C_GT = C_verylow
val C_SLT = C_verylow
val C_SGT = C_verylow
val C_EQ = C_verylow
val C_ISZERO = C_verylow
val C_AND = C_verylow
val C_OR = C_verylow
val C_BYTE = C_verylow
val C_MLOAD = C_verylow
val C_MSTORE = C_verylow
val C_MSTORE8 = C_verylow
val C_PUSH = C_verylow
val C_DUP = C_verylow
val C_SWAP = C_verylow
                
val C_MUL = C_low
val C_DIV = C_low
val C_SDIV = C_low
val C_MOD = C_low
              
val C_JUMPI = C_high
                
val C_SHA3 = 30
val C_SLOAD = 200
val C_SSTORE = C_sset (* can't do value-sensitive analysis, so we'll just use the highest cost *)
val C_JUMPDEST = 1
val C_VALUE_AppT = 0
val C_VALUE_AppI = 0
val C_VALUE_Pack = 0
val C_VALUE_PackI = 0
val C_VALUE_Fold = 0
val C_VALUE_AscType = 0
val C_UNPACK = 0
val C_UNPACKI = 0
val C_UNFOLD = 0
val C_NAT2INT = 0
val C_INT2NAT = 0
val C_BYTE2INT = 0
(* val C_PRINTC = 0 *)
(* val C_PACK_SUM = 0 *)
val C_ASCTIME = 0
val C_ASCSPACE = 0
val C_MARK_PreArray2ArrayPtr = 0
val C_MARK_PreTuple2TuplePtr = 0
                                 
val C_JUMP = C_mid
val C_RETURN = 0
val C_ISDummy = 0
                      
fun C_LOG n = 375 + n * C_logtopic
                         
val C_set_reg = C_PUSH + C_MSTORE
val C_array_init_assign = 3 * C_DUP + C_ADD + C_MSTORE
                                                
val C_New_loop_test = 2 * C_PUSH + C_DUP + C_ISZERO + C_JUMPI
val C_New_loop = C_New_loop_test + 2 * C_PUSH + C_UNPACKI + C_POP + C_SWAP + C_SUB + C_array_init_assign + C_JUMP
val C_New_post_loop = C_UNPACKI + 3 * C_POP + C_SWAP + C_MARK_PreArray2ArrayPtr + C_set_reg
                                                                                
end
