structure EVMCosts = struct

val C_base = 2
val C_verylow = 3
val C_low = 5
val C_mid = 8
val C_high = 10
(* val C_sset = 20000 *)
val C_sset = 5000
val C_sreset = 5000
val R_sclear = 15000
val C_logtopic = 375
val C_logdata = 8
val C_sha3word = 6
val C_memory = 3
                   
val C_POP = C_base
val C_ORIGIN = C_base
val C_ADDRESS = C_base
val C_BALANCE = C_base
val C_CALLER = C_base
val C_CALLVALUE = C_base
val C_CALLDATASIZE = C_base
val C_CODESIZE = C_base
val C_GASPRICE = C_base
val C_COINBASE = C_base
val C_TIMESTAMP = C_base
val C_NUMBER = C_base
val C_DIFFICULTY = C_base
val C_GASLIMIT = C_base
              
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
val C_XOR = C_verylow
val C_NOT = C_verylow
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
                         
val C_get_reg = C_PUSH + C_MLOAD
val C_set_reg = C_PUSH + C_MSTORE
fun C_MSTORE_n w =
  if w = 32 then
    C_MSTORE
  else if w = 1 then
    C_MSTORE8
  else raise Util.Impossible "C_MSTORE_n(): w <> 32 or 1"
fun C_array_init_assign w = 3 * C_DUP + C_ADD + C_MSTORE_n w
                                                
val C_New_loop_test = C_JUMPDEST + 2 * C_PUSH + C_DUP + C_ISZERO + C_JUMPI
fun C_New_loop w = C_New_loop_test + 2 * C_PUSH + C_UNPACKI + C_POP + C_SWAP + C_SUB + C_array_init_assign w + C_JUMP
val C_New_post_loop = C_JUMPDEST + C_UNPACKI + 3 * C_POP + C_SWAP + C_MARK_PreArray2ArrayPtr + C_set_reg

val C_Ifi_branch_prelude = C_set_reg
val C_Case_branch_prelude = C_PUSH + C_ADD + C_MLOAD + C_set_reg

val C_exp = 10
val C_expbyte = 50
                                  
val C_EXP_max = C_exp + C_expbyte * 8

(* val self_destruct_cost = C_selfdestruct + C_newaccount? *)
                                      
end
