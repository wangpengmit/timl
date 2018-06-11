structure MicroTiMLCosts = struct

open EVMCosts
open Operators

val C_Var = max C_get_reg C_PUSH
val C_Const = C_PUSH
val C_Let = C_set_reg
val C_Proj = C_PUSH + C_ADD + C_MLOAD
val C_TupleProj = C_PUSH + C_ADD + C_MLOAD
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
val C_tuple_malloc = C_PUSH + C_MLOAD + C_DUP + C_PUSH + C_ADD + C_PUSH + C_MSTORE
val C_Inj = 2 * C_PUSH + C_tuple_malloc + 2 * C_SWAP + 2 * C_DUP + 2 * C_MSTORE + C_ADD
val C_Fold = 0
val C_Unfold = 0
val C_Unpack = C_set_reg
val C_tuple_assign = C_DUP + C_MSTORE
val C_Pair = C_tuple_malloc + C_PUSH + C_ADD + 2 * (C_PUSH + 2 * C_SWAP + C_SUB + C_tuple_assign) + C_MARK_PreTuple2TuplePtr
fun C_Tuple n = C_tuple_malloc + C_PUSH + C_ADD + n * (C_PUSH + 2 * C_SWAP + C_SUB + C_tuple_assign) + C_MARK_PreTuple2TuplePtr
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
val C_Ifi_branch_prelude = C_set_reg
val C_Ifi = C_ISZERO + C_PUSH + C_SWAP + C_PUSH + C_JUMPI + C_Ifi_branch_prelude
fun C_NewArrayValues n = C_PUSH + C_DUP + C_array_malloc + C_SWAP + C_array_init_len + C_PUSH + n * (C_SWAP * 2 + C_array_init_assign + C_SWAP + C_POP + C_SWAP + C_PUSH + C_ADD) + C_POP + C_MARK_PreArray2ArrayPtr
val C_Never = C_PUSH
val C_Builtin = C_PUSH
val C_Halt = C_PUSH + C_SWAP + C_DUP + C_MSTORE + C_PUSH + C_SWAP + C_RETURN
val C_EHalt = C_Halt + C_Var
                                                                      
val C_EProj = C_Proj + C_Var + C_Let
val C_EPair = C_Pair + 2 * C_Var + C_Let
val C_EPack = C_Let + C_Var
val C_EUnpack = C_Unpack + C_Var
fun C_ETuple len = C_Tuple len + len * C_Var + C_Let
                 
fun C_Abs_BeforeCC n_free_vars = C_ETuple n_free_vars + C_EPair + C_EPack
fun M_Abs_BeforeCC n_free_vars = 2 + n_free_vars
val C_App_BeforeCodeGen = 2 * C_Var + C_set_reg + C_JUMP
val C_App_BeforeCC = C_App_BeforeCodeGen + C_EUnpack + 2 * C_EProj + C_EPair
val M_App_BeforeCC = 2
val C_Abs_Inner_BeforeCodeGen = C_JUMPDEST
(* fun C_Abs_Inner_BeforeCC n_free_vars = 2 * (C_Let + C_Proj + C_Var) + (C_Let + C_Pair + 2 * C_Var) + n_free_vars * (C_Let + C_TupleProj + C_Var) *)
fun C_Abs_Inner_BeforeCC n_free_vars = C_Abs_Inner_BeforeCodeGen + 2 * C_EProj + C_EPair + C_EPack + n_free_vars * (C_Let + C_TupleProj + C_Var)
fun M_Abs_Inner_BeforeCC n_free_vars = 2
fun C_Abs_Inner_BeforeCPS n_fvars = C_Abs_Inner_BeforeCC n_fvars + 2 * C_EProj + C_App_BeforeCC(*todo: if the last computation of the body is EApp(IT)/ECase(Ite), then this C_App_BeforeCC is not needed*)
fun M_Abs_Inner_BeforeCPS n_fvars = M_Abs_Inner_BeforeCC n_fvars + M_App_BeforeCC
fun C_AbsI_Inner_BeforeCPS n_fvars = C_Abs_Inner_BeforeCC n_fvars + C_App_BeforeCC
fun M_AbsI_Inner_BeforeCPS n_fvars = M_Abs_Inner_BeforeCC n_fvars + M_App_BeforeCC
fun C_App_BeforeCPS n_live_vars = C_App_BeforeCC + C_EPair + C_Abs_BeforeCC n_live_vars + C_Abs_Inner_BeforeCC n_live_vars
fun M_App_BeforeCPS n_live_vars = M_App_BeforeCC + 2 + M_Abs_BeforeCC n_live_vars + M_Abs_Inner_BeforeCC n_live_vars
fun C_AppI_BeforeCPS n_live_vars = C_App_BeforeCC + C_Abs_BeforeCC n_live_vars + C_Abs_Inner_BeforeCC n_live_vars
fun M_AppI_BeforeCPS n_live_vars = M_App_BeforeCC + M_Abs_BeforeCC n_live_vars + M_Abs_Inner_BeforeCC n_live_vars
val C_Ite_BeforeCodeGen = C_Var(*no one else is accounting for this variable read*) + C_ISZERO + C_PUSH + C_JUMPI
val C_Case_BeforeCodeGen = C_Var + C_PUSH + C_br_sum + C_Case_branch_prelude
fun C_Ite_BeforeCPS n_live_vars =  C_Ite_BeforeCodeGen +  C_Abs_BeforeCC n_live_vars + C_App_BeforeCC + C_Abs_Inner_BeforeCC n_live_vars
fun M_Ite_BeforeCPS n_live_vars =  M_Abs_BeforeCC n_live_vars + M_App_BeforeCC + M_Abs_Inner_BeforeCC n_live_vars
fun C_Case_BeforeCPS n_live_vars = C_Case_BeforeCodeGen
fun M_Case_BeforeCPS n_live_vars = 0                    

val C_EVar = 0 (* each computation is responsible for accounting for reading from variables, so here the cost is zero *)
val C_EConst = C_Const + C_Let
val C_EPrintc = C_Printc + C_Var + C_Let
fun C_EUPrim opr = C_UPrim opr + C_Var + C_Let
val C_EArrayLen = C_ArrayLen + C_Var + C_Let
val C_ENat2Int = C_Nat2Int + C_Var + C_Let
val C_EInt2Nat = C_Int2Nat + C_Var + C_Let
val C_EStorageGet = C_StorageGet + C_Var + C_Let
val C_EVectorLen = C_VectorLen + C_Var + C_Let
val C_EVectorClear = C_VectorClear + C_Var + C_Let
val C_New_pre_loop = 2 * C_SWAP + 2 * C_DUP + C_array_malloc + C_array_init_len + 2 * C_PUSH + C_JUMP
val C_ENew_order0 = C_New_pre_loop + C_New_loop_test + C_New_post_loop + (2 * C_Var + C_Let)
val C_ENew_order1 = C_New_loop
val C_ERead = C_Read + 2 * C_Var + C_Let
fun C_ENat opr = C_Nat opr + 2 * C_Var + C_Let
fun C_EBPrim opr = C_BPrim opr + 2 * C_Var + C_Let
fun C_ENatCmp opr = C_NatCmp opr + 2 * C_Var + C_Let
val C_EMapPtr = C_MapPtr + 2 * C_Var + C_Let
val C_EVectorGet = C_VectorGet + 2 * C_Var + C_Let
val C_EVectorPushBack = C_VectorPushBack + 2 * C_Var + C_Let
val C_EStorageSet = C_StorageSet + 2 * C_Var + C_Let
val C_EState = C_State + C_Let
val C_EVectorSet = C_VectorSet + 3 * C_Var + C_Let
val C_EWrite = C_Write + 3 * C_Var + C_Let
val C_ENever = C_Never + C_Let
val C_EBuiltin = C_Builtin + C_Let
fun C_ENewArrayValues len = C_NewArrayValues len + len * C_Var + C_Let
val C_EInj = C_Inj + C_Var + C_Let
val C_EFold = C_Fold + C_Var + C_Let
val C_EUnfold = C_Unfold + C_Var + C_Let
val C_ETupleProj = C_TupleProj + C_Var + C_Let

open Util
       
infixr 0 $
         
val () = println $ "C_EProj = " ^ str_int C_EProj
val () = println $ "C_EPair = " ^ str_int C_EPair
val () = println $ "C_EPack = " ^ str_int C_EPack
val () = println $ "C_Let = " ^ str_int C_Let
val () = println $ "C_Var = " ^ str_int C_Var
val () = println $ "C_Proj = " ^ str_int C_Proj
val () = println $ "C_Pair = " ^ str_int C_Pair
                                         
end
