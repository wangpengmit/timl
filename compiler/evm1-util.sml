structure EVM1Util = struct

open EVM1

infixr 0 $
infixr 5 @@
         
fun inline_macro_inst (params as (PUSH_reg, PUSH_tuple_offset, scratch, reg_addr, TUnit)) (inst : ('a, 'b) inst) =
  let
    val inline_macro_inst = inline_macro_inst params
  in
  case inst of
      MACRO_init_free_ptr num_regs => [PUSH_reg $ reg_addr num_regs, PUSH1nat 0, MSTORE ()]
    | MACRO_tuple_malloc ts => [PUSH1nat 0, MLOAD (), DUP1, PUSH_tuple_offset $ 32 * (length $ unInner ts), ADD (), PUSH1 $WNat 0, MSTORE ()]
    | MACRO_tuple_assign () => [DUP2, MSTORE ()]
    | MACRO_printc () => [PUSH_reg scratch, MSTORE (), PUSH1nat 1, PUSH_reg scratch, PUSH1nat 31, ADD (), LOG0, PUSH1 WTT]
    | MACRO_array_malloc (t, b) => [PUSH1nat 0, MLOAD (), PUSH1nat 32, ADD (), DUP1, SWAP2, PUSH1nat 32, MUL (), ADD (), PUSH1nat 0, MSTORE ()]
    | MACRO_array_init_assign () => [DUP3, DUP3, DUP3, ADD (), MSTORE ()]
    | MACRO_array_init_len () => [DUP2, PUSH1nat 32, SWAP1, SUB (), MSTORE ()]
    | MACRO_int2byte () => [PUSH1nat 31, BYTE ()]
    | MACRO_inj t_other =>
      inline_macro_inst (MACRO_tuple_malloc $ Inner [TUnit, TUnit](*only length matters operationally*)) @
      [SWAP1, DUP2, MSTORE (), SWAP1, DUP2, PUSH1nat 32, ADD (), MSTORE ()(* , PACK_SUM (inj, Inner t_other) *)]
    | MACRO_br_sum () => [DUP2, MLOAD (), SWAP1, JUMPI ()]
    | MACRO_map_ptr () => [PUSH_reg $ scratch, MSTORE (), PUSH_reg $ scratch+32, MSTORE (), PUSH1nat 64, PUSH_reg $ scratch, SHA3 ()]
    | MACRO_vector_ptr () => [PUSH_reg $ scratch, MSTORE (), PUSH1nat 32, PUSH_reg $ scratch, SHA3 (), ADD ()]
    | MACRO_vector_push_back () => [DUP2, DUP1, SLOAD (), SWAP1, DUP2, PUSH1nat 1, ADD (), SWAP1, SSTORE (), SWAP1, SWAP2] @ inline_macro_inst (MACRO_vector_ptr ()) @ [SSTORE ()]
    | _ => [inst]
  end

fun inline_macro_insts (params as (inline_macro_inst, PUSH_reg, scratch)) insts =
  let
    val inline_macro_insts = inline_macro_insts params
  in
    case insts of
        ISCons bind =>
        let
          val (inst, I) = unBind bind
        in
          inline_macro_inst inst @@ inline_macro_insts I
        end
      | MACRO_halt t => [PUSH_reg scratch, SWAP1, DUP2, MSTORE (), PUSH1nat 32, SWAP1] @@ RETURN ()(* t *)
      | _ => insts
  end
                                                                     
open MicroTiMLUtilTiML
open Expr
infix 6 %-
fun a %- b = IBinOp (IBBoundedMinus (), a, b)
        
fun N a = INat (a, dummy)
fun T a = ITime (a, dummy)
val N32 = N 32

fun TCell t = TStorageTuplePtr ([t], N 0)
                        
fun assert_TTuple t =
  case t of
      TTuple a => a
    | _ => raise assert_fail $ "assert_TTuple; got: " ^ (ExportPP.pp_t_to_string NONE $ ExportPP.export_t NONE ([], []) t)
                                                          
fun assert_TStorageTuplePtr t =
  case t of
      TTuplePtr (ts, i, true) => (ts, i)
    | _ => raise assert_fail $ "assert_TStorageTuplePtr; got: " ^ (ExportPP.pp_t_to_string NONE $ ExportPP.export_t NONE ([], []) t)
                                                          
end
