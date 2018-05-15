structure EVMCosts = struct

open Util
open EVM1

infixr 0 $
         
val G_base = 2
val G_verylow = 3
val G_low = 5
val G_mid = 8
val G_high = 10
val G_sset = 20000
val G_logdata = 8
val G_sha3word = 6
                   
fun G_inst b =
  case b of
      POP () => G_base
                  
    | ADD () => G_verylow
    | SUB () => G_verylow
    | LT () => G_verylow
    | GT () => G_verylow
    | SLT () => G_verylow
    | SGT () => G_verylow
    | EQ () => G_verylow
    | ISZERO () => G_verylow
    | AND () => G_verylow
    | OR () => G_verylow
    | BYTE () => G_verylow
    | MLOAD () => G_verylow
    | MSTORE () => G_verylow
    | MSTORE8 () => G_verylow
    | PUSH _ => G_verylow
    | DUP _ => G_verylow
    | SWAP _ => G_verylow
                  
    | MUL () => G_low
    | DIV () => G_low
    | SDIV () => G_low
    | MOD () => G_low
                  
    | JUMPI () => G_high
                    
    | SHA3 () => 30
    | SLOAD () => 200
    | SSTORE () => G_sset (* can't do value-sensitive analysis, so we'll just use the highest cost *)
    | JUMPDEST () => 1
    | LOG _ => 375
    (* extensions (noops) *)
    | VALUE_AppT _ => 0
    | VALUE_AppI _ => 0
    | VALUE_Pack _ => 0
    | VALUE_PackI _ => 0
    | VALUE_Fold _ => 0
    | VALUE_AscType _ => 0
    | UNPACK _ => 0
    | UNPACKI _ => 0
    | UNFOLD _ => 0
    | NAT2INT _ => 0
    | INT2NAT _ => 0
    | BYTE2INT _ => 0
    (* | PRINTC _ => 0 *)
    (* | PACK_SUM _ => 0 *)
    | ASCTIME _ => 0
    | MARK_PreArray2ArrayPtr _ => 0
    | MARK_PreTuple2TuplePtr _ => 0
    (* | MARK_inj _ => 0 *)
    | MACRO_init_free_ptr _ => raise Impossible $ "G_inst() on MACRO_init_free_ptr"
    | MACRO_tuple_malloc _ => raise Impossible $ "G_inst() on MACRO_tuple_malloc"
    | MACRO_tuple_assign _ => raise Impossible $ "G_inst() on MACRO_tuple_assign"
    | MACRO_printc _ => raise Impossible $ "G_inst() on MACRO_printc"
    | MACRO_array_malloc _ => raise Impossible $ "G_inst() on MACRO_array_malloc"
    | MACRO_array_init_assign _ => raise Impossible $ "G_inst() on MACRO_array_init_assign"
    | MACRO_array_init_len _ => raise Impossible $ "G_inst() on MACRO_array_init_len"
    | MACRO_int2byte _ => raise Impossible $ "G_inst() on MACRO_int2byte"
    | MACRO_inj _ => raise Impossible $ "G_inst() on MACRO_inj"
    | MACRO_br_sum _ => raise Impossible $ "G_inst() on MACRO_br_sum"
    | MACRO_map_ptr _ => raise Impossible $ "G_inst() on MACRO_map_ptr"
    | MACRO_vector_ptr _ => raise Impossible $ "G_inst() on MACRO_vector_ptr"
    | MACRO_vector_push_back _ => raise Impossible $ "G_inst() on MACRO_vector_push_back"
                                        
fun G_insts insts =
  case insts of
      ISCons bind =>
      let
        val (i, is) = unBind bind
      in
        G_inst i + G_insts is
      end
    | JUMP () => G_mid
    | RETURN () => 0
    (* only for debug/printing purpose *)
    | ISDummy _ => 0
    | MACRO_halt _ => raise Impossible $ "G_insts() on MACRO_halt"
                           
end
