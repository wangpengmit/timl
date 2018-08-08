structure EVM1Assemble = struct

open EVM1

infixr 0 $

infix  6 @+
infix  9 @!
         
fun wc2i c =
  case c of
      WCTT () => inl 0
    | WCNat n => inl n
    | WCInt n => inr n
    | WCBool b => inl $ b2i b
    | WCByte c => inl $ Char.ord c
    | WCiBool b => inl $ b2i b
    | WCLabel n => inl $ n
    | WCState n => inl $ n
                       
fun w2i w =
  case w of
      WConst c => wc2i c
    | _ => inl 0

fun enc inst =
  let
    fun macro name = raise Impossible $ "Can't assemble instruction " ^ name
  in                                                                        
    case inst of
        ADD () => "01"
      | MUL () => "02"
      | SUB () => "03"
      | DIV () => "04"
      | SDIV () => "05"
      | MOD () => "06"
      | SMOD () => "07"
      | EXP () => "0a"
      | LT () => "10"
      | GT () => "11"
      | SLT () => "12"
      | SGT () => "13"
      | EQ () => "14"
      | ISZERO () => "15"
      | AND () => "16"
      | OR () => "17"
      | XOR () => "18"
      | NOT () => "19"
      | BYTE () => "1a"
      | SHA3 () => "20"
      | ADDRESS () => "30"
      | BALANCE () => "31"
      | ORIGIN () => "32"
      | CALLER () => "33"
      | CALLVALUE () => "34"
      | CALLDATALOAD () => "35"
      | CALLDATASIZE () => "36"
      | CALLDATACOPY () => "37"
      | CODESIZE () => "38"
      | GASPRICE () => "3a"
      | COINBASE () => "41"
      | TIMESTAMP () => "42"
      | NUMBER () => "43"
      | DIFFICULTY () => "44"
      | GASLIMIT () => "45"
      | POP () => "50"
      | MLOAD () => "51"
      | MSTORE () => "52"
      | MSTORE8 () => "53"
      | SLOAD () => "54"
      | SSTORE () => "55"
      | JUMPI () => "57"
      | JUMPDEST () => "5b"
      | PUSH (n, w) => hex 1 (0x60+n-1) ^ unify_sum (hex n) (hex_large_int n) (w2i $ unInner w)
      | DUP n => hex 1 $ 0x80+n-1
      | SWAP n => hex 1 $ 0x90+n-1
      | LOG n => hex 1 $ 0xa0+n
      | VALUE_AppT _ => ""
      | VALUE_AppI _ => ""
      | VALUE_Pack _ => ""
      | VALUE_PackI _ => ""
      | VALUE_Fold _ => ""
      | VALUE_AscType _ => ""
      | UNPACK _ => ""
      | UNPACKI _ => ""
      | UNFOLD () => ""
      | NAT2INT () => ""
      | INT2NAT () => ""
      | BYTE2INT () => ""
      | ASCTIME _ => ""
      | ASCSPACE _ => ""
      | MARK_PreArray2ArrayPtr () => ""
      | MARK_PreTuple2TuplePtr () => ""
      | InstRestrictPtr _ => ""
      | MACRO_init_free_ptr _ => macro "MACRO_init_free_ptr"
      | MACRO_tuple_malloc _ => macro "MACRO_tuple_malloc"
      | MACRO_tuple_assign () => macro "MACRO_tuple_assign"
      | MACRO_printc () => macro "MACRO_printc"
      | MACRO_array_malloc _ => macro "MACRO_array_malloc"
      | MACRO_array_init_assign _ => macro "MACRO_array_init_assign"
      | MACRO_array_init_len () => macro "MACRO_array_init_len"
      | MACRO_int2byte () => macro "MACRO_int2byte"
      | MACRO_inj _ => macro "MACRO_inj"
      | MACRO_br_sum () => macro "MACRO_br_sum"
      | MACRO_map_ptr () => macro "MACRO_map_ptr"
      | MACRO_vector_ptr () => macro "MACRO_vector_ptr"
      | MACRO_vector_push_back () => macro "MACRO_vector_push_back"
      | InstJUMP () => macro "InstJUMP"
      | InstRETURN () => macro "InstRETURN"
      | InstREVERT () => macro "InstREVERT"
      | Dispatch _ => macro "Dispatch"
  end

val has_Revert_flag = ref false
                          
fun enc_insts out insts =
  let
    fun macro name = raise Impossible $ "Can't assemble instruction " ^ name
  in                                                                        
    case insts of
        ISCons bind =>
        let
          val (i, is) = unBind bind
        in
          (out $ enc i; enc_insts out is)
        end
      | JUMP () => out "56"
      | RETURN () => out "f3"
      | REVERT () => if !has_Revert_flag then out "fd" else enc_insts out (RETURN ()) (* some EVM version doesn't have opcode 0xfd *)
      | ISDummy _ => out ""
      | MACRO_halt _ => macro "MACRO_halt"
  end

fun size_inst inst =
  let
    fun macro name = raise Impossible $ "Can't calculate size of instruction " ^ name
  in                                                                        
    case inst of
        ADD () => 1
      | MUL () => 1
      | SUB () => 1
      | DIV () => 1
      | SDIV () => 1
      | MOD () => 1
      | SMOD () => 1
      | EXP () => 1
      | LT () => 1
      | GT () => 1
      | SLT () => 1
      | SGT () => 1
      | EQ () => 1
      | ISZERO () => 1
      | AND () => 1
      | OR () => 1
      | XOR () => 1
      | NOT () => 1
      | BYTE () => 1
      | SHA3 () => 1
      | ORIGIN () => 1
      | ADDRESS () => 1
      | BALANCE () => 1
      | CALLER () => 1
      | CALLVALUE () => 1
      | CALLDATASIZE () => 1
         | CALLDATALOAD () => 1
         | CALLDATACOPY () => 1
      | CODESIZE () => 1
      | GASPRICE () => 1
      | COINBASE () => 1
      | TIMESTAMP () => 1
      | NUMBER () => 1
      | DIFFICULTY () => 1
      | GASLIMIT () => 1
      | POP () => 1
      | MLOAD () => 1
      | MSTORE () => 1
      | MSTORE8 () => 1
      | SLOAD () => 1
      | SSTORE () => 1
      | JUMPI () => 1
      | JUMPDEST () => 1
      | PUSH (n, w) => n+1
      | DUP n => 1
      | SWAP n => 1
      | LOG n => 1
      | VALUE_AppT _ => 0
      | VALUE_AppI _ => 0
      | VALUE_Pack _ => 0
      | VALUE_PackI _ => 0
      | VALUE_Fold _ => 0
      | VALUE_AscType _ => 0
      | UNPACK _ => 0
      | UNPACKI _ => 0
      | UNFOLD () => 0
      | NAT2INT () => 0
      | INT2NAT () => 0
      | BYTE2INT () => 0
      | ASCTIME _ => 0
      | ASCSPACE _ => 0
      | MARK_PreArray2ArrayPtr () => 0
      | MARK_PreTuple2TuplePtr () => 0
      | InstRestrictPtr _ => 0
      | MACRO_init_free_ptr _ => macro "MACRO_init_free_ptr"
      | MACRO_tuple_malloc _ => macro "MACRO_tuple_malloc"
      | MACRO_tuple_assign () => macro "MACRO_tuple_assign"
      | MACRO_printc () => macro "MACRO_printc"
      | MACRO_array_malloc _ => macro "MACRO_array_malloc"
      | MACRO_array_init_assign _ => macro "MACRO_array_init_assign"
      | MACRO_array_init_len () => macro "MACRO_array_init_len"
      | MACRO_int2byte () => macro "MACRO_int2byte"
      | MACRO_inj _ => macro "MACRO_inj"
      | MACRO_br_sum () => macro "MACRO_br_sum"
      | MACRO_map_ptr () => macro "MACRO_map_ptr"
      | MACRO_vector_ptr () => macro "MACRO_vector_ptr"
      | MACRO_vector_push_back () => macro "MACRO_vector_push_back"
         | Dispatch _ => macro "Dispatch"
         | InstJUMP _ => macro "InstJUMP"
         | InstRETURN _ => macro "InstRETURN"
         | InstREVERT _ => macro "InstREVERT"
  end

fun size_insts insts =
  let
    fun macro name = raise Impossible $ "Can't calculate size of instruction " ^ name
  in                                                                        
    case insts of
        ISCons bind =>
        let
          val (i, is) = unBind bind
        in
          size_inst i + size_insts is
        end
      | JUMP () => 1
      | RETURN () => 1
         | REVERT () => 1
      | ISDummy _ => 0
      | MACRO_halt _ => macro "MACRO_halt"
  end

(***************** the "relabel" visitor  **********************)    

open EVM1Visitor
       
fun relabel_label m l =
  case m @! l of
      SOME v => v
    | NONE => raise Impossible "relabel/relabel_label"
                    
fun relabel_evm1_visitor_vtable cast m =
  let
    val vtable =
        default_evm1_visitor_vtable
          cast
          extend_noop
          extend_noop
          visit_noop
          visit_noop
          visit_noop
          visit_noop
    val vtable = override_visit_label vtable (ignore_this_env $ relabel_label m)
  in
    vtable
  end

fun new_relabel_evm1_visitor params = new_evm1_visitor relabel_evm1_visitor_vtable params
                                                       
fun relabel_insts m b =
  let
    val visitor as (EVM1Visitor vtable) = new_relabel_evm1_visitor m
  in
    #visit_insts vtable visitor () b
  end

fun relabel_hval m code =
  let
    val (binds, (spec, I)) = unBind code
    val I = relabel_insts m I
  in
    Bind (binds, (spec, I))
  end

fun relabel_prog m (H, I) =
  (map (mapPair' (mapFst $ relabel_label m) (relabel_hval m)) H, relabel_insts m I)

fun relabel (H, I) =
  let
    fun foo (((l, name), code), (m, pc)) =
      let
        val m = m @+ (l, pc)
        val (_, (_, I)) = unBind code
        val pc = pc + size_insts I
      in
        (m, pc)
      end
    val (remapping, _) = foldl foo (Rctx.empty, size_insts I) H
  in
    relabel_prog remapping (H, I)
  end

fun enc_prog out (H, I) =
  let
    val () = enc_insts out I
    fun foo (_, code) =
      let
        val (_, (_, I)) = unBind code
      in
        enc_insts out I
      end
  in
    app foo H
  end

fun ass_prog out p =
  enc_prog out $ relabel p
           
fun to_file filename f =
  let
    val out =  TextIO.openOut filename
    fun outfn s = TextIO.output (out, s)
    val () = f outfn
    val () = TextIO.closeOut out
  in
    ()
  end
    
fun to_str f =
  let
    val acc = ref []
    fun outfn s = push_ref acc s
    val () = f outfn
  in
    String.concat $ rev $ !acc
  end

fun ass2file filename p = to_file filename (fn out => ass_prog out p)
fun ass2str p = to_str (fn out => ass_prog out p)
                       
end
