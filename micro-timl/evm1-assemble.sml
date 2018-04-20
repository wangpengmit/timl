structure EVM1Assemble = struct

open EVM1

infixr 0 $

infix  6 @+
infix  9 @!
         
fun wc2i c =
  case c of
      WCTT => 0
    | WCNat n => n
    | WCInt n => n
    | WCBool b => b2i b
    | WCByte c => Char.ord c
    | WCiBool b => b2i b
    | WCLabel n => n
                     
fun w2i w =
  case w of
      WConst c => wc2i c
    | _ => 0

fun hex nBytes i =
  let
    val n = nBytes * 2
    val s = Int.fmt StringCvt.HEX i
    val len = String.size s
    val s = if len > n then String.extract (s, len-n, NONE)
            else s
    val s = StringCvt.padLeft #"0" n s
  in
    s
  end

fun macro name = raise Impossible $ "Can't assemble instruction " ^ name
                     
fun enc inst =
  case inst of
      ADD => "01"
    | MUL => "02"
    | SUB => "03"
    | DIV => "04"
    | SDIV => "05"
    | MOD => "06"
    | LT => "10"
    | GT => "11"
    | SLT => "12"
    | SGT => "13"
    | EQ => "14"
    | ISZERO => "15"
    | AND => "16"
    | OR => "17"
    | BYTE => "1a"
    | POP => "50"
    | MLOAD => "51"
    | MSTORE => "52"
    | MSTORE8 => "53"
    | JUMPI => "57"
    | JUMPDEST => "5b"
    | PUSH (n, w) => hex 1 (0x60+n-1) ^ hex n (w2i $ unInner w)
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
    | UNFOLD => ""
    | NAT2INT => ""
    | INT2NAT => ""
    | BYTE2INT => ""
    | ASCTIME _ => ""
    | MARK_PreArray2ArrayPtr => ""
    | MARK_PreTuple2TuplePtr => ""
    | MACRO_init_free_ptr _ => macro "MACRO_init_free_ptr"
    | MACRO_malloc_tuple _ => macro "MACRO_malloc_tuple"

fun enc_insts out insts =
  case insts of
      ISCons bind =>
      let
        val (i, is) = unBind bind
      in
        (out $ enc i; enc_insts out is)
      end
    | JUMP => out "56"
    | RETURN => out "f3"
    | ISDummy _ => out ""
    | MACRO_halt _ => macro "MACRO_halt"

fun size_inst inst =
  case inst of
      ADD => 1
    | MUL => 1
    | SUB => 1
    | DIV => 1
    | SDIV => 1
    | MOD => 1
    | LT => 1
    | GT => 1
    | SLT => 1
    | SGT => 1
    | EQ => 1
    | ISZERO => 1
    | AND => 1
    | OR => 1
    | BYTE => 1
    | POP => 1
    | MLOAD => 1
    | MSTORE => 1
    | MSTORE8 => 1
    | JUMPI => 1
    | JUMPDEST => 1
    | PUSH (n, w) => n+1
    | DUP n => 1
    | SWAP n => 1
    | LOG n => 1
    | _ => 0

fun size_insts insts =
  case insts of
      ISCons bind =>
      let
        val (i, is) = unBind bind
      in
        size_inst i + size_insts is
      end
    | JUMP => 1
    | RETURN => 1
    | ISDummy _ => 0
    | _ => 0

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
