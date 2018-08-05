(***************** pretty printers  **********************)    

structure EVM1PP = struct

open MicroTiMLPP
open EVM1
       
infixr 0 $
         
fun str_word_const c =
  case c of
      WCTT () => "()"
    | WCInt n => str_large_int n
    | WCNat n => "#" ^ str_int n
    | WCBool b => str_bool b
    | WCByte c => Char.toCString c
    | WCiBool b => "#" ^ str_bool b
    | WCLabel l => "l_" ^ str_int l
    | WCState n => "st_" ^ str_int n
                                   
fun str_inst a =
  let
    fun err () = raise Impossible "str_inst()"
  in
    case a of
        ADD () => "ADD"
      | MUL () => "MUL"
      | SUB () => "SUB"
      | DIV () => "DIV"
      | SDIV () => "SDIV"
      | MOD () => "MOD"
      | EXP () => "EXP"
      | LT () => "LT"
      | GT () => "GT"
      | SLT () => "SLT"
      | SGT () => "SGT"
      | EQ () => "EQ"
      | ISZERO () => "ISZERO"
      | AND () => "AND"
      | OR () => "OR"
      | XOR () => "XOR"
      | NOT () => "NOT"
      | BYTE () => "BYTE"
      | ORIGIN () => "ORIGIN"
      | ADDRESS () => "ADDRESS"
      | BALANCE () => "BALANCE"
      | CALLER () => "CALLER"
      | CALLVALUE () => "CALLVALUE"
      | CALLDATASIZE () => "CALLDATASIZE"
         | CALLDATALOAD () => "CALLDATALOAD"
         | CALLDATACOPY () => "CALLDATACOPY"
         | InstJUMP () => "InstJUMP"
         | InstRETURN () => "InstRETURN"
         | InstREVERT () => "InstREVERT"
      | CODESIZE () => "CODESIZE"
      | GASPRICE () => "GASPRICE"
      | COINBASE () => "COINBASE"
      | TIMESTAMP () => "TIMESTAMP"
      | NUMBER () => "NUMBER"
      | DIFFICULTY () => "DIFFICULTY"
      | GASLIMIT () => "GASLIMIT"
      | POP () => "POP"
      | MLOAD () => "MLOAD"
      | MSTORE () => "MSTORE"
      | MSTORE8 () => "MSTORE8"
      | JUMPI () => "JUMPI"
      | JUMPDEST () => "JUMPDEST"
      | UNFOLD () => "UNFOLD"
      | NAT2INT () => "NAT2INT"
      | INT2NAT () => "INT2NAT"
      | BYTE2INT () => "BYTE2INT"
      (* | PRINTC () => "PRINTC" *)
      | MARK_PreArray2ArrayPtr () => "MARK_PreArray2ArrayPtr"
      | MARK_PreTuple2TuplePtr () => "MARK_PreTuple2TuplePtr"
      | InstRestrictPtr n => "InstRestrictPtr " ^ str_int n
      | DUP n => "DUP" ^ str_int n
      | SWAP n => "SWAP" ^ str_int n
      | LOG n => "LOG" ^ str_int n
      | UNPACK name => "UNPACK " ^ binder2str name
      | UNPACKI name => "UNPACKI " ^ binder2str name
      | MACRO_init_free_ptr n => "MACRO_init_free_ptr " ^ str_int n
      | MACRO_tuple_assign () => "MACRO_tuple_assign"
      | MACRO_printc () => "MACRO_printc"
      | MACRO_array_init_assign w => "MACRO_array_init_assign " ^ str_int w
      | MACRO_array_init_len () => "MACRO_array_init_len"
      | MACRO_int2byte () => "MACRO_int2byte"
      | MACRO_br_sum () => "MACRO_br_sum"
      | PUSH (n, w) => err ()
      | VALUE_AppT t => err ()
      | VALUE_AppI i => err ()
      | VALUE_Pack (t1, t2) => err ()
      | VALUE_PackI (t, i) => err ()
      | VALUE_Fold t => err ()
      | VALUE_AscType t => err ()
      | ASCTIME i => err ()
      | ASCSPACE i => err ()
      | MACRO_tuple_malloc ts => err ()
      | MACRO_array_malloc t => err ()
      | Dispatch _ => err ()
      | MACRO_inj t => err ()
      | SHA3 () => "SHA3"
      | SLOAD () => "SLOAD"
      | SSTORE () => "SSTORE"
      | MACRO_map_ptr () => "MACRO_map_ptr"
      | MACRO_vector_ptr () => "MACRO_vector_ptr"
      | MACRO_vector_push_back () => "MACRO_vector_push_back"
  end

fun pp_w pp_t s w =
  let
    val pp_t = pp_t s
    fun space () = PP.space s 1
    fun str v = PP.string s v
    fun comma () = (str ","; space ())
    fun open_hbox () = PP.openHBox s
    fun open_vbox () = PP.openVBox s (PP.Rel 2)
    fun open_vbox_noindent () = PP.openVBox s (PP.Rel 0)
    fun close_box () = PP.closeBox s
  in
    case w of
        WConst c =>
        (* ( *)
        (*   open_hbox (); *)
        (*   str "WConst"; *)
        (*   space (); *)
        (*   str $ str_word_const c; *)
        (*   close_box () *)
        (* ) *)
        str $ str_word_const c
      | WUninit t =>
        (
          open_hbox ();
          str "WUninit";
          space ();
          str "(";
          pp_t t;
          str ")";
          close_box ()
        )
      | WBuiltin (name, t) =>
        (
          open_hbox ();
          str "WBuiltin";
          space ();
          str "(";
          str name;
          comma ();
          pp_t t;
          str ")";
          close_box ()
        )
      | WNever t =>
        (
          open_hbox ();
          str "WNever";
          space ();
          str "(";
          pp_t t;
          str ")";
          close_box ()
        )
  end
    
fun str_reg r = "r" ^ str_int r
                              
fun pp_inst (params as (str_i, pp_t, pp_w)) s inst =
  let
    val pp_inst = pp_inst params s
    val str_i = str_i o unInner
    val pp_t = pp_t s o unInner
    val pp_w = pp_w s o unInner
    fun space () = PP.space s 1
    fun str v = PP.string s v
    fun comma () = (str ","; space ())
    fun open_hbox () = PP.openHBox s
    fun open_vbox () = PP.openVBox s (PP.Rel 2)
    fun open_vbox_noindent () = PP.openVBox s (PP.Rel 0)
    fun close_box () = PP.closeBox s
    fun pp_list f ls =
      case ls of
          [] => ()
        | [x] => f x
        | x :: xs =>
          (
            f x;
            comma ();
            pp_list f xs
          )
    fun pp_bracket f =
      (
        str "[";
        f ();
        str "]"
      )
    fun pp_list_bracket f ls = pp_bracket $ (fn () => pp_list f ls)
  in
    case inst of
        PUSH (n, w) =>
        (
          open_hbox ();
          str $ "PUSH" ^ str_int n;
          space ();
          (* str "("; *)
          pp_w w;
          (* str ")"; *)
          close_box ()
        )
      | VALUE_AppT t =>
        (
          open_hbox ();
          str $ "VALUE_AppT";
          space ();
          str "(";
          pp_t t;
          str ")";
          close_box ()
        )
      | VALUE_AppI i =>
        (
          open_hbox ();
          str $ "VALUE_AppI";
          space ();
          str "(";
          str $ str_i i;
          str ")";
          close_box ()
        )
      | VALUE_Pack (t1, t2) =>
        (
          open_hbox ();
          str $ "VALUE_Pack";
          space ();
          str "(";
          pp_t t1;
          comma ();
          pp_t t2;
          str ")";
          close_box ()
        )
      | VALUE_PackI (t, i) =>
        (
          open_hbox ();
          str $ "VALUE_PackI";
          space ();
          str "(";
          pp_t t;
          comma ();
          str $ str_i i;
          str ")";
          close_box ()
        )
      | VALUE_Fold t =>
        (
          open_hbox ();
          str $ "VALUE_Fold";
          space ();
          str "(";
          pp_t t;
          str ")";
          close_box ()
        )
      | VALUE_AscType t =>
        (
          open_hbox ();
          str $ "VALUE_AscType";
          space ();
          str "(";
          pp_t t;
          str ")";
          close_box ()
        )
      (* | PACK_SUM (inj, t) => *)
      (*   ( *)
      (*     open_hbox (); *)
      (*     str $ "PACK_SUM"; *)
      (*     space (); *)
      (*     str "("; *)
      (*     str $ str_inj inj; *)
      (*     comma (); *)
      (*     pp_t t; *)
      (*     str ")"; *)
      (*     close_box () *)
      (*   ) *)
      | ASCTIME i =>
        (
          open_hbox ();
          str $ "ASCTIME";
          space ();
          str "(";
          str $ str_i i;
          str ")";
          close_box ()
        )
      | ASCSPACE i =>
        (
          open_hbox ();
          str $ "ASCSPACE";
          space ();
          str "(";
          str $ str_i i;
          str ")";
          close_box ()
        )
      | MACRO_tuple_malloc ts =>
        (
          open_hbox ();
          str $ "MACRO_tuple_malloc";
          space ();
          str "(";
          app (fn t => (pp_t $ Inner t; comma ())) $ unInner ts;
          str ")";
          close_box ()
        )
      | MACRO_array_malloc (w, t, b) =>
        (
          open_hbox ();
          str $ "MACRO_array_malloc";
          space ();
          str "(";
          str $ str_int w;
          comma ();
          pp_t t;
          comma ();
          str $ str_bool b;
          str ")";
          close_box ()
        )
      | MACRO_inj t =>
        (
          open_hbox ();
          str $ "MACRO_inj";
          space ();
          str "(";
          pp_t t;
          comma ();
          str ")";
          close_box ()
        )
      | Dispatch ls =>
        (
          open_hbox ();
          str "Dispatch";
          space ();
          str "(";
          pp_list_bracket (fn (sg, t1, t2, n) =>
                              (str $ str_int sg;
                               comma ();
                               pp_t t1;
                               comma ();
                               pp_t t2;
                               comma ();
                               str $ str_int n
                          )) ls;
          str ")";
          close_box ()
        )
      | _ => str $ str_inst inst
  end

fun pp_insts (params as (pp_t, pp_inst)) s insts =
  let
    val pp_insts = pp_insts params s
    val pp_t = pp_t s
    val pp_inst = pp_inst s
    fun space () = PP.space s 1
    fun str v = PP.string s v
    fun comma () = (str ","; space ())
    fun open_hbox () = PP.openHBox s
    fun open_vbox () = PP.openVBox s (PP.Rel 2)
    fun open_vbox_noindent () = PP.openVBox s (PP.Rel 0)
    fun close_box () = PP.closeBox s
  in
    case insts of
        ISCons bind =>
        let
          val (i, is) = unBind bind
        in
          (
	    open_vbox_noindent ();
            pp_inst i;
            space ();
            pp_insts is;
            close_box ()
          )
        end
      | JUMP () => str "JUMP"
      | RETURN () => str "RETURN"
         | REVERT () => str "REVERT"
      | ISDummy s => str s
      | MACRO_halt (b, t) =>
        (
          open_hbox ();
          str $ "MACRO_halt";
          space ();
          str "(";
          str $ str_bool b;
          comma ();
          pp_t t;
          str ")";
          close_box ()
        )
  end

fun pp_hval (params as (str_i, str_s, str_b, pp_t, pp_insts)) s bind =
  let
    val pp_t = pp_t s
    val pp_insts = pp_insts s
    val str_k = str_k str_b
    fun space () = PP.space s 1
    fun str v = PP.string s v
    fun comma () = (str ","; space ())
    fun open_hbox () = PP.openHBox s
    fun open_vbox () = PP.openVBox s (PP.Rel 2)
    fun open_vbox_noindent () = PP.openVBox s (PP.Rel 0)
    fun close_box () = PP.closeBox s
    val (itbinds, ((st, rctx, ts, (j, i)), insts)) = unBind bind
    val itbinds = unTeles itbinds
    val itbinds = map (map_inl_inr (mapPair' binder2str unOuter) (mapPair' binder2str unOuter)) itbinds
  in
    open_vbox ();
    open_hbox ();
    str "Code";
    space ();
    str "(";
    app (app_inl_inr
           (fn (name, s) =>
               (str $ name;
                str ":"; space ();
                str $ str_s s;
                comma ()
           ))
           (fn (name, k) =>
               (str $ name;
                str "::"; space ();
                str $ str_k k;
                comma ()
           ))
        ) itbinds;
    close_box ();
    space ();
    open_vbox_noindent ();
    str $ "Pre: " ^ str_i st;
    comma ();
    str "Regs: {";
    Rctx.appi (fn (r, t) =>
                  (str $ str_reg r;
                   str ": "; pp_t t;
                   comma ()
              )) rctx;
    str "}";
    comma ();
    str "Stack: [";
    (* space (); *)
    app (fn t =>
            (pp_t t;
             comma ()
        )) ts;
    str "]";
    comma ();
    str $ "Time: " ^ str_i j;
    comma ();
    str $ "Space: " ^ str_i i;
    comma ();
    str "Body: ";
    space ();
    pp_insts insts;
    str ")";
    close_box ();
    close_box ()
  end
    
fun pp_prog (pp_hval, pp_insts) s (heap, insts) =
  let
    val pp_hval = pp_hval s
    val pp_insts = pp_insts s
    fun space () = PP.space s 1
    fun str v = PP.string s v
    fun comma () = (str ","; space ())
    fun open_hbox () = PP.openHBox s
    fun open_vbox () = PP.openVBox s (PP.Rel 2)
    fun open_vbox_noindent () = PP.openVBox s (PP.Rel 0)
    fun close_box () = PP.closeBox s
  in
    open_vbox_noindent ();
    pp_insts insts;
    space ();
    app (fn ((l, name), h) =>
            (str $ sprintf "$ <$>" [str_int l, name];
             str ":"; space ();
             pp_hval h;
             space ()
        )) heap;
    close_box ()
  end

open WithPP

fun pp_inst_to_fn (str_i, pp_t) s b =
  let
    val pp_w = pp_w pp_t
  in
    withPP ("", 80, s) (fn s => pp_inst (str_i, pp_t, pp_w) s b)
  end
fun pp_inst_fn params = pp_inst_to_fn params TextIO.stdOut
fun pp_inst_to_string_fn params b =
  pp_to_string "pp_inst_to_string.tmp" (fn os => pp_inst_to_fn params os b)
               
fun pp_insts_to_fn (str_i, pp_t) s b =
  let
    val pp_w = pp_w pp_t
  in
    withPP ("", 80, s) (fn s => pp_insts (pp_t, pp_inst (str_i, pp_t, pp_w)) s b)
  end
fun pp_insts_fn params = pp_insts_to_fn params TextIO.stdOut
fun pp_insts_to_string_fn params b =
  pp_to_string "pp_insts_to_string.tmp" (fn os => pp_insts_to_fn params os b)
               
fun pp_prog_to_fn (str_i, str_s, str_bs, pp_t) s b =
  let
    val pp_w = pp_w pp_t
    val pp_insts = pp_insts (pp_t, pp_inst (str_i, pp_t, pp_w))
  in
    withPP ("", 80, s) (fn s => pp_prog (pp_hval (str_i, str_s, str_bs, pp_t, pp_insts), pp_insts) s b)
  end
fun pp_prog_fn params = pp_prog_to_fn params TextIO.stdOut
fun pp_prog_to_string_fn params b =
  pp_to_string "pp_prog_to_string.tmp" (fn os => pp_prog_to_fn params os b)
               
end
