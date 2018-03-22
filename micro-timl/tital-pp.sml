(***************** pretty printers  **********************)    

structure TiTALPP = struct

open MicroTiMLExPP
open TiTAL
       
infixr 0 $
         
fun str_word_const c =
  case c of
      WCTT => "()"
    | WCInt n => str_int n
    | WCNat n => sprintf "#$" [str_int n]
    | WCBool b => str_bool b
                                
fun str_inst_un_op opr =
  case opr of
      IUMov => "mov"
    | IUBrSum => "br_sum"
    | IUBrBool => "br_bool"
    | IUUnfold => "unfold"
    | IUPrim opr => str_prim_expr_un_op opr
    | IUPrint => "print"
    | IUArrayLen => "array_len"
    | IUNat2Int => "nat2int"

fun str_inst_bin_op opr =
  case opr of
      IBPrim opr => str_prim_expr_bin_op opr
    | IBNat opr => str_nat_expr_bin_op opr
    | IBNatCmp opr => str_nat_cmp opr
    | IBNew => "new"
    | IBRead => "read"
    | IBWrite => "write"

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
        WLabel l =>
        (
          open_hbox ();
          str "WLabel";
          space ();
          str $ str_int l;
          close_box ()
        )
      | WConst c =>
        (
          open_hbox ();
          str "WConst";
          space ();
          str $ str_word_const c;
          close_box ()
        )
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
                              
fun pp_v (params as (str_i, pp_t, pp_w)) s v =
  let
    val pp_v = pp_v params s
    val pp_t = pp_t s
    val pp_w = pp_w s
    fun space () = PP.space s 1
    fun str v = PP.string s v
    fun comma () = (str ","; space ())
    fun open_hbox () = PP.openHBox s
    fun open_vbox () = PP.openVBox s (PP.Rel 2)
    fun open_vbox_noindent () = PP.openVBox s (PP.Rel 0)
    fun close_box () = PP.closeBox s
  in
    case v of
        VReg r =>
        str $ str_reg r
      | VWord w =>
        pp_w w
      | VAppT (v, t) =>
        (
          open_hbox ();
          str "VAppT";
          space ();
          str "(";
          pp_v v;
          comma ();
          pp_t t;
          str ")";
          close_box ()
        )
      | VAppI (v, i) =>
        (
          open_hbox ();
          str "VAppI";
          space ();
          str "(";
          pp_v v;
          comma ();
          str $ str_i i;
          str ")";
          close_box ()
        )
      | VPack (t_all, t, v) =>
        (
          open_hbox ();
          str "VPack";
          space ();
          str "(";
          pp_t t;
          comma ();
          pp_v v;
          comma ();
          pp_t t_all;
          str ")";
          close_box ()
        )
      | VPackI (t, i, v) =>
        (
          open_hbox ();
          str "VPackI";
          space ();
          str "(";
          str $ str_i i;
          comma ();
          pp_v v;
          comma ();
          pp_t t;
          str ")";
          close_box ()
        )
      | VFold (t, v) =>
        (
          open_hbox ();
          str "VAppT";
          space ();
          str "(";
          pp_v v;
          comma ();
          pp_t t;
          str ")";
          close_box ()
        )
      | VAscType (v, t) =>
        (
          open_hbox ();
          str "VAscType";
          space ();
          str "(";
          pp_v v;
          comma ();
          pp_t t;
          str ")";
          close_box ()
        )
  end

fun pp_inst (params as (str_i, pp_t, pp_v)) s inst =
  let
    val pp_inst = pp_inst params s
    val pp_t = pp_t s
    val pp_v_core = pp_v s
    val pp_v = pp_v_core o unInner
    val pp_outer_v = pp_v_core o unOuter
    fun space () = PP.space s 1
    fun str v = PP.string s v
    fun comma () = (str ","; space ())
    fun open_hbox () = PP.openHBox s
    fun open_vbox () = PP.openVBox s (PP.Rel 2)
    fun open_vbox_noindent () = PP.openVBox s (PP.Rel 0)
    fun close_box () = PP.closeBox s
  in
    case inst of
        IUnOp (opr, r, v) =>
        (
          open_hbox ();
          str $ str_inst_un_op opr;
          space ();
          str "(";
          str $ str_reg r;
          comma ();
          pp_v v;
          str ")";
          close_box ()
        )
      | IBinOp (opr, r, r', v) =>
        (
          open_hbox ();
          str $ str_inst_bin_op opr;
          space ();
          str "(";
          str $ str_reg r;
          comma ();
          str $ str_reg r';
          comma ();
          pp_v v;
          str ")";
          close_box ()
        )
      | IMallocPair (r, (v, v')) =>
        (
          open_hbox ();
          str "malloc_pair";
          space ();
          str "(";
          str $ str_reg r;
          comma ();
          pp_v v;
          comma ();
          pp_v v';
          str ")";
          close_box ()
        )
      | ILd (r, (r', proj)) =>
        (
          open_hbox ();
          str "ld";
          space ();
          str "(";
          str $ str_reg r;
          comma ();
          str $ str_reg r';
          comma ();
          str $ str_proj proj;
          str ")";
          close_box ()
        )
      | ISt ((r, proj), r') =>
        (
          open_hbox ();
          str "st";
          space ();
          str "(";
          str $ str_reg r;
          comma ();
          str $ str_proj proj;
          comma ();
          str $ str_reg r';
          str ")";
          close_box ()
        )
      | IUnpack (name, r, v) =>
        (
          open_hbox ();
          str "unpack";
          space ();
          str "(";
          str $ binder2str name;
          comma ();
          str $ str_reg r;
          comma ();
          pp_outer_v v;
          str ")";
          close_box ()
        )
      | IUnpackI (name, r, v) =>
        (
          open_hbox ();
          str "unpackI";
          space ();
          str "(";
          str $ binder2str name;
          comma ();
          str $ str_reg r;
          comma ();
          pp_outer_v v;
          str ")";
          close_box ()
        )
      | IInj (r, inj, v, t) =>
        (
          open_hbox ();
          str "inj";
          space ();
          str "(";
          str $ str_reg r;
          comma ();
          str $ str_inj inj;
          comma ();
          pp_v v;
          comma ();
          pp_t $ unInner t;
          str ")";
          close_box ()
        )
      | IString (r, s) =>
        (
          open_hbox ();
          str "string";
          space ();
          str "(";
          str $ str_reg r;
          comma ();
          str s;
          str ")";
          close_box ()
        )
      | IAscTime i =>
        (
          open_hbox ();
          str "asc_time";
          space ();
          str "(";
          str $ str_i $ unInner i;
          str ")";
          close_box ()
        )
  end

fun pp_insts (params as (str_i, pp_t, pp_v, pp_inst)) s insts =
  let
    val pp_insts = pp_insts params s
    val pp_t = pp_t s
    val pp_v = pp_v s
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
      | ISJmp v =>
        (
          open_hbox ();
          str "jmp";
          space ();
          str "(";
          pp_v v;
          str ")";
          close_box ()
        )
      | ISHalt t =>
        (
          open_hbox ();
          str "halt";
          space ();
          str "(";
          pp_t t;
          str ")";
          close_box ()
        )
      | ISDummy s =>
        str s
  end

fun pp_hval (params as (str_i, str_s, str_k, pp_t, pp_insts)) s bind =
  let
    val pp_t = pp_t s
    val pp_insts = pp_insts s
    fun space () = PP.space s 1
    fun str v = PP.string s v
    fun comma () = (str ","; space ())
    fun open_hbox () = PP.openHBox s
    fun open_vbox () = PP.openVBox s (PP.Rel 2)
    fun open_vbox_noindent () = PP.openVBox s (PP.Rel 0)
    fun close_box () = PP.closeBox s
    val (itbinds, ((rctx, i), insts)) = unBind bind
    val itbinds = unTeles itbinds
    val itbinds = map (map_inl_inr (mapPair' binder2str unOuter) (mapFst binder2str)) itbinds
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
    open_hbox ();
    str "{";
    Rctx.appi (fn (r, t) =>
              (str $ str_reg r;
               str ":"; space ();
               pp_t t;
               comma ()
              )) rctx;
    str "}";
    close_box ();
    comma ();
    str $ str_i i;
    comma ();
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
    app (fn ((l, name), h) =>
            (str $ sprintf "$ <$>" [str_int l, name];
             str ":"; space ();
             pp_hval h;
             space ()
        )) heap;
    pp_insts insts;
    close_box ()
  end

open WithPP

fun pp_insts_to_fn (str_i, pp_t) s b =
  let
    val pp_v = pp_v (str_i, pp_t, pp_w pp_t)
  in
    withPP ("", 80, s) (fn s => pp_insts (str_i, pp_t, pp_v, pp_inst (str_i, pp_t, pp_v)) s b)
  end
fun pp_insts_fn params = pp_insts_to_fn params TextIO.stdOut
fun pp_insts_to_string_fn params b =
  pp_to_string "pp_insts_to_string.tmp" (fn os => pp_insts_to_fn params os b)
    
fun pp_prog_to_fn (str_i, str_s, str_k, pp_t) s b =
  let
    val pp_v = pp_v (str_i, pp_t, pp_w pp_t)
    val pp_insts = pp_insts (str_i, pp_t, pp_v, pp_inst (str_i, pp_t, pp_v))
  in
    withPP ("", 80, s) (fn s => pp_prog (pp_hval (str_i, str_s, str_k, pp_t, pp_insts), pp_insts) s b)
  end
fun pp_prog_fn params = pp_prog_to_fn params TextIO.stdOut
fun pp_prog_to_string_fn params b =
  pp_to_string "pp_prog_to_string.tmp" (fn os => pp_prog_to_fn params os b)
    
end
