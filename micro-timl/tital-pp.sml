(***************** pretty printers  **********************)    

structure TiTALPP = struct

open MicroTiMLExPP
open TiTAL
       
infixr 0 $
         
fun str_inst_un_op opr =
  case opr of
      IUMov => "mov"
    | IUBr => "br"
    | IUUnfold => "unfold"

fun str_inst_bin_op opr =
  case opr of
      IBPrim opr => str_prim_expr_bin_op opr
    | IBNatAdd => "nat_add"
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
          str $ str_expr_const c;
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
      | WBuiltin t =>
        (
          open_hbox ();
          str "WBuiltin";
          space ();
          str "(";
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
          str "IUnOp";
          space ();
          str "(";
          str $ str_inst_un_op opr;
          comma ();
          str $ str_reg r;
          comma ();
          pp_v v;
          str ")";
          close_box ()
        )
      | IBinOp (opr, r, r', v) =>
        (
          open_hbox ();
          str "IBinOp";
          space ();
          str "(";
          str $ str_inst_bin_op opr;
          comma ();
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
          str "IMallocPair";
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
          str "ILd";
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
          str "ISt";
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
          str "IUnpack";
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
          str "IUnpackI";
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
      | IInj (r, inj, v) =>
        (
          open_hbox ();
          str "ISt";
          space ();
          str "(";
          str $ str_reg r;
          comma ();
          str $ str_inj inj;
          comma ();
          pp_v v;
          str ")";
          close_box ()
        )
      | IAscTime i =>
        (
          open_hbox ();
          str "IAscTime";
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
          str "ISJmp";
          space ();
          str "(";
          pp_v v;
          str ")";
          close_box ()
        )
      | ISHalt t =>
        (
          open_hbox ();
          str "ISHalt";
          space ();
          str "(";
          pp_t t;
          str ")";
          close_box ()
        )
      | ISDummy s =>
        str s
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
    
end
