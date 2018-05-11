(***************** pretty printers  **********************)    

structure MicroTiMLPP = struct

open MicroTiML
       
infixr 0 $
         
fun get_bind b = mapFst binder2str $ unBind b
fun get_bind_anno b =
  let
    val ((name, anno), t) = unBindAnno b
  in
    (Name2str name, anno, t)
  end

fun str_ty_const c =
  case c of
      TCUnit => "unit"
    | TCEmpty => "empty"
    | TCTiML t => BaseTypes.str_bt t
      
fun str_ty_bin_op opr =
  case opr of
      TBProd => "prod"
    | TBSum => "sum"

(* depth=NONE means no depth limit *)
fun pp_t (params as (str_var, str_b, str_i, str_s, str_k)) s depth t =
  let
    val (reached_depth_limit, depth) =
        case depth of
            NONE => (false, NONE)
          | SOME n => if n <= 0 then
                        (true, NONE)
                      else
                        (false, SOME (n-1))
    val pp_t = pp_t params s depth
    fun space () = PP.space s 1
    fun add_space a = (space (); a)
    fun str v = PP.string s v
    fun comma () = (str ","; space ())
    fun open_hbox () = PP.openHBox s
    (* fun open_vbox () = PP.openVBox s (PP.Abs 2) *)
    fun open_vbox () = PP.openVBox s (PP.Rel 2)
    fun close_box () = PP.closeBox s
    fun pp_pair (fa, fb) (a, b) =
      (
        open_hbox ();
        str "(";
        fa a;
        comma ();
        fb b;
        str ")";
        close_box ()
      )
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
  in
    if reached_depth_limit then str "..."
    else
    case t of
        TVar (x, ks) =>
        (* ( *)
        (*   open_hbox (); *)
        (*   str "TVar"; *)
        (*   space (); *)
          str $ str_var x (* ^ sprintf "[$]" [str_int $ length ks] *)(* ; *)
        (*   close_box () *)
        (* ) *)
      | TConst TCUnit =>
        str "TUnit"
      | TConst c =>
        (
          open_hbox ();
          str "TConst";
          space ();
          str $ str_ty_const c;
          close_box ()
        )
      | TBinOp (TBProd, t1, t2) =>
        let
          val ts = collect_TProd_left t
          val (t, ts) = assert_cons ts
          val pp_t = fn t => (str "("; pp_t t; str ")")
        in
          open_hbox ();
          pp_t t;
          app (fn t => (space (); str "*"; space (); pp_t t)) ts;
          close_box ()
        end
      | TBinOp (opr, t1, t2) =>
        (
          open_hbox ();
          str "TBinOp";
          space ();
          str "(";
          str $ str_ty_bin_op opr;
          comma ();
          pp_t t1;
          comma ();
          pp_t t2;
          str ")";
          close_box ()
        )
      | TArrow ((i1, t1), i, (i2, t2)) =>
        (
          open_hbox ();
          str "TArrow";
          space ();
          str "(";
          str $ str_i i1;
          comma ();
          pp_t t1;
          comma ();
          str $ str_i i;
          comma ();
          str $ str_i i2;
          comma ();
          pp_t t2;
          str ")";
          close_box ()
        )
      | TAbsI bind =>
        let
          val (name, b, t) = get_bind_anno bind
        in
          open_hbox ();
          str "TAbsI";
          space ();
          str "(";
          str name;
          comma ();
          str $ str_b b;
          comma ();
          pp_t t;
          str ")";
          close_box ()
        end
      | TAppI (t, i) =>
        (
          open_hbox ();
          str "TAppI";
          space ();
          str "(";
          pp_t t;
          comma ();
          str $ str_i i;
          str ")";
          close_box ()
        )
      | TQuan (q, bind) =>
        let
          val (name, k, t) = get_bind_anno bind
        in
          open_hbox ();
          str "TQuan";
          space ();
          str "(";
          str $ str_quan q;
          comma ();
          str name;
          comma ();
          str $ str_k k;
          comma ();
          pp_t t;
          str ")";
          close_box ()
        end
      | TQuanI (q, bind) =>
        let
          val (name, s, t) = get_bind_anno bind
        in
          open_hbox ();
          str "TQuanI";
          space ();
          str "(";
          str $ str_quan q;
          comma ();
          str name;
          comma ();
          str $ str_s s;
          comma ();
          pp_t t;
          str ")";
          close_box ()
        end
      | TRec bind =>
        let
          val (name, k, t) = get_bind_anno bind
        in
          open_hbox ();
          str "TRec";
          space ();
          str "(";
          str name;
          comma ();
          str $ str_k k;
          comma ();
          pp_t t;
          str ")";
          close_box ()
        end
      | TNat i =>
        (
          open_hbox ();
          str "TNat";
          space ();
          str "(";
          str $ str_i i;
          str ")";
          close_box ()
        )
      | TiBool i =>
        (
          open_hbox ();
          str "TiBool";
          space ();
          str "(";
          str $ str_i i;
          str ")";
          close_box ()
        )
      | TArr (t, i) =>
        (
          open_hbox ();
          str "TArr";
          space ();
          str "(";
          pp_t t;
          comma ();
          str $ str_i i;
          str ")";
          close_box ()
        )
      | TPreArray (t, i1, i2, (b, b2)) =>
        (
          open_hbox ();
          str "TPreArray";
          space ();
          str "(";
          pp_t t;
          comma ();
          str $ str_i i1;
          comma ();
          str $ str_i i2;
          comma ();
          str $ str_bool b;
          comma ();
          str $ str_bool b2;
          str ")";
          close_box ()
        )
      | TArrayPtr (t, i1, i2) =>
        (
          open_hbox ();
          str "TArrayPtr";
          space ();
          str "(";
          pp_t t;
          comma ();
          str $ str_i i1;
          comma ();
          str $ str_i i2;
          str ")";
          close_box ()
        )
      | TTuplePtr (ts, i, b) =>
        (
          open_hbox ();
          str "TTuplePtr";
          space ();
          str "(";
          app (fn t => (pp_t t; comma ())) ts;
          str $ str_i i;
          comma ();
          str $ str_bool b;
          str ")";
          close_box ()
        )
      | TPreTuple (ts, i, i2) =>
        (
          open_hbox ();
          str "TPreTuple";
          space ();
          str "(";
          app (fn t => (pp_t t; comma ())) ts;
          str $ str_i i;
          comma ();
          str $ str_i i2;
          str ")";
          close_box ()
        )
      | TAbsT bind =>
        let
          val (name, k, t) = get_bind_anno bind
        in
          open_hbox ();
          str "TAbsT";
          space ();
          str "(";
          str name;
          comma ();
          str $ str_k k;
          comma ();
          pp_t t;
          str ")";
          close_box ()
        end
      | TAppT (t, t') =>
        (
          open_hbox ();
          str "TAppT";
          space ();
          str "(";
          pp_t t;
          comma ();
          pp_t t';
          str ")";
          close_box ()
        )
      | TProdEx ((t1, b1), (t2, b2)) =>
        (
          open_hbox ();
          str "TProdEx";
          space ();
          str "(";
          str $ str_bool b1;
          comma ();
          pp_t t1;
          comma ();
          str $ str_bool b2;
          comma ();
          pp_t t2;
          str ")";
          close_box ()
        )
      | TArrowTAL (ts, i) =>
        (
          open_hbox ();
          str "TArrowTAL";
          space ();
          str "(";
          Rctx.appi
            (fn (r, t) =>
                (str ("r" ^ str_int r);
                 str ":"; space ();
                 pp_t t;
                 comma ())) ts;
          str $ str_i i;
          str ")";
          close_box ()
        )
      | TArrowEVM (i1, rctx, ts, i2) =>
        (
          open_hbox ();
          str "TArrowEVM";
          space ();
          str "(";
          str $ str_i i1;
          comma ();
          str "{";
          Rctx.appi
            (fn (r, t) =>
                (str ("r" ^ str_int r);
                 str ":"; space ();
                 pp_t t;
                 comma ())) rctx;
          str "}";
          comma ();
          str "[";
          app (fn t => (pp_t t; comma ())) ts;
          str "]";
          comma ();
          str $ str_i i2;
          str ")";
          close_box ()
        )
      | TMap t =>
        (
          open_hbox ();
          str "TMap";
          space ();
          str "(";
          pp_t t;
          str ")";
          close_box ()
        )
      | TState x => str $ "TState " ^ x
      | TVectorPtr (x, i) =>
        (
          open_hbox ();
          str "TVectorPtr";
          space ();
          str "(";
          str x;
          comma ();
          str $ str_i i;
          str ")";
          close_box ()
        )
  end

open WithPP
       
fun pp_t_fn params d t = withPP ("", 80, TextIO.stdOut) (fn s => pp_t params s d t)
val pp_t_to_fn = pp_t
fun pp_t_to_os_fn params os d t = withPP ("", 80, os) (fn s => pp_t params s d t)
fun pp_t_to_string_fn params d t =
  pp_to_string "pp_t_to_string.tmp" (fn os => pp_t_to_os_fn params os d t)
                              
fun str_inj opr =
  case opr of
      InjInl => "inl"
    | InjInr => "inr"

fun str_expr_un_op str_t opr =
  case opr of
     EUInj (opr, t) => sprintf "($, $)" [str_inj opr, str_t t]
    | EUFold t => sprintf "(fold $)" [str_t t]
    | EUUnfold => "unfold"
    | EUTiML opr => Operators.str_expr_un_op opr

fun get_bind b = mapFst binder2str $ unBind b
fun get_bind_anno b =
  let
    val ((name, anno), t) = unBindAnno b
  in
    (Name2str name, anno, t)
  end
                 
fun str_inj opr =
  case opr of
      InjInl => "inl"
    | InjInr => "inr"

fun str_expr_un_op str_t opr =
  case opr of
     EUInj (opr, t) => sprintf "($, $)" [str_inj opr, str_t t]
    | EUFold t => sprintf "(fold $)" [str_t t]
    | EUUnfold => "unfold"
    | EUTiML opr => Operators.str_expr_un_op opr

fun str_expr_tri_op opr =
  case opr of
      ETWrite () => "EWrite"
    | ETIte () => "EIte"
    | ETVectorSet () => "EVectorSet"
                                             
fun str_e str_var str_i e =
  let
    val str_e = str_e str_var str_i
  in
    case e of
        EVar x => sprintf "EVar $" [str_var x]
      | EAppI (e, i) => sprintf "EAppI ($, $)" [str_e e, str_i i]
      | EMatchSum (e, branches) => sprintf "EMatchSum ($, $)" [str_e e, str_ls (str_pair (id, str_e) o get_bind) branches]
      | EMatchPair (e, branch) =>
        let
          val (name1, branch) = get_bind branch
          val (name2, branch) = get_bind branch
        in
          sprintf "EMatchPair ($, ($, $, $))" [str_e e, name1, name2, str_e branch]
        end
      | EMatchUnfold (e, branch) => sprintf "EMatchUnfold ($, $)" [str_e e, str_pair (id, str_e) $ get_bind branch]
      | EUnpackI (e, branch) =>
        let
          val (name1, branch) = get_bind branch
          val (name2, branch) = get_bind branch
        in
          sprintf "EUnpackI ($, ($, $, $))" [str_e e, name1, name2, str_e branch]
        end
      | _ => raise Unimpl ""
  end
    
(* depth=NONE means no depth limit *)
fun pp_e (params as (str_var, str_i, str_s, str_k, pp_t)) s (depth_t, depth) e =
  let
    val (reached_depth_limit, depth) =
        case depth of
            NONE => (false, NONE)
          | SOME n => if n <= 0 then
                        (true, NONE)
                      else
                        (false, SOME (n-1))
    val pp_e = pp_e params s (depth_t, depth)
    val pp_t = pp_t s depth_t
    fun space () = PP.space s 1
    fun add_space a = (space (); a)
    fun str v = PP.string s v
    fun comma () = (str ","; space ())
    fun open_hbox () = PP.openHBox s
    (* fun open_vbox () = PP.openVBox s (PP.Abs 2) *)
    fun open_vbox () = PP.openVBox s (PP.Rel 2)
    (* fun open_vbox_noindent () = PP.openVBox s (PP.Abs 0) *)
    fun open_vbox_noindent () = PP.openVBox s (PP.Rel 0)
    (* fun open_vbox_indent a = PP.openVBox s a *)
    (* fun open_vbox () = PP.openVBox s (PP.Rel 2) *)
    fun close_box () = PP.closeBox s
    fun pp_pair (fa, fb) (a, b) =
      (
        open_hbox ();
        str "(";
        fa a;
        comma ();
        fb b;
        str ")";
        close_box ()
      )
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
    if reached_depth_limit then str "..."
    else
    case e of
        EVar x =>
        (* ( *)
        (*   open_hbox (); *)
        (*   str "EVar"; *)
        (*   space (); *)
        str $ str_var x(* ; *)
        (*   close_box () *)
        (* ) *)
      | EVarConstr x =>
        (
          open_hbox ();
          str "EVarConstr";
          space ();
          str $ str_var x;
          close_box ()
        )
      | EMatchSum (e, branches) =>
        (
	  open_vbox ();
          open_hbox ();
          str "EMatchSum";
          space ();
          str "(";
          pp_e e;
	  close_box ();
          comma ();
          str "[";
	  open_vbox_noindent ();
          (* space (); *)
          pp_list (pp_pair (str, pp_e) o get_bind) branches;
	  close_box ();
          str "]";
          str ")";
          close_box ()
        )
      | EMatchPair (e, branch) =>
        let
          val (name1, branch) = get_bind branch
          val (name2, branch) = get_bind branch
        in
	  open_vbox ();
          (* space (); *)
          open_hbox ();
          str "EMatchPair";
          space ();
          str "(";
          pp_e e;
	  close_box ();
          comma ();
	  open_hbox ();
          str name1;
          comma ();
          str name2;
	  close_box ();
          comma ();
          pp_e branch;          
          str ")";
          close_box ()
        end
      | EMatchUnfold (e, branch) =>
        (
          open_hbox ();
          str "EMatchUnfold";
          space ();
          str "(";
          pp_e e;
          comma ();
	  open_vbox ();
          space ();
          pp_pair (str, pp_e) o get_bind $ branch;
	  close_box ();
          str ")";
          close_box ()
        )
      | EConst (ECTT ()) =>
        str "ETT"
      | EConst c =>
        (
          open_hbox ();
          str "EConst";
          space ();
          str $ str_expr_const c;
          close_box ()
        )
      (* | ELoc l => *)
      (*   ( *)
      (*     open_hbox (); *)
      (*     str "ELoc"; *)
      (*     space (); *)
      (*     str $ str_int l; *)
      (*     close_box () *)
      (*   ) *)
      | EUnOp (opr, e) =>
        (
          open_hbox ();
          str "EUnOp";
          space ();
          str "(";
          str $ str_expr_un_op (const_fun "<ty>") opr;
          comma ();
          pp_e e;
          str ")";
          close_box ()
        )
      | EBinOp (EBApp (), e1, e2) =>
        (
          open_hbox ();
          str "EApp";
          space ();
          str "(";
          pp_e e1;
          comma ();
          pp_e e2;
          str ")";
          close_box ()
        )
      | EBinOp (EBPair (), e1, e2) =>
        (
          open_hbox ();
          str "EPair";
          space ();
          str "(";
          pp_e e1;
          comma ();
          pp_e e2;
          str ")";
          close_box ()
        )
      | EBinOp (EBPrim (EBPIntAdd ()), e1, e2) =>
        (
          open_hbox ();
          str "EAdd";
          space ();
          str "(";
          pp_e e1;
          comma ();
          pp_e e2;
          str ")";
          close_box ()
        )
      | EBinOp (opr, e1, e2) =>
        (
          open_hbox ();
          str "EBinOp";
          space ();
          str "(";
          str $ str_expr_bin_op opr;
          comma ();
          pp_e e1;
          comma ();
          pp_e e2;
          str ")";
          close_box ()
        )
      | ETriOp (ETIte (), e, e1, e2) =>
        (
          open_vbox (); open_hbox (); str "ETIte"; space (); str "("; pp_e e; close_box (); comma ();
    	    open_vbox_noindent (); pp_e e1; comma ();
            space ();
            pp_e e2; close_box (); str ")"; close_box ()
        )
      (* | ETriOp (ETWrite, e1, e2, e3) => *)
      (*   ( *)
      (*     open_hbox (); *)
      (*     str "EWrite"; *)
      (*     space (); *)
      (*     str "("; *)
      (*     pp_e e1; *)
      (*     comma (); *)
      (*     pp_e e2; *)
      (*     comma (); *)
      (*     pp_e e3; *)
      (*     str ")"; *)
      (*     close_box () *)
      (*   ) *)
      | ETriOp (opr, e1, e2, e3) =>
        (
          open_hbox ();
          str $ str_expr_tri_op opr;
          space ();
          str "(";
          pp_e e1;
          comma ();
          pp_e e2;
          comma ();
          pp_e e3;
          str ")";
          close_box ()
        )
      | ECase (e, bind1, bind2) =>
        let
          val (name1, e1) = get_bind bind1
          val (name2, e2) = get_bind bind2
        in
          open_vbox_noindent (); open_hbox (); str "ECase"; space (); str "("; pp_e e; close_box (); comma ();
	  open_vbox (); str name1; str ":"; space ();
            pp_e e1; close_box (); comma ();
	  open_vbox (); str name2; str ":"; space ();
            pp_e e2; close_box (); str ")"; close_box ()
        end
      | EIfi (e, bind1, bind2) =>
        let
          val (name1, e1) = get_bind bind1
          val (name2, e2) = get_bind bind2
        in
          open_vbox_noindent (); open_hbox (); str "EIfi"; space (); str "("; pp_e e; close_box (); comma ();
	  open_vbox (); str name1; str ":"; space ();
            pp_e e1; close_box (); comma ();
	  open_vbox (); str name2; str ":"; space ();
            pp_e e2; close_box (); str ")"; close_box ()
        end
      | ELet (e, branch) =>
        let
          val (name, e_body) = get_bind branch
        in
	  open_vbox_noindent ();
          (* space (); *)
          open_vbox ();
          open_hbox ();
          str "ELet";
          space ();
          str "(";
          str name;
	  close_box ();
          comma ();
          pp_e e;
	  close_box ();
          comma ();
          pp_e e_body;
          str ")";
          close_box ()
        end
      | EAbs (i, bind) =>
        let
          val (name, t, e) = get_bind_anno bind
        in
          open_vbox ();
          open_hbox ();
          str "EAbs";
          space ();
          str "(";
          str $ str_i i;
          comma ();
          str name;
          comma ();
          pp_t t;
          close_box ();
          comma ();
          pp_e e;
          str ")";
          close_box ()
        end
      | EAbsConstr bind =>
        let
          val ((tnames, inames, ename), e) = unBind bind
        in
          open_vbox ();
          open_hbox ();
          str "EAbsConstr";
          space ();
          str "(";
          str $ sprintf "$, $, $" [str_ls binder2str tnames, str_ls binder2str inames, binder2str ename];
          close_box ();
          comma ();
          pp_e e;
          str ")";
          close_box ()
        end
      | ERec bind =>
        let
          val (name, t, e) = get_bind_anno bind
        in
          open_vbox ();
          open_hbox ();
          str "ERec";
          space ();
          str "(";
          str name;
          comma ();
          pp_t t;
          close_box ();
          comma ();
          pp_e e;
          str ")";
          close_box ()
        end
      | EAbsT bind =>
        let
          val (name, k, e) = get_bind_anno bind
        in
          open_vbox ();
          open_hbox ();
          str "EAbsT";
          space ();
          str "(";
          str name;
          comma ();
          str $ str_k k;
          close_box ();
          comma ();
          pp_e e;
          str ")";
          close_box ()
        end
      | EAppT (e, t) =>
        (
          open_hbox ();
          str "EAppT";
          space ();
          str "(";
          pp_e e;
          comma ();
          pp_t t;
          str ")";
          close_box ()
        )
      | EAppConstr (e1, ts, is, e2) =>
        (
          open_hbox ();
          str "EAppConstr";
          space ();
          str "(";
          pp_e e1;
          comma ();
          pp_list_bracket pp_t ts;
          comma ();
          str $ str_ls str_i is;
          comma ();
          pp_e e2;
          str ")";
          close_box ()
        )
      (* | EAbsI bind => *)
      (*   let *)
      (*     val (name, s, e) = get_bind_anno bind *)
      (*   in *)
      (*     open_vbox (); *)
      (*     open_hbox (); *)
      (*     str "EAbsI"; *)
      (*     space (); *)
      (*     str "("; *)
      (*     str name; *)
      (*     comma (); *)
      (*     str $ str_s s; *)
      (*     close_box (); *)
      (*     comma (); *)
      (*     pp_e e; *)
      (*     str ")"; *)
      (*     close_box () *)
      (*   end *)
      | EAbsI _ =>
        let
          val (binds, e) = MicroTiMLUtil.collect_EAbsI e
        in
          open_vbox ();
          open_hbox ();
          str "EAbsI";
          space ();
          str "(";
          foldl (fn ((name, s), ()) =>
                    (str $ fst name;
                     str ":"; space ();
                     str $ str_s s;
                     comma ()
                )) () binds;
          close_box ();
          space ();
          pp_e e;
          str ")";
          close_box ()
        end
      (* | EAppI (e, i) => *)
      (*   ( *)
      (*     open_hbox (); *)
      (*     str "EAppI"; *)
      (*     space (); *)
      (*     str "("; *)
      (*     pp_e e; *)
      (*     comma (); *)
      (*     str $ str_i i; *)
      (*     str ")"; *)
      (*     close_box () *)
      (*   ) *)
      | EAppI _ =>
        let
          val (e, is) = MicroTiMLUtil.collect_EAppI e
        in
        (
          open_hbox ();
          str "EAppI";
          space ();
          str "(";
          pp_e e;
          app (fn i => (comma ();
                        str $ str_i i)) is;
          str ")";
          close_box ()
        )
        end
      | EPack (t_all, t, e) =>
        (
          open_hbox ();
          str "EPack";
          space ();
          str "(";
          (* pp_t t; *)
          comma ();
          pp_e e;
          comma ();
          (* pp_t t_all; *)
          str ")";
          close_box ()
        )
      | EPackI (t, i, e) =>
        (
          open_hbox ();
          str "EPackI";
          space ();
          str "(";
          str $ str_i i;
          comma ();
          pp_e e;
          comma ();
          pp_t t;
          str ")";
          close_box ()
        )
      | EPackIs (t, is, e) =>
        (
          open_hbox ();
          str "EPackIs";
          space ();
          str "(";
          pp_t t;
          comma ();
          str "[";
          pp_list (str o str_i) is;
          str "]";
          comma ();
          pp_e e;
          str ")";
          close_box ()
        )
      | EUnpackI (e, branch) =>
        let
          val (name1, branch) = get_bind branch
          val (name2, branch) = get_bind branch
        in
	  open_vbox_noindent ();
          (* space (); *)
          open_hbox ();
          str "EUnpackI";
          space ();
          str "(";
          str name1;
          comma ();
          str name2;
          comma ();
          pp_e e;
	  close_box ();
          comma ();
          pp_e branch;          
          str ")";
          close_box ()
        end
      | EUnpack (e, branch) =>
        let
          val (name1, branch) = get_bind branch
          val (name2, branch) = get_bind branch
        in
	  open_vbox_noindent ();
          (* space (); *)
          open_hbox ();
          str "EUnpack";
          space ();
          str "(";
          str name1;
          comma ();
          str name2;
          comma ();
          pp_e e;
	  close_box ();
          comma ();
          pp_e branch;          
          str ")";
          close_box ()
        end
      (* | EUnpack (e, bind) => *)
      (*   let *)
      (*     val (tname, bind) = get_bind bind *)
      (*     val (ename, e) = get_bind bind *)
      (*   in *)
      (*     open_hbox (); *)
      (*     str "EUnpack"; *)
      (*     space (); *)
      (*     str "("; *)
      (*     str tname; *)
      (*     comma (); *)
      (*     str ename; *)
      (*     comma (); *)
      (*     pp_e e; *)
      (*     str ")"; *)
      (*     close_box () *)
      (*   end *)
      | EAscTime (e, i) =>
        (
	  open_vbox_noindent ();
          open_hbox ();
          str "EAscTime";
          space ();
          str "(";
          str $ str_i i;
          close_box ();
          comma ();
          pp_e e;
          str ")";
          close_box ()
        )
        (* pp_e e *)
      | EAscState (e, i) =>
        (
	  open_vbox_noindent ();
          open_hbox ();
          str "EAscState";
          space ();
          str "(";
          str $ str_i i;
          close_box ();
          comma ();
          pp_e e;
          str ")";
          close_box ()
        )
        (* pp_e e *)
      | EAscType (e, t) =>
        (
	  open_vbox_noindent ();
          open_hbox ();
          str "EAscType";
          space ();
          str "(";
          pp_t t;
          close_box ();
          comma ();
          pp_e e;
          str ")";
          close_box ()
        )
        (* pp_e e *)
      | ENever t =>
        (
          open_hbox ();
          str "ENever";
          space ();
          str "(";
          pp_t t;
          str ")";
          close_box ()
        )
      | EBuiltin (name, t) =>
        (
          open_hbox ();
          str "EBuiltin";
          space ();
          str "(";
          str name;
          comma ();
          pp_t t;
          str ")";
          close_box ()
        )
      | ENewArrayValues (t, es) =>
        (
          open_vbox ();
          open_hbox ();
          str "ENewArrayValues";
          space ();
          str "(";
          pp_t t;
          close_box ();
          comma ();
          open_vbox_noindent ();
          app (fn e => (pp_e e; comma ())) es;
          str ")";
          close_box ();
          close_box ()
        )
      | ELetIdx (i, branch) =>
        let
          val (name, e_body) = get_bind branch
        in
	  open_vbox_noindent ();
          (* space (); *)
          open_hbox ();
          str "ELetIdx";
          space ();
          str "(";
          str name;
          comma ();
          str $ str_i i;
	  close_box ();
          comma ();
          pp_e e_body;
          str ")";
          close_box ()
        end
      | ELetType (t, branch) =>
        let
          val (name, e_body) = get_bind branch
        in
	  open_vbox_noindent ();
          (* space (); *)
          open_hbox ();
          str "ELetType";
          space ();
          str "(";
          str name;
          comma ();
          pp_t t;
	  close_box ();
          comma ();
          pp_e e_body;
          str ")";
          close_box ()
        end
      | ELetConstr (e, branch) =>
        let
          val (name, e_body) = get_bind branch
        in
	  open_vbox_noindent ();
          (* space (); *)
          open_hbox ();
          str "ELetConstr";
          space ();
          str "(";
          str name;
          comma ();
          pp_e e;
	  close_box ();
          comma ();
          pp_e e_body;
          str ")";
          close_box ()
        end
      | EMallocPair (a, b) =>
        (
          open_hbox ();
          str "EMallocPair";
          space ();
          str "(";
          pp_e a;
          comma ();
          pp_e b;
          str ")";
          close_box ()
        )
      | EPairAssign (e1, proj, e2) =>
        (
          open_hbox ();
          str "EPairAssign";
          space ();
          str "(";
          pp_e e1;
          comma ();
          str $ str_proj proj;
          comma ();
          pp_e e2;
          str ")";
          close_box ()
        )
      | EProjProtected (proj, e) =>
        (
          open_hbox ();
          str "EProjProtected";
          space ();
          str "(";
          str $ str_proj proj;
          comma ();
          pp_e e;
          str ")";
          close_box ()
        )
      | EHalt (e, t) =>
        (
          open_hbox ();
          str "EHalt";
          space ();
          str "(";
          pp_e e;
          comma ();
          pp_t t;
          str ")";
          close_box ()
        )
      | EState x => str $ "EState " ^ x
  end

open WithPP
       
fun pp_e_to_fn params s ds e = withPP ("", 80, s) (fn s => pp_e params s ds e)
fun pp_e_fn params = pp_e_to_fn params TextIO.stdOut
fun pp_e_to_string_fn params ds e =
  pp_to_string "pp_e_to_string.tmp" (fn os => pp_e_to_fn params os ds e)
    
end
