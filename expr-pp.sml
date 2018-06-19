(***************** pretty printers  **********************)    

functor PrettyPrinterFn (structure Expr : IDX_TYPE_EXPR
                                            where type Idx.base_sort = BaseSorts.base_sort
                                              and type Type.base_type = BaseTypes.base_type
                                              and type Idx.region = Region.region
                                              and type Type.region = Region.region
                                              and type Idx.name = string * Region.region
                                              and type Type.name = string * Region.region
                                              and type Idx.var = string
                                              and type mod_id = string
                         sharing type Expr.Type.basic_sort = Expr.Idx.basic_sort
                         val str_uvar_bs : ('a -> string) -> 'a Expr.Idx.uvar_bs -> string
                         val str_uvar_i : ('basic_sort -> string) * ('idx -> string) -> ('basic_sort, 'idx) Expr.Idx.uvar_i -> string
                         val str_uvar_s : ('sort -> string) -> ('basic_sort, 'sort) Expr.Idx.uvar_s -> string
                         val str_uvar_mt : ('sort -> string) * ('kind -> string) * ('mtype -> string) -> ('sort, 'kind, 'mtype) Expr.Type.uvar_mt -> string
                        ) = struct

infixr 0 $
         
fun pp_t (params as (str_b, str_i : idx -> string, str_s, str_k)) s t =
    let
      val pp_t = pp_t params s depth
      fun space () = PP.space s 1
      fun add_space a = (space (); a)
      fun str v = PP.string s v
      fun comma () = (str ","; space ())
      fun open_hbox () = PP.openHBox s
      (* fun open_vbox () = PP.openVBox s (PP.Abs 2) *)
      fun open_vbox () = PP.openVBox s (PP.Rel 2)
      fun close_box () = PP.closeBox s
    in
      case t of
          TArrow ((st1, t1), (i, j), (st2, t2)) =>
          (
            open_hbox ();
            str "TArrow";
            space ();
            str "(";
            str $ str_st st1;
            comma ();
            pp_t t1;
            comma ();
            str $ str_i i;
            comma ();
            str $ str_i j;
            comma ();
            str $ str_st st2;
            comma ();
            pp_t t2;
            str ")";
            close_box ()
          )
        | TNat (i, _) =>
          (
            open_hbox ();
            str "TNat";
            space ();
            str "(";
            str $ str_i i;
            str ")";
            close_box ()
          )
        | TiBool (i, _) =>
          (
            open_hbox ();
            str "TiBool";
            space ();
            str "(";
            str $ str_i i;
            str ")";
            close_box ()
          )
        | TArray (t, i) =>
          (
            open_hbox ();
            str "TArray";
            space ();
            str "(";
            pp_t t;
            comma ();
            str $ str_i i;
            str ")";
            close_box ()
          )
        | TUnit _ =>
          str "TUnit"
        | TProd (t1, t2) =>
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
        | TUniI (s, Bind (name, ((i, j), t)), _) =>
          (
            open_hbox ();
            str "TUniI";
            space ();
            str "(";
            str name;
            comma ();
            str $ str_s s;
            comma ();
            str $ str_i i;
            comma ();
            str $ str_i j;
            comma ();
            pp_t t;
            str ")";
            close_box ()
          )
        | TVar x => str x
        | TApp (t1, t2) =>
          (
            open_hbox ();
            str "TApp";
            space ();
            str "(";
            pp_t t1;
            comma ();
            pp_t t2;
            str ")";
            close_box ()
          )
        | TAbs (k, Bind (name, t), _) =>
          (
            open_hbox ();
            str "TAbs";
            space ();
            str "(";
            str name;
            comma ();
            str $ str_k k;
            comma ();
            pp_t t;
            str ")";
            close_box ()
          )
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
        | TAbsI (b, Bind (name, t), _) =>
          (
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
          )
        | TSumbool (s1, s2) =>
          (
            open_hbox ();
            str "TSumbool";
            space ();
            str "(";
            str $ str_s s1;
            comma ();
            str $ str_s s2;
            str ")";
            close_box ()
          )
        | TBase (bt, _) =>
          (
            open_hbox ();
            str "TBase";
            space ();
            str "(";
            str $ str_bt bt;
            str ")";
            close_box ()
          )
        | TUVar (u, r) =>
          (
            open_hbox ();
            str "TUVar";
            space ();
            str "(";
            str $ str_uvar_mt (strn_bs, strn_k, strn_mt) u;
            str ")";
            close_box ()
          )
        | TDatatype (Bind (name, tbinds), _) =>
          let
            val (tname_kinds, (basic_sorts, constr_decls)) = unfold_binds tbinds
            fun str_constr_decl (name, core, _) =
                let
                  val (iname_sorts, (t, is)) = unfold_binds core
                in
                  (
                    str "[";
                    str name;
                    comma ();
                    app (fn ((name, _), s) => (str name; colon (); str $ str_s s; comma ())) iname_sorts;
                    pp_t t;
                    comma ();
                    app (fn i => (str $ str_i i; comma ())) is;
                    str "]"
                  )
                end
          in
            (
              open_hbox ();
              str "TDatatype";
              space ();
              str "(";
              str name;
              comma ();
              app (fn ((name, _), k) => (str name; colon (); str $ str_k k; comma ())) tname_kinds;
              app (fn b => (str $ str_b b; comma ())) basic_sorts;
              app str_constr_decl constr_decls;
              str ")";
              close_box ()
            )
          end
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
        | TState (x, _) =>
          (
            open_hbox ();
            str "TState";
            space ();
            str "(";
            str x;
            str ")";
            close_box ()
          )
        | TTuplePtr (ts, n, _) =>
          (
            open_hbox ();
            str "TTuplePtr";
            space ();
            str "(";
            str $ str_int n;
            comma ();
            app (fn t => (pp_t t; comma ())) ts;
            str ")";
            close_box ()
          )
    end

fun get_bind b = mapFst binder2str $ unBind b
fun get_bind_anno b =
  let
    val ((name, anno), t) = unBindAnno b
  in
    (Name2str name, anno, t)
  end

open WithPP
       
fun pp_t_fn params d t = withPP ("", 80, TextIO.stdOut) (fn s => pp_t params s d t)
val pp_t_to_fn = pp_t
fun pp_t_to_os_fn params os d t = withPP ("", 80, os) (fn s => pp_t params s d t)
fun pp_t_to_string_fn params d t =
  pp_to_string "pp_t_to_string.tmp" (fn os => pp_t_to_os_fn params os d t)
                              
fun get_bind b = mapFst binder2str $ unBind b
fun get_bind_anno b =
  let
    val ((name, anno), t) = unBindAnno b
  in
    (Name2str name, anno, t)
  end
                 
fun str_inj opr =
  case opr of
      InjInl () => "inl"
    | InjInr () => "inr"

fun str_expr_un_op str_t opr =
  case opr of
     EUInj (opr, t) => sprintf "inj ($, $)" [str_inj opr, str_t t]
    | EUFold t => sprintf "fold $" [str_t t]
    | EUUnfold () => "unfold"
    | EUTiML opr => Operators.str_expr_un_op opr
    | EUTupleProj n => "proj " ^ str_int n

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
    val pp_e = pp_e params s (depth_t, depth)
    val pp_t = pp_t s depth_t
    fun space () = PP.space s 1
    fun add_space a = (space (); a)
    fun str v = PP.string s v
    fun comma () = (str ","; space ())
    fun colon () = (str ":"; space ())
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
    case e of
      EVar (x, b) => decorate_var b x
    | EConst (c, _) => str_expr_const c
    | EState (x, _) => x
    | EUnOp (opr, e, _) => sprintf "($ $)" [str_expr_un_op opr, strn_e e]
    | EBinOp (opr, e1, e2) =>
      (case opr of
           EBApp _ => sprintf "($ $)" [strn_e e1, strn_e e2]
         | EBPair () =>
           let
             val es = collect_Pair e
           in
             sprintf "($)" [join ", " $ map strn_e es]
           end
         | EBNew () => sprintf "(new $ $)" [strn_e e1, strn_e e2]
         | EBRead () => sprintf "(read $ $)" [strn_e e1, strn_e e2]
         | _ => sprintf "($ $ $)" [strn_e e1, pretty_str_expr_bin_op opr, strn_e e2]
      )
    | ETriOp (opr, e1, e2, e3) => sprintf "($ $ $ $)" [str_expr_tri_op opr, strn_e e1, strn_e e2, strn_e e3]
    | EEI (opr, e, i) =>
      (case opr of
           EEIAppI () => sprintf "($ {$})" [strn_e e, strn_i i]
         | EEIAscTime () => sprintf "($ |> $)" [strn_e e, strn_i i]
         | EEIAscSpace () => sprintf "($ |# $)" [strn_e e, strn_i i]
      )
    | EET (opr, e, t) =>
      (case opr of
           EETAppT () => sprintf "($ [$])" [strn_e e, strn_mt t]
         | EETAsc () => sprintf "($ : $)" [strn_e e, strn_mt t]
         | EETHalt () => sprintf "(halt $ [$])" [strn_e e, strn_mt t]
      )
    | ENewArrayValues (t, es, _) => sprintf "array [$] {$}" [strn_mt t, join ", " $ map strn_e es]
    | ET (opr, t, _) =>
      (case opr of
           ETNever () => sprintf "(never [$])" [strn_mt t]
         | ETBuiltin name => sprintf "(builtin $ [$])" [name, strn_mt t]
      )
    | EAbs (st, bind, spec) => 
      let
        val (pn, e) = Unbound.unBind bind
        val st = strn_state st
        val pn = strn_pn pn
	val e = strn_e e
      in
        sprintf "(fn $$$ => $)" [st, pn, default "" $ Option.map (fn (i, j) => sprintf " return $, $" [strn_i i, strn_i j]) spec, e]
      end
    | EAbsI (bind, _) =>
      let
        val ((name, s), e) = unBindAnno bind
        val name = Name2str name
      in
        sprintf "(fn {$ : $} => $)" [name, strn_s s, strn_e e]
      end
    | ELet (return, bind, _) => 
      let
        val (decls, e) = Unbound.unBind bind
        val decls = unTeles decls
        val return = strn_return return
        val decls = map strn_decl decls
      in
        sprintf "let $$ in $ end" [return, join_prefix " " decls, strn_e e]
      end
    | EAppConstr ((x, b), ts, is, e, _) =>
      sprintf "([$]$$ $)" [
        decorate_var b x,
        (join "" o map (prefix " ") o map (fn t => sprintf "{$}" [strn_mt t])) ts,
        (join "" o map (prefix " ") o map (fn i => sprintf "{$}" [strn_i i])) is,
        strn_e e]
    | ECase (e, return, rules, _) => sprintf "(case $ $of $)" [strn_e e, strn_return return, join " | " (map strn_rule rules)]
    | ECaseSumbool (e, bind1, bind2, _) =>
      let
        val (name1, e1) = unBindSimpName bind1
        val (name2, e2) = unBindSimpName bind2
      in
        sprintf "(case_sumbool $ (left $ => $) (right $ => $))" [strn_e e, fst name1, strn_e e1, fst name2, strn_e e2]
      end
    | EIfi (e, bind1, bind2, _) =>
      let
        val (name1, e1) = unBindSimpName bind1
        val (name2, e2) = unBindSimpName bind2
      in
        sprintf "(ifi $ (itrue $ => $) (ifalse $ => $))" [strn_e e, fst name1, strn_e e1, fst name2, strn_e e2]
      end
    | ESetModify (is_modify, x, es, e, _) => sprintf "($ $$ $)" [if is_modify then "modify" else "set", x, join "" $ map (surround "[" "]" o strn_e) es, strn_e e]
    | EGet (x, es, _) => sprintf "$$" [x, join "" $ map (surround "[" "]" o strn_e) es]

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
      | EUnOp (EUTiML (EUProj (ProjFst ())), e) =>
        (
          open_hbox ();
          str "EFst";
          space ();
          str "(";
          pp_e e;
          str ")";
          close_box ()
        )
      | EUnOp (EUTiML (EUProj (ProjSnd ())), e) =>
        (
          open_hbox ();
          str "ESnd";
          space ();
          str "(";
          pp_e e;
          str ")";
          close_box ()
        )
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
      | EAbs (i, bind, spec) =>
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
          colon ();
          pp_t t;
          Option.app (fn (i, j) =>
                         (comma ();
                          str $ str_i i;
                          comma ();
                          str $ str_i j
                     )) spec;
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
          colon ();
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
                     colon ();
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
          str "EAppIs";
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
          pp_e e;
          comma ();
          pp_t t;
          comma ();
          pp_t t_all;
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
      | EAscSpace (e, i) =>
        (
	  open_vbox_noindent ();
          open_hbox ();
          str "EAscSpace";
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
      | ETuple es =>
        (
          open_hbox ();
          str "ETuple";
          space ();
          str "(";
          app (fn e => (pp_e e; comma ())) es;
          str ")";
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
