(***************** pretty printers  **********************)    

structure AstPP = struct

open Util
open Region
open Operators
open Ast

infixr 0 $

fun str_long_id (m, (x, _)) = default "" (Option.map (fn (m, _) => m ^ "..") m) ^ x
      
fun pp_i s i =
    let
      val pp_i = pp_i s
      fun space () = PP.space s 1
      fun add_space a = (space (); a)
      fun str v = PP.string s v
      fun strs s = (str s; space ())
      fun pp_id x = str $ fst x
      fun pp_long_id x = str $ str_long_id x
      fun pp_int n = str $ str_int n
      fun pp_bool n = str $ str_bool n
      fun comma () = (str ","; space ())
      fun colon () = (str ":"; space ())
      fun open_hbox () = PP.openHBox s
      fun open_vbox () = PP.openVBox s (PP.Rel 2)
      fun close_box () = PP.closeBox s
    in
      case i of
	 IVar x => pp_long_id x
       | INat (n, _) => pp_int n
       | ITime (s, _) => str s
       | IBinOp (opr, i1, i2, _) =>
         (
           open_hbox ();
           str "IBinOp";
           space ();
           str "(";
           str $ str_idx_bin_op opr;
           comma ();
           pp_i i1;
           comma ();
           pp_i i2;
           str ")";
           close_box ()
         )
       | ITT r => str "ITT"
       | IAbs (names, i, _) =>
         (
           open_hbox ();
           str "IAbs";
           space ();
           str "(";
           app (fn name => (pp_id name; comma ())) names;
           pp_i i;
           str ")";
           close_box ()
         )
       | IDiv (i, (n, _), _) =>
         (
           open_hbox ();
           str "IDiv";
           space ();
           str "(";
           pp_i i;
           comma ();
           pp_int n;
           str ")";
           close_box ()
         )
    end

fun pp_p s p =
    let
      val pp_i = pp_i s
      val pp_p = pp_p s
      fun space () = PP.space s 1
      fun add_space a = (space (); a)
      fun str v = PP.string s v
      fun strs s = (str s; space ())
      fun pp_id x = str $ fst x
      fun pp_long_id x = str $ str_long_id x
      fun pp_int n = str $ str_int n
      fun pp_bool n = str $ str_bool n
      fun comma () = (str ","; space ())
      fun colon () = (str ":"; space ())
      fun open_hbox () = PP.openHBox s
      fun open_vbox () = PP.openVBox s (PP.Rel 2)
      fun close_box () = PP.closeBox s
    in
      case p of
	  PConst (s, _) => str s
        | PNot (p, _) =>
          (
            open_hbox ();
            str "PNot";
            space ();
            str "(";
            pp_p p;
            str ")";
            close_box ()
          )
	| PBinConn (opr, p1, p2, _) =>
         (
           open_hbox ();
           str "PBinConn";
           space ();
           str "(";
           str $ str_bin_conn opr;
           comma ();
           pp_p p1;
           comma ();
           pp_p p2;
           str ")";
           close_box ()
         )
	| PBinPred (opr, i1, i2, _) =>
         (
           open_hbox ();
           str "PBinPred";
           space ();
           str "(";
           str $ str_bin_pred opr;
           comma ();
           pp_i i1;
           comma ();
           pp_i i2;
           str ")";
           close_box ()
         )
    end

fun pp_bsort s bs =
    let
      fun space () = PP.space s 1
      fun str v = PP.string s v
      fun strs s = (str s; space ())
      fun pp_id x = str $ fst x
      fun open_hbox () = PP.openHBox s
      fun close_box () = PP.closeBox s
    in
      case bs of
          BSId x =>
          (
            open_hbox ();
            strs "BSId";
            pp_id x;
            close_box ()
          )
    end
      
fun pp_s s sort =
    let
      val pp_i = pp_i s
      val pp_p = pp_p s
      val pp_bsort = pp_bsort s
      fun space () = PP.space s 1
      fun add_space a = (space (); a)
      fun str v = PP.string s v
      fun strs s = (str s; space ())
      fun pp_id x = str $ fst x
      fun pp_long_id x = str $ str_long_id x
      fun pp_int n = str $ str_int n
      fun pp_bool n = str $ str_bool n
      fun comma () = (str ","; space ())
      fun colon () = (str ":"; space ())
      fun open_hbox () = PP.openHBox s
      fun open_vbox () = PP.openVBox s (PP.Rel 2)
      fun close_box () = PP.closeBox s
    in
      case sort of
	 SBasic bs => pp_bsort bs
       | SSubset (bs, name, p, _) =>
         (
           open_hbox ();
           str "SSubset";
           space ();
           str "(";
           pp_bsort bs;
           comma ();
           pp_id name;
           comma ();
           pp_p p;
           str ")";
           close_box ()
         )
       | SBigO (s, bs, i, _) =>
         (
           open_hbox ();
           str "SBigO";
           space ();
           str "(";
           str s;
           comma ();
           pp_bsort bs;
           comma ();
           pp_i i;
           str ")";
           close_box ()
         )
    end
      
fun pp_st s st =
    let
      val pp_i = pp_i s
      fun str v = PP.string s v
      fun space () = PP.space s 1
      fun pp_id x = str $ fst x
      fun pp_long_id x = str $ str_long_id x
      fun comma () = (str ","; space ())
      fun colon () = (str ":"; space ())
      fun open_hbox () = PP.openHBox s
      fun close_box () = PP.closeBox s
    in
      (
        open_hbox ();
        str "{";
        app (fn (k, i) => (pp_id k; colon (); pp_i i; comma ())) st;
        str "}";
        close_box ()
      )
    end

fun str_quan q =
    case q of
        Forall () => "Forall"
                    
fun pp_sort_bind s (name, sort, _) =
    let
      val pp_s = pp_s s
      fun space () = PP.space s 1
      fun str v = PP.string s v
      fun pp_id x = str $ fst x
      fun comma () = (str ","; space ())
      fun colon () = (str ":"; space ())
      fun open_hbox () = PP.openHBox s
      fun close_box () = PP.closeBox s
    in
        open_hbox ();
        str "(";
        pp_id name;
        colon ();
        pp_s sort;
        str ")";
        close_box ()
    end
      
fun pp_bsort_bind s (name, bsort, _) =
    let
      val pp_bsort = pp_bsort s
      fun space () = PP.space s 1
      fun str v = PP.string s v
      fun pp_id x = str $ fst x
      fun comma () = (str ","; space ())
      fun colon () = (str ":"; space ())
      fun open_hbox () = PP.openHBox s
      fun close_box () = PP.closeBox s
    in
        open_hbox ();
        str "(";
        pp_id name;
        colon ();
        pp_bsort bsort;
        str ")";
        close_box ()
    end
      
fun pp_t s t =
    let
      val pp_i = pp_i s
      val pp_t = pp_t s
      val pp_st = pp_st s
      val pp_sort_bind = pp_sort_bind s
      val pp_bsort_bind = pp_bsort_bind s
      fun space () = PP.space s 1
      fun add_space a = (space (); a)
      fun str v = PP.string s v
      fun pp_id x = str $ fst x
      fun pp_long_id x = str $ str_long_id x
      fun comma () = (str ","; space ())
      fun colon () = (str ":"; space ())
      fun pp_id_or_bsort_bind b = app_inl_inr pp_id pp_bsort_bind b
      fun open_hbox () = PP.openHBox s
      (* fun open_vbox () = PP.openVBox s (PP.Abs 2) *)
      fun open_vbox () = PP.openVBox s (PP.Rel 2)
      fun close_box () = PP.closeBox s
    in
      case t of
	 TVar x => pp_long_id x
       | TArrow ((st1, t1), (i, j), (st2, t2), _) =>
          (
            open_hbox ();
            str "TArrow";
            space ();
            str "(";
            pp_st st1;
            comma ();
            pp_t t1;
            comma ();
            pp_i i;
            comma ();
            pp_i j;
            comma ();
            pp_st st2;
            comma ();
            pp_t t2;
            str ")";
            close_box ()
          )
       | TProd (t1, t2, _) =>
          (
            open_hbox ();
            str "TProd";
            space ();
            str "(";
            pp_t t1;
            comma ();
            pp_t t2;
            str ")";
            close_box ()
          )
       | TQuan (q, binds, t, _) =>
         (
           open_hbox ();
           str "TQuan";
           space ();
           str "(";
           str $ str_quan q;
           comma ();
           app (fn b => (pp_sort_bind b; comma ())) binds;
           pp_t t;
           str ")";
           close_box ()
         )
       | TAppT (t1, t2, _) =>
         (
           open_hbox ();
           str "TAppT";
           space ();
           str "(";
           pp_t t1;
           comma ();
           pp_t t2;
           str ")";
           close_box ()
         )
       | TAppI (t, i, _) =>
         (
           open_hbox ();
           str "TAppI";
           space ();
           str "(";
           pp_t t;
           comma ();
           pp_i i;
           str ")";
           close_box ()
         )
       | TAbs (binds, t, _) =>
         (
           open_hbox ();
           str "TAbs";
           space ();
           str "(";
           app (fn b => (pp_id_or_bsort_bind b; comma ())) binds;
           pp_t t;
           str ")";
           close_box ()
         )
       | TRecord (ts, _) =>
         (
           open_hbox ();
           str "TRecord";
           space ();
           str "(";
           app (fn (name, t) => (pp_id name; colon (); pp_t t; comma ())) ts;
           str ")";
           close_box ()
         )
    end

fun pp_datatype s (name, tnames, binds, basic_sorts, constr_decls, _) =
    let
      val pp_t = pp_t s
      val pp_bsort = pp_bsort s
      val pp_sort_bind = pp_sort_bind s
      val pp_bsort_bind = pp_bsort_bind s
      fun space () = PP.space s 1
      fun add_space a = (space (); a)
      fun str v = PP.string s v
      fun pp_id x = str $ fst x
      fun pp_long_id x = str $ str_long_id x
      fun comma () = (str ","; space ())
      fun colon () = (str ":"; space ())
      fun pp_id_or_bsort_bind b = app_inl_inr pp_id pp_bsort_bind b
      fun open_hbox () = PP.openHBox s
      fun open_vbox () = PP.openVBox s (PP.Rel 2)
      fun close_box () = PP.closeBox s
      fun str_constr_decl (name, binds, core, _) =
          (
            comma ();
            str "[";
            pp_id name;
            colon ();
            app (fn bind => (pp_sort_bind bind; comma ())) binds;
            Option.app (fn (t1, t2) => (pp_t t1; comma (); Option.app pp_t t2)) core;
            str "]"
          )
    in
      (
        open_hbox ();
        str name;
        app (fn name => (comma (); str name)) tnames;
        app (fn b => (comma (); pp_bsort_bind b)) binds;
        app (fn b => (comma (); pp_bsort b)) basic_sorts;
        app str_constr_decl constr_decls;
        close_box ()
      )
    end
            
fun pp_pn s pn =
    let
      val pp_pn = pp_pn s
      val pp_t = pp_t s
      fun space () = PP.space s 1
      fun str v = PP.string s v
      fun strs s = (str s; space ())
      fun pp_id x = str $ fst x
      fun pp_long_id x = str $ str_long_id x
      fun pp_int n = str $ str_int n
      fun pp_bool n = str $ str_bool n
      fun comma () = (str ","; space ())
      fun open_hbox () = PP.openHBox s
      fun close_box () = PP.closeBox s
    in
      case pn of
	  PnConstr ((x, b), names, pn, _) =>
         (
           open_hbox ();
           strs "PnConstr";
           str "(";
           pp_long_id x;
           comma ();
           pp_bool b;
           comma ();
           app (fn s => (str s; comma ())) names;
           Option.app pp_pn pn;
           str ")";
           close_box ()
         )
        | PnTuple (pns, _) =>
         (
           open_hbox ();
           strs "PnTuple";
           str "(";
           app (fn pn => (pp_pn pn; comma ())) pns;
           str ")";
           close_box ()
         )
        | PnAlias (name, pn, _) =>
         (
           open_hbox ();
           strs "PnAlias";
           str "(";
           pp_id name;
           comma ();
           pp_pn pn;
           str ")";
           close_box ()
         )
        | PnAnno (pn, t, _) =>
         (
           open_hbox ();
           strs "PnAnno";
           str "(";
           pp_pn pn;
           comma ();
           pp_t t;
           str ")";
           close_box ()
         )
    end

fun pp_bind s bind =
    case bind of
        BindSorting bind => pp_sort_bind s bind
      | BindTyping pn => pp_pn s pn

fun str_expr_const c =
    case c of
        ECInt n => n
      | ECNat n => "#" ^ str_int n
      | ECString s => sprintf "\"$\"" [s]
      | ECChar c => sprintf "'$'" [str_char c]

fun str_ast_expr_unop opr =
    case opr of
        EUTiML opr => str_expr_un_op opr
      | EUDeref () => "deref"
                            
fun str_ast_expr_binop opr =
    case opr of
         EBTiML opr => str_expr_bin_op opr
       | EBStrConcat () => "str_concat"
       | EBSetRef () => "set_ref"

fun str_ast_expr_triop opr =
    case opr of
        ETIte () => "EIte"
      | ETIfDec () => "EIfDec"
      | ETIfi () => "EIfi"

fun pp_return s (t, i, j) =
    let
      val pp_i = pp_i s
      val pp_t = pp_t s
      fun space () = PP.space s 1
      fun str v = PP.string s v
      fun comma () = (str ","; space ())
    in
      (Option.app pp_t; comma ();
       Option.app (pp_i) i; comma ();
       Option.app (pp_i) j)
    end

fun str_storage st =
    case st of
        StMemory => "memory"
      | StStorage => "storage"
      (* | StIndexed => "indexed" *)
      
fun pp_e s e =
    let
      val pp_e = pp_e s
      val pp_decls = pp_decls s
      val pp_i = pp_i s
      val pp_t = pp_t s
      val pp_return = pp_return s
      val pp_pn = pp_pn s
      val pp_st = pp_st s
      val pp_bind = pp_bind s
      fun space () = PP.space s 1
      fun add_space a = (space (); a)
      fun str v = PP.string s v
      fun strs s = (str s; space ())
      fun pp_id x = str $ fst x
      fun pp_long_id x = str $ str_long_id x
      fun pp_int n = str $ str_int n
      fun pp_bool n = str $ str_bool n
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
          EVar (x, (b1, b2)) =>
          (
            open_hbox ();
            strs "EVar";
            str "(";
            pp_long_id x;
            comma ();
            str $ str_bool b1;
            comma ();
            str $ str_bool b2;
            str ")";
            close_box ()
          )
        | ETuple (es, _) =>
          (
            open_hbox ();
            strs "ETuple";
            str "(";
            app (fn e => (pp_e e; comma ())) es;
            str ")";
            close_box ()
          )
        | EAbs (binds, return, e, _) =>
          (
            open_hbox ();
            strs "EAbs";
            str "(";
            app (fn bind => (pp_bind bind; comma ())) binds;
            pp_return return;
            comma ();
            pp_e e;
            str ")";
            close_box ()
          )
        | EAppI (e, i, _) =>
          (
            open_hbox ();
            strs "EAppI";
            str "(";
            pp_e e;
            comma ();
            pp_i i;
            str ")";
            close_box ()
          )
        | ECase (e, return, rules, _) =>
          (
            open_vbox_noindent (); open_hbox (); str "ECase"; space (); pp_e e; comma (); pp_return return; close_box (); space ();
	    app
              (fn (pn, e) =>
                  (open_vbox ();
                   open_hbox (); str "|"; space (); pp_pn pn; space (); str "=>"; close_box (); space ();
                   pp_e e; close_box (); space ())
              ) rules;
            close_box ()
          )
        | EAsc (e, t, _) =>
          (
            open_hbox ();
            strs "EAsc";
            str "(";
            pp_e e;
            comma ();
            pp_t t;
            str ")";
            close_box ()
          )
        | EAscTime (e, i, _) =>
          (
            open_hbox ();
            strs "EAscTime";
            str "(";
            pp_e e;
            comma ();
            pp_i i;
            str ")";
            close_box ()
          )
        | EAscSpace (e, i, _) =>
          (
            open_hbox ();
            strs "EAscSpace";
            str "(";
            pp_e e;
            comma ();
            pp_i i;
            str ")";
            close_box ()
          )
        | ELet (return, decls, e, _) =>
          (
	    open_vbox_noindent ();
            open_hbox (); str "ELet"; space (); pp_return return; close_box (); space ();
            pp_decls decls;
            str "In"; space ();
            pp_e e; space ();
            str "End";
            close_box ()
          )
        | EConst (c, _) =>
          (
            open_hbox ();
            strs "EConst";
            str $ str_expr_const c;
            close_box ()
          )
        | EUnOp (opr, e, _) =>
          (
            open_hbox ();
            str "EUnOp";
            space ();
            str "(";
            str $ str_ast_expr_unop opr;
            comma ();
            pp_e e;
            str ")";
            close_box ()
          )
        | EBinOp (opr, e1, e2, _) =>
          (
            open_hbox ();
            str "EBinOp";
            space ();
            str "(";
            str $ str_ast_expr_binop opr;
            comma ();
            pp_e e1;
            comma ();
            pp_e e2;
            str ")";
            close_box ()
          )
        | ETriOp (ETIte (), e, e1, e2, _) =>
          (
            open_vbox (); open_hbox (); str "ETIte"; space (); str "("; pp_e e; close_box (); comma ();
    	    open_vbox_noindent (); pp_e e1; comma ();
            space ();
            pp_e e2; close_box (); str ")"; close_box ()
          )
        | ETriOp (ETIfi (), e, e1, e2, _) =>
          (
            open_vbox (); open_hbox (); str "ETIfi"; space (); str "("; pp_e e; close_box (); comma ();
    	    open_vbox_noindent (); pp_e e1; comma ();
            space ();
            pp_e e2; close_box (); str ")"; close_box ()
          )
        | ETriOp (opr, e1, e2, e3, _) =>
          (
            open_hbox ();
            str $ str_ast_expr_triop opr;
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
        | ENever r => str "ENever"
        | ESetModify (b, (e1, es), e2, _) =>
          (
            open_hbox ();
            str "ESetModify";
            space ();
            str "(";
            pp_bool b;
            comma ();
            pp_e e1;
            comma ();
            pp_list_bracket pp_e es;
            comma ();
            pp_e e2;
            str ")";
            close_box ()
          )
        | EGet ((e, es), _) =>
          (
            open_hbox ();
            str "EGet";
            space ();
            str "(";
            pp_e e;
            comma ();
            pp_list_bracket pp_e es;
            str ")";
            close_box ()
          )
        | ERecord (es, _) =>
          (
            open_hbox ();
            strs "ERecord";
            str "(";
            app (fn (name, e) => (pp_id name; colon (); pp_e e; comma ())) es;
            str ")";
            close_box ()
          )
        | EField (e, name, _) =>
          (
            open_hbox ();
            strs "EField";
            str "(";
            pp_e e;
            comma ();
            pp_id name;
            str ")";
            close_box ()
          )
        | EAsm (e, _) =>
          (
            open_hbox ();
            strs "EAsm";
            str "(";
            pp_e e;
            str ")";
            close_box ()
          )
        | EReturn (e, _) =>
          (
            open_hbox ();
            strs "EReturn";
            str "(";
            pp_e e;
            str ")";
            close_box ()
          )
        | EFor (id, t, e1, e2, e3, e4, _) =>
          (
            open_vbox ();
            open_hbox ();
            strs "EFor";
            str "(";
            pp_id id;
            Option.app (fn t => (comma (); pp_t t)) t;
            comma ();
            pp_e e1;
            comma ();
            pp_e e2;
            comma ();
            pp_e e3;
            str ")";
            close_box ();
            space ();
            pp_e e4;
            close_box ()
          )
        | EWhile (e1, e2, _) =>
          (
            open_vbox ();
            open_hbox ();
            strs "EWhile";
            str "(";
            pp_e e1;
            str ")";
            close_box ();
            space ();
            pp_e e2;
            close_box ()
          )
        | ESemis (es, _) =>
          (
            open_vbox_noindent ();
            open_hbox ();
            strs "ESemis";
            str "(";
            close_box ();
            space ();
            app (fn e => (pp_e e; strs ";")) es;
            str ")";
            close_box ()
          )
        | ELet2 (st, pn, e, _) =>
          (
            open_hbox ();
            strs "ELet2";
            str "(";
            Option.app (fn st => (strs $ str_storage st; comma ())) st;
            pp_pn pn;
            comma ();
            Option.app pp_e e;
            str ")";
            close_box ()
          )
        | EIfs (ifs, _) =>
          let
            fun pp_if i =
              case i of
                  If (e1, e2, _) =>
                  (
                    open_vbox ();
                    open_hbox ();
                    strs "If";
                    str "(";
                    pp_e e1;
                    strs ")";
                    str "Then";
                    close_box ();
                    space ();
                    pp_e e2;
                    close_box ()
                  )
                | Elseif (e1, e2, _) =>
                  (
                    open_vbox ();
                    open_hbox ();
                    strs "Elseif";
                    str "(";
                    pp_e e1;
                    strs ")";
                    str "Then";
                    close_box ();
                    space ();
                    pp_e e2;
                    close_box ()
                  )
                | Else (e, _) =>
                  (
                    open_vbox ();
                    strs "Else";
                    pp_e e;
                    close_box ()
                  )
          in
          (
            open_vbox_noindent ();
            app (fn i => (pp_if i; space ())) ifs;
            str "End";
            close_box ()
          )
          end
    end

and pp_d s d =
    let
      val pp_d = pp_d s
      val pp_e = pp_e s
      val pp_i = pp_i s
      val pp_t = pp_t s
      val pp_pn = pp_pn s
      val pp_st = pp_st s
      val pp_return = pp_return s
      val pp_bind = pp_bind s
      val pp_datatype = pp_datatype s
      val pp_s = pp_s s
      fun space () = PP.space s 1
      fun str v = PP.string s v
      fun strs s = (str s; space ())
      fun comma () = (str ","; space ())
      fun colon () = (str ":"; space ())
      fun pp_id x = str $ fst x
      fun pp_long_id x = str $ str_long_id x
      fun open_hbox () = PP.openHBox s
      fun open_vbox () = PP.openVBox s (PP.Rel 2)
      fun open_vbox_noindent () = PP.openVBox s (PP.Rel 0)
      fun close_box () = PP.closeBox s
      fun equal () = (str "="; space ())
    in
      case d of
          DVal (names, pn, e, _) =>
          (
            open_hbox ();
            strs "DVal";
            app (fn name => (pp_id name; space ())) names;
            pp_pn pn;
            space ();
            equal ();
            pp_e e;
            close_box ()
          )
        | DRec (tnames, name, binds, pre_st, post_st, return, e, _) =>
          (
            open_vbox ();
            open_hbox ();
            strs "DRec";
            pp_id name;
            space ();
            app (fn name => (str "["; pp_id name; str "]"; space ())) tnames;
            app (fn bind => (pp_bind bind; space ())) binds;
            comma ();
            pp_st pre_st;
            comma ();
            Option.app pp_st post_st;
            comma ();
            pp_return return;
            space ();
            equal ();
            close_box ();
            space ();
            pp_e e;
            close_box ()
          )
        | DDatatype dt =>
          (
            open_hbox ();
            strs "DDatatype";
            str "(";
            pp_datatype dt;
            str ")";
            close_box ()
          )
        | DIdxDef (name, s, i) =>
          (
            open_hbox ();
            strs "DIdxDef";
            pp_id name;
            Option.app (fn s => (strs ":"; pp_s s)) s; space ();
            strs "=";
            pp_i i;
            close_box ()
          )
        | DAbsIdx2 (name, s, i) =>
          (
            open_hbox ();
            strs "DAbsIdx2";
            pp_id name;
            Option.app (fn s => (strs ":"; pp_s s)) s; space ();
            strs "=";
            pp_i i;
            close_box ()
          )
        | DAbsIdx (name, s, i, decls, _) =>
          (
            open_hbox ();
            strs "DAbsIdx";
            pp_id name;
            space ();
            Option.app (fn s => (strs ":"; pp_s s)) s; space ();
            strs "=";
            Option.app (fn i => (space (); pp_i i)) i; 
            close_box ();
            strs "With";
            app (fn d => (pp_d d; space ())) decls;
            str "End"
          )
        | DTypeDef (name, t) =>
          (
            open_hbox ();
            strs "DTypeDef";
            pp_id name;
            space ();
            strs "=";
            pp_t t;
            close_box ()
          )
        | DOpen x =>
          (
            open_hbox ();
            strs "DOpen";
            pp_id x;
            close_box ()
          )
        | DState (name, t, init) =>
          let
            fun pp_init init =
                case init of
                    InitExpr e => pp_e e
                  | InitArray es =>
                    (
                      open_vbox_noindent ();
                      str "{";
                      app (fn e => (pp_e e; comma ())) es;
                      str "}";
                      close_box ()
                    )
          in
          (
            open_hbox ();
            strs "DState";
            pp_id name;
            space ();
            pp_t t;
            Option.app (fn init => (space (); equal (); pp_init init)) init;
            close_box ()
          )
          end
        | DEvent (name, ts) =>
          (
            open_hbox ();
            strs "DEvent";
            str "(";
            pp_id name;
            app (fn (t, b) => (comma (); pp_t t; comma (); str $ str_bool b)) ts;
            str ")";
            close_box ()
          )
    end
      
and pp_decls s decls =
  let
    val pp_d = pp_d s
    fun space () = PP.space s 1
    fun open_vbox_noindent () = PP.openVBox s (PP.Rel 0)
    fun close_box () = PP.closeBox s
  in
    open_vbox_noindent ();
    app (fn d => (pp_d d; space ())) decls;
    close_box ()
  end

fun pp_spec s spec =
    let
      val pp_d = pp_d s
      val pp_e = pp_e s
      val pp_i = pp_i s
      val pp_t = pp_t s
      val pp_pn = pp_pn s
      val pp_st = pp_st s
      val pp_return = pp_return s
      val pp_bind = pp_bind s
      val pp_datatype = pp_datatype s
      val pp_s = pp_s s
      val pp_bsort = pp_bsort s
      fun space () = PP.space s 1
      fun str v = PP.string s v
      fun strs s = (str s; space ())
      fun comma () = (str ","; space ())
      fun colon () = (str ":"; space ())
      fun pp_id x = str $ fst x
      fun pp_long_id x = str $ str_long_id x
      fun open_hbox () = PP.openHBox s
      fun open_vbox () = PP.openVBox s (PP.Rel 2)
      fun close_box () = PP.closeBox s
      fun equal () = (str "="; space ())
    in
      case spec of
          SpecVal (name, names, t, _) =>
          (
            open_hbox ();
            strs "SpecVal";
            str "(";
            pp_id name;
            app (fn name => (comma (); pp_id name)) names;
            comma ();
            pp_t t;
            str ")";
            close_box ()
          )
        | SpecDatatype dt =>
          (
            open_hbox ();
            strs "SpecDatatype";
            str "(";
            pp_datatype dt;
            str ")";
            close_box ()
          )
        | SpecIdx (name, s) =>
          (
            open_hbox ();
            strs "SpecIdx";
            str "(";
            pp_id name;
            comma ();
            pp_s s;
            str ")";
            close_box ()
          )
        | SpecType (names, bs, _) =>
          (
            open_hbox ();
            strs "SpecType";
            str "(";
            app (fn name => (pp_id name; comma ())) names;
            app (fn b => (pp_bsort b; comma ())) bs;
            str ")";
            close_box ()
          )
        | SpecTypeDef (name, t) =>
          (
            open_hbox ();
            strs "SpecTypeDef";
            str "(";
            pp_id name;
            comma ();
            pp_t t;
            str ")";
            close_box ()
          )
        | SpecFun (name, ts, return) =>
          (
            open_hbox ();
            strs "SpecFun";
            str "(";
            pp_id name;
            app (fn t => (comma (); pp_t t)) ts;
            comma ();
            pp_return return;
            str ")";
            close_box ()
          )
        | SpecEvent (name, ts) =>
          (
            open_hbox ();
            strs "SpecEvent";
            str "(";
            pp_id name;
            app (fn (t, b) => (comma (); pp_t t; comma (); str $ str_bool b)) ts;
            str ")";
            close_box ()
          )
    end
      
fun pp_sgn s sgn =
    let
      val pp_spec = pp_spec s
      fun space () = PP.space s 1
      fun str v = PP.string s v
      fun strs s = (str s; space ())
      fun open_vbox_noindent () = PP.openVBox s (PP.Rel 0)
      fun close_box () = PP.closeBox s
    in
      case sgn of
          SigComponents (specs, _) =>
          (
            open_vbox_noindent ();
            strs "Sig";
            app (fn spec => (pp_spec spec; space ())) specs;
            str "End";
            close_box ()
          )
    end

fun pp_mod s m =
    let
      val pp_d = pp_d s
      val pp_mod = pp_mod s
      val pp_sgn = pp_sgn s
      fun space () = PP.space s 1
      fun str v = PP.string s v
      fun strs s = (str s; space ())
      fun comma () = (str ","; space ())
      fun colon () = (str ":"; space ())
      fun pp_id x = str $ fst x
      fun open_hbox () = PP.openHBox s
      fun open_vbox () = PP.openVBox s (PP.Rel 2)
      fun open_vbox_noindent () = PP.openVBox s (PP.Rel 0)
      fun close_box () = PP.closeBox s
    in
      case m of
          ModComponents (ids, decls, _) =>
          (
            open_vbox_noindent ();
            open_hbox ();
            str "Mod";
            app (fn id => (comma (); pp_id id)) ids;
            close_box ();
            space ();
            app (fn d => (pp_d d; space ())) decls;
            str "End";
            close_box ()
          )
        | ModSeal (m, sgn) =>
          (
            open_vbox ();
            strs "ModSeal";
            pp_mod m;
            strs ":";
            pp_sgn sgn;
            close_box ()
          )
        | ModTransparentAsc (m, sgn) =>
          (
            open_vbox ();
            strs "ModTransAsc";
            pp_mod m;
            strs ":";
            pp_sgn sgn;
            close_box ()
          )
    end
      
fun pp_top_bind s top_bind =
    let
      val pp_t = pp_t s
      val pp_d = pp_d s
      val pp_mod = pp_mod s
      val pp_sgn = pp_sgn s
      fun space () = PP.space s 1
      fun str v = PP.string s v
      fun strs s = (str s; space ())
      fun comma () = (str ","; space ())
      fun colon () = (str ":"; space ())
      fun pp_id x = str $ fst x
      fun pp_long_id x = str $ str_long_id x
      fun open_hbox () = PP.openHBox s
      fun open_vbox () = PP.openVBox s (PP.Rel 2)
      fun open_vbox_noindent () = PP.openVBox s (PP.Rel 0)
      fun close_box () = PP.closeBox s
    in
      case top_bind of
          TBMod (name, m) =>
          (
            open_vbox ();
            open_hbox ();
            strs "TBMod";
            pp_id name;
            space ();
            str "=";
            close_box ();
            space ();
            pp_mod m;
            close_box ()
          )
        | TBFunctor (name1, (name2, sgn), m) =>
          (
            open_vbox ();
            open_hbox ();
            strs "TBFunctor";
            pp_id name1;
            space ();
            str "(";
            pp_id name1;
            strs ":";
            pp_sgn sgn;
            strs ")";
            str "=";
            close_box ();
            space ();
            pp_mod m;
            close_box ()
          )
        | TBFunctorApp (id1, id2, id3) =>
          (
            open_hbox ();
            strs "TBFunctorApp";
            str "(";
            pp_id id1;
            comma ();
            pp_id id2;
            comma ();
            pp_id id3;
            str ")";
            close_box ()
          )
        | TBState (name, t) =>
          (
            open_hbox ();
            strs "TBState";
            str "(";
            pp_id name;
            comma ();
            pp_t t;
            str ")";
            close_box ()
          )
        | TBPragma (name, s) =>
          (
            open_hbox ();
            strs "TBPragma";
            str "(";
            pp_id name;
            comma ();
            str s;
            str ")";
            close_box ()
          )
        | TBInterface (name, sgn) =>
          (
            open_vbox ();
            strs "TBInterface";
            pp_id name;
            space ();
            strs "=";
            pp_sgn sgn;
            close_box ()
          )
    end
      
fun pp_prog s prog =
  let
    val pp_top_bind = pp_top_bind s
    fun space () = PP.space s 1
    fun str v = PP.string s v
    fun strs s = (str s; space ())
    fun open_vbox_noindent () = PP.openVBox s (PP.Rel 0)
    fun close_box () = PP.closeBox s
  in
    open_vbox_noindent ();
    app (fn tb => (pp_top_bind tb; space ())) prog;
    close_box ()
  end

          
open WithPP
       
fun pp_prog_to s e = withPP ("", 80, s) (fn s => pp_prog s e)
fun pp_prog_to_stdout a = pp_prog_to TextIO.stdOut a
fun pp_prog_to_string e =
    pp_to_string "pp_prog_to_string.tmp" (fn os => pp_prog_to os e)
                 
end
