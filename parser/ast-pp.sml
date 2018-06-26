(***************** pretty printers  **********************)    

structure AstPP = struct

open Expr
open Idx
open Type
open Region
open BaseSorts
open BaseTypes
open Operators
open Pattern

infixr 0 $

fun pp_i s i =
    let
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
       | IAbs (is, i, _) =>
         (
           open_hbox ();
           str "IAbs";
           space ();
           str "(";
           app (fn i => (pp_i i; comma ())) is;
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
    in
      case p of
	  PConst s => str s
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
      
fun pp_s s sort =
    let
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
      
fun pp_st str_i s st =
    let
      fun str v = PP.string s v
      fun space () = PP.space s 1
      fun comma () = (str ","; space ())
      fun colon () = (str ":"; space ())
      fun open_hbox () = PP.openHBox s
      fun close_box () = PP.closeBox s
    in
      (
        open_hbox ();
        str "{";
        StMap.appi (fn (k, i) => (str k; colon (); str $ str_i i; comma ())) st;
        str "}";
        close_box ()
      )
    end
         
fun pp_t (params as (str_b, str_i : idx -> string, str_s, str_k : kind -> string)) s t =
    let
      val pp_t = pp_t params s
      val pp_st = pp_st str_i s
      fun space () = PP.space s 1
      fun add_space a = (space (); a)
      fun str v = PP.string s v
      fun comma () = (str ","; space ())
      fun colon () = (str ":"; space ())
      fun open_hbox () = PP.openHBox s
      (* fun open_vbox () = PP.openVBox s (PP.Abs 2) *)
      fun open_vbox () = PP.openVBox s (PP.Rel 2)
      fun close_box () = PP.closeBox s
    in
      case t of
	 TVar x => pp_long_id x
       | TArrow ((st1, t1), (i, j), (st2, t2)) =>
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
    end

fun pp_pn (params as pp_t) s pn =
    let
      val pp_pn = pp_pn params s
      val pp_t = pp_t s
      fun space () = PP.space s 1
      fun str v = PP.string s v
      fun strs s = (str s; space ())
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

fun pp_bind bind =
    case bind of
        SortingST (name, Outer s) =>
        (
          open_hbox ();
          str "{";
          str $ binder2str name;
          colon ();
          str $ str_s s;
          str "}";
          close_box ()
        )
      | TypingST pn =>
        (
          open_hbox ();
          str "(";
          pp_pn pn;
          str ")";
          close_box ()
        )
          
fun pp_datatype (name, tnames, binds, basic_sorts, constr_decls, _) =
    let
      fun str_constr_decl (name, binds, core, _) =
          (
            comma ();
            str "[";
            pp_id name;
            colon ();
            app (fn bind => (pp_sort_bind bind; comma ())) binds;
            Option.app (fn (t1, t2) => (pp_t t1; comma (), Option.app pp_t t2)) core;
            str "]"
          )
    in
      (
        open_hbox ();
        str $ fst name;
        app (fn name => (comma (); pp_id name)) tnames;
        app (fn b => (comma (); pp_bsort_bind b)) binds;
        app (fn b => (comma (); pp_bsort b)) basic_sorts;
        app str_constr_decl constr_decls;
        close_box ()
      )
    end
            
fun pp_e (params as (str_i, str_s, pp_t, pp_pn)) s e =
    let
      val pp_e = pp_e params s
      val pp_decls = pp_decls params s
      val pp_t = pp_t s
      val pp_pn = pp_pn s
      val pp_st = pp_st str_i s
      fun space () = PP.space s 1
      fun add_space a = (space (); a)
      fun str v = PP.string s v
      fun strs s = (str s; space ())
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
      fun pp_return (t, i, j) =
          (Option.app pp_t; comma ();
           Option.app (str o str_i) i; comma ();
           Option.app (str o str_i) j)
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
            str $ str_expr_un_op opr;
            comma ();
            pp_e e;
            str ")";
            close_box ()
          )
        | EBinOp (opr, e1, e2) =>
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
        | ETriOp (ETTiML (ETIte ()), e, e1, e2) =>
          (
            open_vbox (); open_hbox (); str "ETIte"; space (); str "("; pp_e e; close_box (); comma ();
    	    open_vbox_noindent (); pp_e e1; comma ();
            space ();
            pp_e e2; close_box (); str ")"; close_box ()
          )
        | ETriOp (opr, e1, e2, e3) =>
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
        | ESetModify (b, (x, es), e, _) =>
          (
            open_hbox ();
            str "ESetModify";
            space ();
            str "(";
            pp_bool b;
            comma ();
            pp_id x;
            comma ();
            pp_list_bracket pp_e es;
            comma ();
            pp_e e;
            str ")";
            close_box ()
          )
        | EGet ((x, es), _) =>
          (
            open_hbox ();
            str "EGet";
            space ();
            str "(";
            pp_id x;
            comma ();
            pp_list_bracket pp_e es;
            str ")";
            close_box ()
          )
        | EField (e, name, _) =>
          (
            open_hbox ();
            str "EField";
            space ();
            str "(";
            pp_e e;
            comma ();
            pp_id name;
            str ")";
            close_box ()
          )
    end

and pp_d (params as (str_i, str_s, pp_t, pp_pn)) s d =
    let
      val pp_d = pp_d params s
      val pp_e = pp_e params s
      val pp_t = pp_t s
      val pp_pn = pp_pn s
      val pp_st = pp_st str_i s
      fun space () = PP.space s 1
      fun str v = PP.string s v
      fun strs s = (str s; space ())
      fun comma () = (str ","; space ())
      fun colon () = (str ":"; space ())
      fun open_hbox () = PP.openHBox s
      fun open_vbox () = PP.openVBox s (PP.Rel 2)
      fun close_box () = PP.closeBox s
      fun equal () = (str "="; space ())
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
      case d of
          DVal (names, pn, e, _) =>
          (
            open_hbox ();
            strs "DVal";
            app (fn name => (pn_id name; space ())) names;
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
            strs name;
            app (fn name => (str "["; str name; str "]"; space ())) tnames;
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
            Option.app (fn s => (strs ":"; pp_sort s)) s; space ();
            strs "=";
            pp_i i;
            close_box ()
          )
        | DAbsIdx2 (name, s, i) =>
          (
            open_hbox ();
            strs "DAbsIdx2";
            pp_id name;
            Option.app (fn s => (strs ":"; pp_sort s)) s; space ();
            strs "=";
            pp_i i;
            close_box ()
          )
        | DAbsIdx (name, s, i, decls, _) =>
          (
            open_hbox ();
            strs "DAbsIdx";
            str name;
            Option.app (fn s => (strs ":"; pp_sort s)) s; space ();
            strs "=";
            Option.app (fn s => (space (); pp_i i)) i; 
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
        | DState (name, t) =>
          (
            open_hbox ();
            strs "DState";
            pp_id name;
            space ();
            pp_t t;
            close_box ()
          )
    end
      
and pp_decls s decls =
  let
    val pp_d = pp_d params s
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
            pp_sort s;
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
    end
      
fun pp_sgn s sgn =
    let
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

fun pp_mod s mod =
    let
    in
      case mod of
          ModComponents (decls, _) =>
          (
            open_vbox_noindent ();
            strs "Mod";
            app (fn d => (pp_d d; space ())) decls;
            str "End";
            close_box ()
          )
        | ModSeal (mod, sgn) =>
          (
            open_vbox ();
            strs "ModSeal";
            pp_mod mod;
            strs ":";
            pp_sgn sgn;
            close_box ()
          )
        | ModTransparentAsc (mod, sgn) =>
          (
            open_vbox ();
            strs "ModTransAsc";
            pp_mod mod;
            strs ":";
            pp_sgn sgn;
            close_box ()
          )
    end
      
fun pp_top_bind s top_bind =
    let
    in
      case top_bind of
          TBMod (name, mod) =>
          (
            open_vbox ();
            strs "TBMod";
            pp_id name;
            space ();
            strs "=";
            pp_mod mod;
            close_box ()
          )
        | TBFunctor (name1, (name2, sgn), mod) =>
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
            pp_mod mod;
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

and pp_prog s prog =
  let
  in
    open_vbox_noindent ();
    app (fn tb => (pp_top_bind tb; space ())) prog;
    close_box ()
  end

          
open WithPP
       
fun pp_t_fn params t = withPP ("", 80, TextIO.stdOut) (fn s => pp_t params s t)
val pp_t_to_fn = pp_t
fun pp_t_to_os_fn params os t = withPP ("", 80, os) (fn s => pp_t params s t)
fun pp_t_to_string_fn params t =
    pp_to_string "pp_t_to_string.tmp" (fn os => pp_t_to_os_fn params os t)
                              
fun pp_e_to_fn params s e = withPP ("", 80, s) (fn s => pp_e params s e)
fun pp_e_fn params = pp_e_to_fn params TextIO.stdOut
fun pp_e_to_string_fn params e =
    pp_to_string "pp_e_to_string.tmp" (fn os => pp_e_to_fn params os e)
                 
fun pp_d_to_fn params s e = withPP ("", 80, s) (fn s => pp_d params s e)
fun pp_d_fn params = pp_d_to_fn params TextIO.stdOut
fun pp_d_to_string_fn params e =
    pp_to_string "pp_d_to_string.tmp" (fn os => pp_d_to_fn params os e)
                 
fun pp_decls_to_fn params s e = withPP ("", 80, s) (fn s => pp_decls params s e)
fun pp_decls_fn params = pp_decls_to_fn params TextIO.stdOut
fun pp_decls_to_string_fn params e =
    pp_to_string "pp_decls_to_string.tmp" (fn os => pp_decls_to_fn params os e)
                 
open Unbound
open Binders
      
fun get_bind b = mapFst binder2str $ unBind b
fun get_bind_anno b =
    let
      val ((name, anno), t) = unBindAnno b
    in
      (Name2str name, anno, t)
    end

end
