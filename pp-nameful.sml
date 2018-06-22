(***************** pretty printers  **********************)    

functor PPNamefulFn (structure Expr : IDX_TYPE_EXPR
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
                         val pp_uvar_mt : ('sort -> string) * ('kind -> string) * ('mtype -> unit) * (string -> unit) -> ('sort, 'kind, 'mtype) Expr.Type.uvar_mt -> unit
                         val str_ptrn_constr_tag : Expr.ptrn_constr_tag -> string
                        ) = struct

open Expr
open Idx
open Type
open Region
open BaseSorts
open BaseTypes
open Operators
open Pattern

structure IdxUtil = IdxUtilFn (Idx)
open IdxUtil
structure TypeUtil = TypeUtilFn (Type)
open TypeUtil
structure ExprUtil = ExprUtilFn (Expr)
open ExprUtil
       
open Bind
       
infixr 0 $

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
          TArrow ((st1, t1), (i, j), (st2, t2)) =>
          (
            open_hbox ();
            str "TArrow";
            space ();
            str "(";
            pp_st st1;
            comma ();
            pp_t t1;
            comma ();
            str $ str_i i;
            comma ();
            str $ str_i j;
            comma ();
            pp_st st2;
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
            str $ fst name;
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
            str $ fst name;
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
            str $ fst name;
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
            pp_uvar_mt (str_b, str_k, pp_t, str) u;
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
                    str $ fst name;
                    colon ();
                    app (fn (name, s) => (str $ fst name; colon (); str $ str_s s; comma ())) iname_sorts;
                    pp_t t;
                    comma ();
                    app (fn i => (str $ str_i i; comma ())) is;
                    str "]";
                    comma ()
                  )
                end
          in
            (
              open_hbox ();
              str "TDatatype";
              space ();
              str "(";
              str $ fst name;
              comma ();
              app (fn (name, ()) => (str $ fst name; comma ())) tname_kinds;
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

open Unbound
open Binders
      
fun get_bind b = mapFst binder2str $ unBind b
fun get_bind_anno b =
    let
      val ((name, anno), t) = unBindAnno b
    in
      (Name2str name, anno, t)
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
          PnConstr (Outer ((x, tag), eia), inames, pn, _) =>
          (
            open_hbox ();
            strs "PnConstr";
            str "(";
            str x;
            comma ();
            str $ str_ptrn_constr_tag tag;
            comma ();
            str $ str_bool eia;
            comma ();
            app (fn b => (str $ binder2str b; comma ())) inames;
            str "(";
            pp_pn pn;
            str ")";
            str ")";
            close_box ()
          )
        | PnVar name =>
          (
            open_hbox ();
            strs "PnConstr";
            str $ binder2str name;
            close_box ()
          )
        | PnPair (pn1, pn2) =>
          (
            open_hbox ();
            strs "PnPair";
            str "(";
            pp_pn pn1;
            comma ();
            pp_pn pn2;
            str ")";
            close_box ()
          )
        | PnTT _ => str "PnTT"
        | PnAlias (name, pn, _) =>
          (
            open_hbox ();
            strs "PnAlias";
            str "(";
            str $ binder2str name;
            comma ();
            pp_pn pn;
            str ")";
            close_box ()
          )
        | PnAnno (pn, Outer t) =>
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
          EVar (x, b) =>
          (
            open_hbox ();
            str "EVar";
            space ();
            str "(";
            str x;
            comma ();
            str $ str_bool b;
            str ")";
            close_box ()
          )
        | EConst (c, _) =>
          (
            open_hbox ();
            str "EConst";
            space ();
            str "(";
            str $ str_expr_const c;
            str ")";
            close_box ()
          )
        | EState (x, _) =>
          (
            open_hbox ();
            str "EState";
            space ();
            str "(";
            str x;
            str ")";
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
        | EEI (EEIAppI (), _, _) =>
          let
            val (e, is) = collect_EAppI e
          in
            (
              open_hbox ();
              str "EAppIs";
              space ();
              str "(";
              pp_e e;
              app (fn i => (comma (); str $ str_i i)) is;
              str ")";
              close_box ()
            )
          end
        | EEI (EEIAscTime (), e, i) =>
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
        | EEI (EEIAscSpace (), e, i) =>
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
        | EET (EETAppT (), e, t) =>
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
        | EET (EETAsc (), e, t) =>
          (
	    open_vbox_noindent ();
            open_hbox ();
            str "EAsc";
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
        | EET (EETHalt (), e, t) =>
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
        | ENewArrayValues (t, es, _) =>
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
        | ET (ETNever (), t, _) =>
          (
            open_hbox ();
            str "ENever";
            space ();
            str "(";
            pp_t t;
            str ")";
            close_box ()
          )
        | ET (ETBuiltin name, t, _) =>
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
        | EAbs (st, bind, spec) =>
          let
            val (pn, e) = unBind bind
          in
            open_vbox ();
            open_hbox ();
            str "EAbs";
            space ();
            str "(";
            pp_st st;
            comma ();
            pp_pn pn;
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
        | EAbsI _ =>
          let
            val (binds, e) = collect_EAbsI e
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
        | ELet (return, bind, _) => 
          let
            val (decls, e) = Unbound.unBind bind
          in
	    open_vbox_noindent ();
            open_hbox (); str "ELet"; space (); pp_return return; close_box (); space ();
            pp_decls decls;
            str "In"; space ();
            pp_e e; space ();
            str "End";
            close_box ()
          end
        | EAppConstr ((x, b), ts, is, e, _) =>
          (
            open_hbox ();
            str "EAppConstr";
            space ();
            str "(";
            str x;
            comma ();
            str $ str_bool b;
            comma ();
            app (fn t => (pp_t t; comma ())) ts;
            app (fn i => (str $ str_i i; comma ())) is;
            pp_e e;
            str ")";
            close_box ()
          )
        | ECase (e, return, rules, _) =>
          (
            open_vbox_noindent (); open_hbox (); str "ECase"; space (); pp_e e; comma (); pp_return return; close_box (); space ();
	    app
              (fn rule =>
                  let
                    val (pn, e) = unBind rule
                  in
                    (open_vbox ();
                     open_hbox (); str "|"; space (); pp_pn pn; space (); str "=>"; close_box (); space ();
                     pp_e e; close_box (); space ())
                  end) rules;
            close_box ()
          )
        | ECaseSumbool (e, bind1, bind2, _) =>
          let
            val (name1, e1) = get_bind bind1
            val (name2, e2) = get_bind bind2
          in
            open_vbox_noindent (); open_hbox (); str "ECaseSumbool"; space (); str "("; pp_e e; close_box (); comma ();
	    open_vbox (); str name1; str ":"; space ();
            pp_e e1; close_box (); comma ();
	    open_vbox (); str name2; str ":"; space ();
            pp_e e2; close_box (); str ")"; close_box ()
          end
        | EIfi (e, bind1, bind2, _) =>
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
        | ESetModify (is_modify, x, es, e, _) =>
          (
            open_hbox ();
            str "ESetModify";
            space ();
            str "(";
            str $ str_bool is_modify;
            comma ();
            str x;
            comma ();
            app (fn e => (pp_e e; comma ())) es;
            pp_e e;
            str ")";
            close_box ()
          )
        | EGet (x, es, _) =>
          (
            open_hbox ();
            str "EGet";
            space ();
            str "(";
            str x;
            comma ();
            app (fn e => (pp_e e; comma ())) es;
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
          DVal (name, Outer bind, _) =>
          let
            val (tnames, e) = Unbound.unBind bind
            val tnames = map (mapPair' binder2str unOuter) tnames
          in
            (
              open_hbox ();
              strs "DVal";
              strs $ binder2str name;
              app (fn (name, (i, j)) => (str "["; str name; colon (); str $ str_i i; comma (); str $ str_i j; str "]"; space ())) tnames;
              equal ();
              pp_e e;
              close_box ()
            )
          end
        | DValPtrn (pn, Outer e, _) =>
          (
            open_hbox ();
            strs "DValPtrn";
            pp_pn pn;
            space ();
            equal ();
            pp_e e;
            close_box ()
          )
        | DRec (name, bind, _) =>
          let
            val name = binder2str name
            val ((tnames, Rebind binds), ((pre_st, post_st), (t, (i, j)), e)) = Unbound.unBind $ unInner bind
            val binds = unTeles binds
            val tnames = map (mapPair' binder2str unOuter) tnames
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
          in
            (
              open_vbox ();
              open_hbox ();
              strs "DRec";
              strs name;
              app (fn (name, (i, j)) => (str "["; str name; colon (); str $ str_i i; comma (); str $ str_i j; str "]"; space ())) tnames;
              app (fn bind => (pp_bind bind; space ())) binds;
              comma ();
              pp_st pre_st;
              comma ();
              pp_st post_st;
              comma ();
              pp_t t;
              comma ();
              str $ str_i i;
              comma ();
              strs $ str_i j;
              equal ();
              close_box ();
              space ();
              pp_e e;
              close_box ()
            )
          end
        | DIdxDef (name, Outer s, Outer i) =>
          (
            open_hbox ();
            strs "DIdxDef";
            strs $ binder2str name;
            Option.app (fn s => (strs ":";
                                 strs $ str_s s)) s;
            strs "=";
            str $ str_i i;
            close_box ()
          )
        | DConstrDef (name, Outer x) =>
          (
            open_hbox ();
            strs "DConstrDef";
            strs $ binder2str name;
            strs "=";
            str x;
            close_box ()
          )
        | DAbsIdx2 (name, Outer s, Outer i) =>
          (
            open_hbox ();
            strs "DAbsIdx2";
            str $ binder2str name;
            strs ":";
            strs $ str_s s;
            strs "=";
            str $ str_i i;
            close_box ()
          )
        | DAbsIdx ((name, Outer s, Outer i), Rebind decls, _) =>
          let
            val name = binder2str name
            val decls = unTeles decls
          in
            (
              open_hbox ();
              strs "DAbsIdx";
              str name;
              strs ":";
              strs $ str_s s;
              strs "=";
              strs $ str_i i;
              close_box ();
              strs "With";
              app (fn d => (pp_d d; space ())) decls;
              str "End"
            )
          end
        | DTypeDef (name, Outer t) =>
          (
            open_hbox ();
            strs "DTypeDef";
            strs $ binder2str name;
            strs "=";
            pp_t t;
            close_box ()
          )
        | DOpen (m, ctx) =>
          (
            open_hbox ();
            strs "DOpen";
            strs $ unInner m;
            space ();
            Option.app (fn (a, b, c, d) =>
                           let
                             fun f ls = (pp_list_bracket (str o binder2str) ls; comma ())
                           in
                             (f a; f b; f c; f d)
                           end) ctx;
            close_box ()
          )
    end
      
and pp_decls params s decls =
  let
    val decls = unTeles decls
    val pp_d = pp_d params s
    fun space () = PP.space s 1
    fun open_vbox_noindent () = PP.openVBox s (PP.Rel 0)
    fun close_box () = PP.closeBox s
  in
    open_vbox_noindent ();
    app (fn d => (pp_d d; space ())) decls;
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
                 
end
