functor ToStringRawFn (structure Expr : IDX_TYPE_EXPR
                                          where type Idx.base_sort = BaseSorts.base_sort
                                            and type Type.base_type = BaseTypes.base_type
                       sharing type Expr.Type.basic_sort = Expr.Idx.basic_sort
                       val str_raw_var : Expr.var -> string
                       val str_uvar_i : ('basic_sort -> string) * ('idx -> string) -> ('basic_sort, 'idx) Expr.Idx.uvar_i -> string
                       val str_uvar_mt : ('sort -> string) * ('kind -> string) * ('mtype -> string) -> ('sort, 'kind, 'mtype) Expr.Type.uvar_mt -> string
                      ) = struct

open Expr
open Idx
open Type
open Util
open BaseSorts
open BaseTypes
open Operators
open Bind
       
infixr 0 $
         
fun str_raw_option f a = case a of SOME a => sprintf "SOME ($)" [f a] | NONE => "NONE"

fun str_raw_name (s, _) = s

fun str_raw_bind f (Bind (_, a)) = sprintf "Bind ($)" [f a]

fun str_raw_bs b =
  case b of
      BSBase s => (* sprintf "BSBase ($)" [ *)str_b s(* ] *)
    | BSArrow (s1, s2) => sprintf "BSArrow ($, $)" [str_raw_bs s1, str_raw_bs s2]
    | BSUVar u => "BSUVar"

fun str_raw_i i =
  case i of
      IVar (x, _) => sprintf "IVar ($)" [str_raw_var x]
    | IConst (c, _) => sprintf "IConst ($)" [str_idx_const c]
    | IUnOp (opr, i, _) => sprintf "IUnOp ($, $)" [str_idx_un_op opr, str_raw_i i]
    | IBinOp (opr, i1, i2) => sprintf "IBinOp ($, $, $)" [str_idx_bin_op opr, str_raw_i i1, str_raw_i i2]
    | IIte (i1, i2, i3, _) => sprintf "IIte ($, $, $)" [str_raw_i i1, str_raw_i i2, str_raw_i i3]
    | IAbs (b, bind, _) => sprintf "IAbs ($, $)" [str_raw_bs b, str_raw_bind str_raw_i bind]
    | IUVar (u, _) => str_uvar_i (str_raw_bs, str_raw_i) u
    | IState st => sprintf "IState $" [StMapU.str_map (id, str_raw_i) st]

fun str_raw_s s =
  case s of
      SBasic (b, _) => sprintf "SBasic ($)" [str_raw_bs b]
    | _ => "<sort>"
                    
fun str_raw_k k = "<kind>"

fun str_raw_state st = StMapU.str_map (id, str_raw_i) st
                                      
fun str_raw_mt (t : mtype) : string =
  case t of
      TArrow ((st1, t1), (j, i), (st2, t2)) => sprintf "TArrow ($, $, $, $, $)" [str_raw_state st1, str_raw_mt t1, str_raw_i j, str_raw_i i, str_raw_state st2, str_raw_mt t2]
    | TNat (i, _) => sprintf "TNat ($))" [str_raw_i i]
    | TiBool (i, _) => sprintf "TiBool ($))" [str_raw_i i]
    | TArray (t, i) => sprintf "TArray ($, $)" [str_raw_mt t, str_raw_i i]
    | TUnit _ => "TUnit"
    (* | TProd (t1, t2) => sprintf "TProd ($, $)" [str_raw_mt t1, str_raw_mt t2] *)
    | TUniI (s, bind, _) => sprintf "TUniI ($, $)" ["<sort>", str_raw_bind (fn ((i, j), t) => sprintf "$, $, $" [str_raw_i i, str_raw_i j, str_raw_mt t]) bind]
    | TVar x => sprintf "TVar ($)" [str_raw_var x]
    | TApp (t1, t2) => sprintf "TApp ($, $)" [str_raw_mt t1, str_raw_mt t2]
    | TAbs (k, bind, _) => sprintf "TAbs ($, $)" ["<kind>", str_raw_bind str_raw_mt bind]
    | TAppI (t, i) => sprintf "TAppI ($, $)" [str_raw_mt t, str_raw_i i]
    | TAbsI (s, bind, _) => sprintf "TAbsI ($, $)" ["<sort>", str_raw_bind str_raw_mt bind]
    | TBase (bt, _) => sprintf "TBase ($)" [str_bt bt]
    | TUVar (u, _) => sprintf "TUVar ($)" [str_uvar_mt (str_raw_bs, str_raw_k, str_raw_mt) u]
    | TDatatype (Bind (name, tbinds), _) =>
      let
        fun str_raw_name name = "<name>"
        val (tname_kinds, (basic_sorts, constr_decls)) = unfold_binds tbinds
        val tnames = map (str_raw_name o fst) tname_kinds
        val tnames = join_prefix " " tnames
        val basic_sorts = map str_raw_bs basic_sorts
        val basic_sorts = if null basic_sorts then ""
                     else surround " {" "}" $ join " " basic_sorts
        fun str_raw_constr_decl family_name tnames (name, core, _) =
          let
            val (iname_sorts, (t, is)) = unfold_binds core
            val iname_sorts = join_prefix " " $ map (fn (name, s) => sprintf "{$ : $}" [str_raw_name name, str_raw_s s]) iname_sorts
            val t = str_raw_mt t
            val is = join_prefix " " $ map (surround "{" "}" o str_raw_i) is
          in
            sprintf "$$ of $ -> $$$" [str_raw_name name, iname_sorts, t, family_name, tnames, is]
          end
        val constr_decls = join " | " $ map (str_raw_constr_decl (str_raw_name name) tnames) constr_decls
      in
        sprintf "(datatype $$$ = $)" [str_raw_name name, tnames, basic_sorts, constr_decls]
      end
    (* | TSumbool (s1, s2) => sprintf "TSumbool ($, $)" [str_raw_s s1, str_raw_s s2] *)
    | TRecord (fields, _) => sprintf "(TRecord $)" [SMapU.str_map (id, str_raw_mt) fields]
    | TState (x, _) => sprintf "TState $" [x]
    | TMap t => sprintf "TMap ($)" [str_raw_mt t]
    | TVector t => sprintf "TVector ($)" [str_raw_mt t]
    | TSCell t => sprintf "(TSCell $)" [str_raw_mt t]
    | TNatCell r => "TNatCell"
    | TPtr t => sprintf "TPtr ($)" [str_raw_mt t]

fun str_raw_t (t : ty) : string =
  case t of
      PTMono t => str_raw_mt t
    | PTUni ((i, j), t, _) => sprintf "PTUni ($, $, $)" [str_raw_i i, str_raw_i j, str_raw_bind str_raw_t t]

(* fun str_raw_e e = *)
(*   case e of *)
(*       EAppConstr _ => "EAppConstr (...)" *)
(*     | EVar _ => "EVar (...)" *)
(*     | EConst _ => "EConst (...)" *)
(*     | EState (x, _) => sprintf "EState $" [x] *)
(*     | EUnOp _ => "EUnOp (...)" *)
(*     | EBinOp _ => "EBinOp (...)" *)
(*     | ETriOp _ => "ETriOp (...)" *)
(*     | EEI (opr, e, i) => sprintf "EEI ($, $, $)" [str_expr_EI opr, str_raw_e e, str_raw_i i] *)
(*     | EET (opr, e, t) => sprintf "EET ($, $, $)" [str_expr_ET opr, str_raw_e e, str_raw_mt t] *)
(*     | ET (opr, t, r) => sprintf "ET ($, $)" [str_expr_T opr, str_raw_mt t] *)
(*     | ENewArrayValues (t, es, _) => sprintf "ENewArrayValues [$] ($)" [str_raw_mt t, join ", " $ map str_raw_e es] *)
(*     | EAbs _ => "EAbs (...)" *)
(*     | EAbsI _ => "EAbsI (...)" *)
(*     | ECase _ => "ECase (...)" *)
(*     | ECaseSumbool _ => "ECaseSumbool (...)" *)
(*     | EIfi _ => "EIfi (...)" *)
(*     | ELet _ => "ELet (...)" *)
(*     | ESetModify _ => "ESetModify (...)" *)
(*     | EGet _ => "EGet (...)" *)

end
