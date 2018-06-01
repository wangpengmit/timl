structure MicroTiMLLiveVars = struct

open Util
open Unbound
open Binders
open VisitorUtil
open EvalConstr
open MicroTiMLLongId
open MicroTiMLUtil
open MicroTiML
       
infixr 0 $

infix 6 @%-
val op@%- = ISetU.delete
         
fun live_vars_expr_visitor_vtable cast () =
  let
    val extend_i = extend_noop
    val extend_t = extend_noop
    val extend_c = extend_noop
    val extend_e = extend_noop
    val visit_cvar = visit_noop
    val visit_idx = visit_noop
    val visit_sort = visit_noop
    val visit_ty = visit_noop
    fun visit_ibinder this = visit_binder (#extend_i (cast this) this)
    fun visit_tbinder this = visit_binder (#extend_t (cast this) this)
    fun visit_ebinder this = visit_binder (#extend_e (cast this) this)
    fun visit_ibind this = visit_bind_simp (#extend_i (cast this) this)
    fun visit_tbind this = visit_bind_simp (#extend_t (cast this) this)
    fun visit_cbind this = visit_bind_simp (#extend_c (cast this) this)
    fun visit_ibind_anno this = visit_bind_anno (#extend_i (cast this) this)
    fun visit_tbind_anno this = visit_bind_anno (#extend_t (cast this) this)
    fun visit_cbind_anno this = visit_bind_anno (#extend_c (cast this) this)
                                                
    fun visit_ebind this f (env as (lvars, _)) bind =
      let
        val (name, b) = unBindSimp bind
        val () = unop_ref (ISet.map inc) lvars
        val b = f env b
        val () = unop_ref (fn s => ISet.map dec (s @%- 0)) lvars
      in
        BindSimp (name, b)
      end
    fun visit_ebind_anno this f_anno f (env as (lvars, _)) bind =
      let
        val ((name, anno), b) = unBindAnno bind
        val bind = visit_ebind this f env $ BindSimp (name, b)
        val (name, b) = unBindSimp bind
        val anno = f_anno env anno
      in
        BindAnno ((name, anno), b)
      end
                                                
    fun add_AnnoLiveVars (bind, n) =
      let
        val (name, e) = unBindSimp bind
      in
        BindSimp (name, EAnnoLiveVars (e, n))
      end
        
    (* has_k: a continuation variable will also be alive (which is invisible before CPS), so the number of live variables should be added by one *)
    fun num_lvars (lvars, has_k) = ISet.numItems (!lvars) + b2i has_k
                                                              
    fun visit_expr this env data =
      let
        val vtable = cast this
      in
        case data of
            EVar data => #visit_EVar vtable this env data
          | EConst data => #visit_EConst vtable this env data
          (* | ELoc data => #visit_ELoc vtable this env data *)
          | EUnOp data => #visit_EUnOp vtable this env data
          | EBinOp data => #visit_EBinOp vtable this env data
          | ETriOp data => #visit_ETriOp vtable this env data
          | ECase data => #visit_ECase vtable this env data
          | EAbs data => #visit_EAbs vtable this env data
          | ERec data => #visit_ERec vtable this env data
          | EAbsT data => #visit_EAbsT vtable this env data
          | EAppT data => #visit_EAppT vtable this env data
          | EAbsI data => #visit_EAbsI vtable this env data
          | EAppI data => #visit_EAppI vtable this env data
          | EPack data => #visit_EPack vtable this env data
          | EUnpack data => #visit_EUnpack vtable this env data
          | EPackI data => #visit_EPackI vtable this env data
          | EPackIs data => #visit_EPackIs vtable this env data
          | EUnpackI data => #visit_EUnpackI vtable this env data
          | EAscTime data => #visit_EAscTime vtable this env data
          | EAscSpace (e, i) => EAscSpace (#visit_expr vtable this env e, #visit_idx vtable this env i)
          | EAscState (e, i) => EAscState (#visit_expr vtable this env e, #visit_idx vtable this env i)
          | EAscType data => #visit_EAscType vtable this env data
          | ENever data => #visit_ENever vtable this env data
          | EBuiltin data => #visit_EBuiltin vtable this env data
          | ELet data => #visit_ELet vtable this env data
          | ELetIdx data => #visit_ELetIdx vtable this env data
          | ELetType data => #visit_ELetType vtable this env data
          | ELetConstr data => #visit_ELetConstr vtable this env data
          | EAbsConstr data => #visit_EAbsConstr vtable this env data
          | EAppConstr data => #visit_EAppConstr vtable this env data
          | EVarConstr data => #visit_EVarConstr vtable this env data
          | EMatchSum data => #visit_EMatchSum vtable this env data
          | EMatchPair data => #visit_EMatchPair vtable this env data
          | EMatchUnfold data => #visit_EMatchUnfold vtable this env data
          | EMallocPair data => #visit_EMallocPair vtable this env data
          | EPairAssign data => #visit_EPairAssign vtable this env data
          | EProjProtected data => #visit_EProjProtected vtable this env data
          | EHalt data => #visit_EHalt vtable this env data
          | ENewArrayValues (t, es) => ENewArrayValues (#visit_ty vtable this env t, mapr (#visit_expr vtable this env) es)
          | ETuple es => ETuple (mapr (#visit_expr vtable this env) es)
          | EIfi (e, bind1, bind2) =>
            let
              val lvars = fst env
              val n_lvars = num_lvars env
              val new_lvars = ref ISet.empty
              (* In the branches, there will be a live continuation variable. *)
              val bind1 = visit_ebind this (#visit_expr vtable this) (new_lvars, true) bind1
              val () = output_set lvars (!new_lvars)
              val () = new_lvars := ISet.empty
              val bind2 = visit_ebind this (#visit_expr vtable this) (new_lvars, true) bind2
              val () = output_set lvars (!new_lvars)
              val e = #visit_expr vtable this env e
            in
              EIfi (e, bind1, add_AnnoLiveVars (bind2, n_lvars))
            end
          | EState x => EState x
      end
    fun visit_ETriOp this env (opr, e1, e2, e3) =
      case opr of
          ETIte _ =>
          let
            val lvars = fst env
            val n_lvars = num_lvars env
            val vtable = cast this
            val new_lvars = ref ISet.empty
            (* In the branches, there will be a live continuation variable. *)
            val e2 = #visit_expr vtable this (new_lvars, true) e2
            val () = output_set lvars (!new_lvars)
            val () = new_lvars := ISet.empty
            val e3 = #visit_expr vtable this (new_lvars, true) e3
            val () = output_set lvars (!new_lvars)
            val e1 = #visit_expr vtable this env e1
          in
            ETriOp (opr, e1, e2, EAnnoLiveVars (e3, n_lvars))
          end
        | _ =>
          let
            val vtable = cast this
            val e3 = #visit_expr vtable this env e3
            val e2 = #visit_expr vtable this env e2
            val e1 = #visit_expr vtable this env e1
          in
            ETriOp (opr, e1, e2, e3)
          end
    fun visit_ECase this env (e, e1, e2) =
      let
        val lvars = fst env
        val n_lvars = num_lvars env
        val vtable = cast this
        val new_lvars = ref ISet.empty
        (* In the branches, there will be a live continuation variable. *)
        val e1 = visit_ebind this (#visit_expr vtable this) (new_lvars, true) e1
        val () = output_set lvars (!new_lvars)
        val () = new_lvars := ISet.empty
        val e2 = visit_ebind this (#visit_expr vtable this) (new_lvars, true) e2
        val () = output_set lvars (!new_lvars)
        val e = #visit_expr vtable this env e
      in
        ECase (e, e1, add_AnnoLiveVars (e2, n_lvars))
      end
    fun visit_var this (lvars, _) data =
      ((case data of
            ID (n, _) => output lvars n
          | QID _ => raise Impossible "live_evars/QID"
       );
       data)
    fun visit_EVar this env data =
      let
        val vtable = cast this
      in
        EVar $ #visit_var vtable this env data
      end
    fun visit_EConst this env data = EConst data
    fun visit_un_op this env opr = 
      let
        val vtable = cast this
        fun on_t x = #visit_ty vtable this env x
      in
        case opr of
            EUInj (opr, t) => EUInj (opr, on_t t)
          | EUFold t => EUFold $ on_t t
          | EUUnfold () => EUUnfold ()
          | EUTiML opr => EUTiML opr
          | EUTupleProj n => EUTupleProj n
      end
    fun visit_EUnOp this env data = 
      let
        val vtable = cast this
        val (opr, e) = data
        val opr = visit_un_op this env opr
        val e = #visit_expr vtable this env e
      in
        EUnOp (opr, e)
      end
    fun visit_EBinOp this env (opr, e1, e2) =
      case opr of
          EBApp _ =>
          let
            val n_lvars = num_lvars env
            val vtable = cast this
            val e2 = #visit_expr vtable this env e2
            val e1 = #visit_expr vtable this env e1
          in
            EBinOp (EBApp (), e1, EAnnoLiveVars (e2, n_lvars))
          end
        | _ =>
          let
            val vtable = cast this
            val e2 = #visit_expr vtable this env e2
            val e1 = #visit_expr vtable this env e1
          in
            EBinOp (opr, e1, e2)
          end
    fun visit_EAbs this (env as (lvars, _)) (i, bind) =
      let
        val vtable = cast this
        val i = #visit_idx vtable this env i
        val new_lvars = ref ISet.empty
        (* now there will be a live continuation variable *)
        val bind = visit_ebind_anno this (#visit_ty vtable this) (#visit_expr vtable this) (new_lvars, true) bind
        val () = output_set lvars (!new_lvars)
      in
        EAbs (i, bind)
      end
    fun visit_ERec this env data =
      let
        val vtable = cast this
        val data = visit_ebind_anno this (#visit_ty vtable this) (#visit_expr vtable this) env data
      in
        ERec data
      end
    fun visit_EAbsT this (lvars, _) data =
      let
        val vtable = cast this
        val new_lvars = ref ISet.empty
        (* now there will be a live continuation variable *)
        val data = visit_tbind_anno this (#visit_kind vtable this) (#visit_expr vtable this) (new_lvars, true) data
        val () = output_set lvars (!new_lvars)
      in
        EAbsT data
      end
    fun visit_EAppT this env (e, t) = 
      let
        val n_lvars = num_lvars env
        val vtable = cast this
        val t = #visit_ty vtable this env t
        val e = #visit_expr vtable this env e
      in
        EAppT (EAnnoLiveVars (e, n_lvars), t)
      end
    fun visit_EAbsI this (lvars, _) data =
      let
        val vtable = cast this
        val new_lvars = ref ISet.empty
        (* now there will be a live continuation variable *)
        val data = visit_ibind_anno this (#visit_sort vtable this) (#visit_expr vtable this) (new_lvars, true) data
        val () = output_set lvars (!new_lvars)
      in
        EAbsI data
      end
    fun visit_EAppI this env (e, i) = 
      let
        val n_lvars = num_lvars env
        val vtable = cast this
        val i = #visit_idx vtable this env i
        val e = #visit_expr vtable this env e
      in
        EAppI (EAnnoLiveVars (e, n_lvars), i)
      end
    fun visit_EPack this env data = 
      let
        val vtable = cast this
        val (t_all, t, e) = data
        val t_all = #visit_ty vtable this env t_all
        val t = #visit_ty vtable this env t
        val e = #visit_expr vtable this env e
      in
        EPack (t_all, t, e)
      end
    fun visit_EUnpack this env data =
      let
        val vtable = cast this
        val (e, bind) = data
        val bind = (visit_tbind this o visit_ebind this) (#visit_expr vtable this) env bind
        val e = #visit_expr vtable this env e
      in
        EUnpack (e, bind)
      end
    fun visit_EPackI this env data = 
      let
        val vtable = cast this
        val (t, i, e) = data
        val t = #visit_ty vtable this env t
        val i = #visit_idx vtable this env i
        val e = #visit_expr vtable this env e
      in
        EPackI (t, i, e)
      end
    fun visit_EPackIs this env data = 
      let
        val vtable = cast this
        val (t, is, e) = data
        val t = #visit_ty vtable this env t
        val is = map (#visit_idx vtable this env) is
        val e = #visit_expr vtable this env e
      in
        EPackIs (t, is, e)
      end
    fun visit_EUnpackI this env data =
      let
        val vtable = cast this
        val (e, bind) = data
        val bind = (visit_ibind this o visit_ebind this) (#visit_expr vtable this) env bind
        val e = #visit_expr vtable this env e
      in
        EUnpackI (e, bind)
      end
    fun visit_EAscTime this env data = 
      let
        val vtable = cast this
        val (e, i) = data
        val e = #visit_expr vtable this env e
        val i = #visit_idx vtable this env i
      in
        EAscTime (e, i)
      end
    fun visit_EAscType this env data = 
      let
        val vtable = cast this
        val (e, t) = data
        val e = #visit_expr vtable this env e
        val t = #visit_ty vtable this env t
      in
        EAscType (e, t)
      end
    fun visit_ENever this env data = 
      let
        val vtable = cast this
        val data = #visit_ty vtable this env data
      in
        ENever data
      end
    fun visit_EBuiltin this env (name, t) = 
      let
        val vtable = cast this
        val t = #visit_ty vtable this env t
      in
        EBuiltin (name, t)
      end
    fun visit_ELet this env data =
      let
        val vtable = cast this
        val (e, bind) = data
        val bind = visit_ebind this (#visit_expr vtable this) env bind
        val e = #visit_expr vtable this env e
      in
        ELet (e, bind)
      end
    fun visit_ELetIdx this env (i, bind) =
      let
        val (_, e) = unBindSimp bind
      in
        #visit_expr (cast this) this env $ subst0_i_e i e
      end
    fun visit_ELetType this env (t, bind) =
      let
        val (_, e) = unBindSimp bind
      in
        #visit_expr (cast this) this env $ subst0_t_e t e
      end
    fun visit_ELetConstr this env (e1, bind) =
      let
        val (_, e2) = unBindSimp bind
        val e = subst0_c_e e1 e2
        val e = eval_constr e
      in
        #visit_expr (cast this) this env e
      end
    fun visit_EHalt this env (e, t) =
      let
        val vtable = cast this
        val e = #visit_expr vtable this env e
        val t = #visit_ty vtable this env t
      in
        EHalt (e, t)
      end
    fun visit_EMallocPair this env (a, b) =
      let
        val vtable = cast this
        val b = #visit_expr vtable this env b
        val a = #visit_expr vtable this env a
      in
        EMallocPair (a, b)
      end
    fun visit_EPairAssign this env (e1, proj, e2) =
      let
        val vtable = cast this
        val e2 = #visit_expr vtable this env e2
        val e1 = #visit_expr vtable this env e1
      in
        EPairAssign (e1, proj, e2)
      end
    fun visit_EProjProtected this env (proj, e) =
      let
        val vtable = cast this
        val e = #visit_expr vtable this env e
      in
        EProjProtected (proj, e)
      end
    fun err name = raise Impossible $ "live_vars/" ^ name
    fun visit_EMatchSum this env data = err "EMatchSum"
    fun visit_EMatchPair this env data = err "EMatchPair"
    fun visit_EMatchUnfold this env data = err "EMatchUnfold"
    fun visit_EVarConstr this env data = err "EVarConstr"
    fun visit_EAbsConstr this env data = err "EAbsConstr"
    fun visit_EAppConstr this env data = err "EAppConstr"
  in
    {
      visit_expr = visit_expr,
      visit_EVar = visit_EVar,
      visit_EConst = visit_EConst,
      visit_EUnOp = visit_EUnOp,
      visit_EBinOp = visit_EBinOp,
      visit_ETriOp = visit_ETriOp,
      visit_ECase = visit_ECase,
      visit_EAbs = visit_EAbs,
      visit_ERec = visit_ERec,
      visit_EAbsT = visit_EAbsT,
      visit_EAppT = visit_EAppT,
      visit_EAbsI = visit_EAbsI,
      visit_EAppI = visit_EAppI,
      visit_EPack = visit_EPack,
      visit_EUnpack = visit_EUnpack,
      visit_EPackI = visit_EPackI,
      visit_EPackIs = visit_EPackIs,
      visit_EUnpackI = visit_EUnpackI,
      visit_EAscTime = visit_EAscTime,
      visit_EAscType = visit_EAscType,
      visit_ENever = visit_ENever,
      visit_EBuiltin = visit_EBuiltin,
      visit_ELet = visit_ELet,
      visit_ELetIdx = visit_ELetIdx,
      visit_ELetType = visit_ELetType,
      visit_ELetConstr = visit_ELetConstr,
      visit_EAbsConstr = visit_EAbsConstr,
      visit_EAppConstr = visit_EAppConstr,
      visit_EVarConstr = visit_EVarConstr,
      visit_EMatchSum = visit_EMatchSum,
      visit_EMatchPair = visit_EMatchPair,
      visit_EMatchUnfold = visit_EMatchUnfold,
      visit_EMallocPair = visit_EMallocPair,
      visit_EPairAssign = visit_EPairAssign,
      visit_EProjProtected = visit_EProjProtected,
      visit_EHalt = visit_EHalt,
      visit_var = visit_var,
      visit_cvar = visit_cvar,
      visit_idx = visit_idx,
      visit_sort = visit_sort,
      visit_kind = visit_noop,
      visit_ty = visit_ty,
      extend_i = extend_i,
      extend_t = extend_t,
      extend_c = extend_c,
      extend_e = extend_e
    }
  end

fun new_live_vars_expr_visitor params = new_expr_visitor live_vars_expr_visitor_vtable params
fun live_vars b =
  let
    val lvars = ref ISet.empty
    val visitor as (ExprVisitor vtable) = new_live_vars_expr_visitor ()
    val b = #visit_expr vtable visitor (lvars, false) b
  in
    (b, !lvars)
  end
    
end
