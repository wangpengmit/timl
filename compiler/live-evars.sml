structure LiveEVars = struct

fun live_evars_expr_visitor_vtable cast () =
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
                                                
    fun visit_ebind this f env bind =
      let
        val (name, b) = unBindSimp bind
        val () = unop_ref (fn s => ISet.map add s) env
        val b = f env b
        val () = unop_ref (fn s => ISet.map dec (s @%- 0)) env
      in
        EBind (name, b)
      end
    fun visit_ebind_anno this f_anno f env bind =
      let
        val ((name, anno), b) = unBindAnno bind
        val bind = visit_ebind this f env $ EBind (name, b)
        val (name, b) = unBindSimp bind
        val anno = f env anno
      in
        EBindAnno ((name, anno), b)
      end
                                                
    fun output env n = push_ref env n
    fun output_set env s = ISet.app (push_ref env) s
                                    
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
          | EIfi (e, bind1, bind2, _) =>
            let
              val n_lvars = ISet.numItems (!env)
              val new_env = ref ISet.empty
              val bind1 = visit_ebind this (#visit_expr vtable this) new_env bind1
              val () = output_set env (!new_env)
              val () = new_env := ISet.empty
              val bind2 = visit_ebind this (#visit_expr vtable this) new_env bind2
              val () = output_set env (!new_env)
              val e = #visit_expr vtable this env e
            in
              EIfi (e, bind1, bind2, n_lvars)
            end
          | EState x => EState x
      end
    fun visit_ETriOp this env (opr, e1, e2, e3) =
      case opr of
          ETIte _ =>
          let
            val n_lvars = ISet.numItems (!env)
            val vtable = cast this
            val new_env = ref ISet.empty
            val e1 = #visit_expr vtable this new_env e1
            val () = output_set env (!new_env)
            val () = new_env := ISet.empty
            val e2 = #visit_expr vtable this new_env e2
            val () = output_set env (!new_env)
            val e = #visit_expr vtable this env e
          in
            ETriOp (ETIte n_lvars, e, e1, e2)
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
    fun visit_ECase this env (e, e1, e2, _) =
      let
        val n_lvars = ISet.numItems (!env)
        val vtable = cast this
        val new_env = ref ISet.empty
        val e1 = visit_ebind this (#visit_expr vtable this) new_env e1
        val () = output_set env (!new_env)
        val () = new_env := ISet.empty
        val e2 = visit_ebind this (#visit_expr vtable this) new_env e2
        val () = output_set env (!new_env)
        val e = #visit_expr vtable this env e
      in
        ECase (e, e1, e2, n_lvars)
      end
    fun visit_var this env data =
      ((case data of
            ID (n, _) => if n >= env then output env $ n - env
                         else ()
          | QID _ => raise Impossible "free_evars/QID");
       data)
    fun visit_EVar this env data =
      let
        val vtable = cast this
      in
        EVar $ #visit_var vtable this env data
      end
    fun visit_EVarConstr this env data =
      let
        val vtable = cast this
      in
        EVarConstr $ #visit_cvar vtable this env data
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
            val n_lvars = ISet.numItems (!env)
            val vtable = cast this
            val e2 = #visit_expr vtable this env e2
            val e1 = #visit_expr vtable this env e1
          in
            EBinOp (EBApp n_lvars, e1, e2)
          end
          _ =>
          let
            val vtable = cast this
            val e2 = #visit_expr vtable this env e2
            val e1 = #visit_expr vtable this env e1
          in
            EBinOp (opr, e1, e2)
          end
    fun visit_EAbs this env (i, bind) =
      let
        val vtable = cast this
        val i = #visit_idx vtable this env i
        val new_env = ref ISet.empty
        val bind = visit_ebind_anno this (#visit_ty vtable this) (#visit_expr vtable this) new_env bind
        val () = output_set env (!new_env)
      in
        EAbs (i, bind)
      end
    fun visit_EAbsConstr this env data =
      let
        val vtable = cast this
        val data = visit_bind (visit_triple (visit_list $ visit_tbinder this) (visit_list $ visit_ibinder this) (visit_ebinder this)) (#visit_expr vtable this) env data
      in
        EAbsConstr data
      end
    fun visit_ERec this env data =
      let
        val vtable = cast this
        val data = visit_ebind_anno this (#visit_ty vtable this) (#visit_expr vtable this) env data
      in
        ERec data
      end
    fun visit_EAbsT this env data =
      let
        val vtable = cast this
        val new_env = ref ISet.empty
        val data = visit_tbind_anno this (#visit_kind vtable this) (#visit_expr vtable this) new_env data
        val () = output_set env (!new_env)
      in
        EAbsT data
      end
    fun visit_EAppT this env (e, t, _) = 
      let
        val n_lvars = ISet.numItems (!env)
        val vtable = cast this
        val e = #visit_expr vtable this env e
        val t = #visit_ty vtable this env t
      in
        EAppT (e, t, n_lvars)
      end
    fun visit_EAbsI this env data =
      let
        val vtable = cast this
        val new_env = ref ISet.empty
        val data = visit_ibind_anno this (#visit_sort vtable this) (#visit_expr vtable this) env data
        val () = output_set env (!new_env)
      in
        EAbsI data
      end
    fun visit_EAppI this env (e, i, _) = 
      let
        val n_lvars = ISet.numItems (!env)
        val vtable = cast this
        val e = #visit_expr vtable this env e
        val i = #visit_idx vtable this env i
      in
        EAppI (e, i, n_lvars)
      end
    fun visit_EAppConstr this env data = 
      let
        val vtable = cast this
        val (e1, ts, is, e2) = data
        val e2 = #visit_expr vtable this env e2
        val e1 = #visit_expr vtable this env e1
        val ts = visit_list (#visit_ty vtable this) env ts
        val is = visit_list (#visit_idx vtable this) env is
      in
        EAppConstr (e1, ts, is, e2)
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
    fun visit_ELetIdx this env data =
      let
        val vtable = cast this
        val (i, bind) = data
        val i = #visit_idx vtable this env i
        val bind = visit_ibind this (#visit_expr vtable this) env bind
      in
        ELetIdx (i, bind)
      end
    fun visit_ELetType this env data =
      let
        val vtable = cast this
        val (t, bind) = data
        val t = #visit_ty vtable this env t
        val bind = visit_tbind this (#visit_expr vtable this) env bind
      in
        ELetType (t, bind)
      end
    fun visit_ELetConstr this env data =
      let
        val vtable = cast this
        val (e, bind) = data
        val bind = visit_cbind this (#visit_expr vtable this) env bind
        val e = #visit_expr vtable this env e
      in
        ELetConstr (e, bind)
      end
    fun visit_EMatchSum this env data =
      let
        val vtable = cast this
        val (e, branches) = data
        val e = #visit_expr vtable this env e
        val branches = (visit_list o visit_ebind this) (#visit_expr vtable this) env branches
      in
        EMatchSum (e, branches)
      end
    fun visit_EMatchPair this env data =
      let
        val vtable = cast this
        val (e, branch) = data
        val e = #visit_expr vtable this env e
        val branch = (visit_ebind this o visit_ebind this) (#visit_expr vtable this) env branch
      in
        EMatchPair (e, branch)
      end
    fun visit_EMatchUnfold this env data =
      let
        val vtable = cast this
        val (e, branch) = data
        val e = #visit_expr vtable this env e
        val branch = visit_ebind this (#visit_expr vtable this) env branch
      in
        EMatchUnfold (e, branch)
      end
    fun visit_EMallocPair this env (a, b) =
      let
        val vtable = cast this
        val a = #visit_expr vtable this env a
        val b = #visit_expr vtable this env b
      in
        EMallocPair (a, b)
      end
    fun visit_EPairAssign this env (e1, proj, e2) =
      let
        val vtable = cast this
        val e1 = #visit_expr vtable this env e1
        val e2 = #visit_expr vtable this env e2
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
    fun visit_EHalt this env (e, t) =
      let
        val vtable = cast this
        val e = #visit_expr vtable this env e
        val t = #visit_ty vtable this env t
      in
        EHalt (e, t)
      end
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

fun new_live_evars_expr_visitor params = new_expr_visitor live_evars_expr_visitor_vtable params
fun live_evars b =
  let
    val env = ref []
    val visitor as (ExprVisitor vtable) = new_live_evars_expr_visitor ()
    val b = #visit_expr vtable visitor env b
  in
    (b, !env)
  end
    
end
