structure LiveVars = struct

structure Visitor = ExprVisitorFn (structure S = UnderscoredExpr
                                   structure T = UnderscoredExpr)

open UnderscoredExprShift
open Visitor
open VisitorUtil
open Util
open LongId

infixr 0 $
                             
structure PV = PatternVisitor
structure Set = EVarSet
structure SetU = EVarSetU
       
(***************** the "count_binder" visitor  **********************)    
    
fun count_binder_expr_visitor_vtable cast () =
  let
    fun extend_i this (a, b, c, d) name = ((a+1, b, c, d), name)
    fun extend_t this (a, b, c, d) name = ((a, b+1, c, d), name)
    fun extend_c this (a, b, c, d) name = ((a, b, c+1, d), name)
    fun extend_e this (a, b, c, d) name = ((a, b, c, d+1), name)
  in
    default_expr_visitor_vtable
      cast
      extend_i
      extend_t
      extend_c
      extend_e
      visit_noop
      visit_noop
      visit_noop
      visit_noop
      visit_noop
      visit_noop
      visit_noop
      visit_noop
      visit_noop
  end

fun new_count_binder_expr_visitor params = new_expr_visitor count_binder_expr_visitor_vtable params
    
fun count_binder_decls b =
  let
    val visitor as (ExprVisitor vtable) = new_count_binder_expr_visitor ()
    val ctx = env2ctx (0, 0, 0, 0)
    val _ = visit_decls (#visit_decl vtable visitor) ctx b
  in
    !(#current ctx)
  end

(***************** the "live_vars" visitor  **********************)    

fun visit_decls visit_decl ctx decls =
  let
    val decls = unTeles decls
    val decls = List.concat $ mapr (visit_decl ctx) decls
  in
    Teles decls
  end
    
fun live_vars_expr_visitor_vtable cast () =
  let
    val extend_i = extend_noop
    val extend_t = extend_noop
    val extend_c = extend_noop
    val extend_e = extend_noop
    val visit_cvar = visit_noop
    val visit_mod_id = visit_noop
    val visit_idx = visit_noop
    val visit_sort = visit_noop
    val visit_mtype = visit_noop
    val visit_ty = visit_noop
    val visit_kind = visit_noop
    val visit_ptrn_constr_tag = visit_noop
    fun visit_ibind this = visit_bind_simp (#extend_i (cast this) this)
    fun visit_ibind_anno this = visit_bind_anno (#extend_i (cast this) this)
                                                
    (* has_cont_var: a continuation variable will also be alive (which is invisible before CPS), so the number of live variables should be added by one *)
    fun num_lvars (lvars, has_k, has_cont_var) = (Set.numItems (!lvars) + b2i has_cont_var, has_k)
    fun set_has_k (lvars, _, has_cont_var) = (lvars, true, has_cont_var)
    fun output lvars n = ((* println "output";  *)binop_ref (curry Set.add) lvars n)
    fun output_set lvars s = Set.app (output lvars) s
    fun add_AnnoLiveVars (bind, n, r) =
      let
        val (name, e) = unBindSimp bind
      in
        BindSimp (name, EAnnoLiveVars (e, n, r))
      end
                                                                
    fun long_id_to_var data =
      case data of
          ID (n, _) => inl n
        | QID ((m, _), (n, _)) => inr (m, n)
    fun shift n x =
      case x of
          inl x => inl $ x + n
        | inr _ => x
    fun forget n s = Set.map (fn x => case x of inl x => inl $ x - n | inr _ => x) $ Set.filter (fn inl x => x >= n | inr _ => true) s
    fun is_var_or_state e =
        let
          val f = is_var_or_state
        in
          case e of
              EVar (x, (_, false)) => SOME $ SOME $ long_id_to_var x
            | EState _ => SOME NONE
            | EEI (EEIAscTime (), e, _) => f e
            | EEI (EEIAscSpace (), e, _) => f e
            | EET (EETAsc (), e, _) => f e
            | _ => NONE
        end
    fun forget01_e_e a = forget_e_e 0 1 a
    fun visit_e2 this env (e1, e2) =
        let
          val vtable = cast this
          val lvars = #1 env
          val env = set_has_k env
        in
          case is_var_or_state e1 of
              NONE =>
              let
                val () = unop_ref (Set.map (shift 1)) lvars
                val () = unop_ref (curry Set.add' $ inl 0) lvars
                val e2 = shift_e_e e2
                val e2 = #visit_expr vtable this env e2
                val e2 = forget01_e_e e2
                val () = unop_ref (forget 1) lvars
                val e1 = #visit_expr vtable this env e1
              in
                (e1, e2)
              end
            | SOME x =>
              let
                val () = Option.app (fn x => unop_ref (fn s => Set.add (s, x)) lvars) x
                val e2 = #visit_expr vtable this env e2
                val e1 = #visit_expr vtable this env e1
              in
                (e1, e2)
              end
        end
    fun visit_es this env es =
        case es of
            [] => []
          | _ => 
        let
          val vtable = cast this
          (* delegate to visit_e2 *)
          val len = length es
          fun to_adds es = foldl_nonempty (fn (e, acc) => EIntAdd (e, acc)) $ rev es
          fun from_adds n e =
            if n <= 1 then [e]
            else
              case e of
                  EBinOp (EBPrim (EBPIntAdd ()), e1, e2) => e1 :: from_adds (n-1) e2
                | _ => raise Impossible "live-vars/visit_es()"
          val e = #visit_expr vtable this env $ to_adds es
        in
          from_adds len e
        end
    fun visit_es_left this env es =
        case es of
            [] => []
          | _ => 
        let
          val vtable = cast this
          (* delegate to visit_e2 *)
          val len = length es
          fun to_adds es = foldl_nonempty (fn (e, acc) => EIntAdd (acc, e)) $ es
          fun from_adds n e =
            if n <= 1 then [e]
            else
              case e of
                  EBinOp (EBPrim (EBPIntAdd ()), e1, e2) => e2 :: from_adds (n-1) e1
                | _ => raise Impossible "live-vars/visit_es()"
          val e = #visit_expr vtable this env $ to_adds es
        in
          rev $ from_adds len e
        end
    fun visit_e3 this env (e1, e2, e3) =
      case visit_es this env [e1, e2, e3] of
          [e1, e2, e3] => (e1, e2, e3)
        | _ => raise Impossible "live-vars/visit_e3()"
    (* fun visit_e3 this env (e1, e2, e3) = *)
    (*     let *)
    (*       val vtable = cast this *)
    (*       (* delegate to visit_e2 *) *)
    (*       val e = #visit_expr vtable this env (EIntAdd (e1, EIntAdd (e2, e3))) *)
    (*     in *)
    (*       case e of *)
    (*           EBinOp (EBPrim (EBPIntAdd ()), e1, (EBinOp (EBPrim (EBPIntAdd ()), e2, e3))) => *)
    (*           (e1, e2, e3) *)
    (*         | _ => raise Impossible "live-vars/visit_e3()" *)
    (*     end *)
    fun visit_expr this (env as (_, has_k, _)) data =
      let
        val vtable = cast this
        val ret = 
        case data of
	    EVar data => #visit_EVar vtable this env data
          | EConst data => #visit_EConst vtable this env data
          | EState data => EState data
          | EUnOp data => #visit_EUnOp vtable this env data
          | EBinOp data => #visit_EBinOp vtable this env data
	  | ETriOp data => #visit_ETriOp vtable this env data
          | EEI data => #visit_EEI vtable this env data
          | EET data => #visit_EET vtable this env data
          | ET data => #visit_ET vtable this env data
          | ENewArrayValues (t, es, r) => ENewArrayValues (#visit_mtype vtable this env t, visit_es this env es, r)
	  | EAbs data => #visit_EAbs vtable this env data
	  | EAbsI data => #visit_EAbsI vtable this env data
	  | EAppConstr data => #visit_EAppConstr vtable this env data
	  | ECase data => #visit_ECase vtable this env data
	  | ELet data => #visit_ELet vtable this env data
	  | ECaseSumbool data => #visit_ECaseSumbool vtable this env data
	  | EIfi (e, bind1, bind2, r) =>
            let
              val lvars = #1 env
              val n_lvars = num_lvars env
              val new_lvars = ref Set.empty
              (* In the branches, there will be a live continuation variable. *)
              val bind2 = visit_ibind this (#visit_expr vtable this) (new_lvars, false, true) bind2
              val () = output_set lvars (!new_lvars)
              val () = new_lvars := Set.empty
              val bind1 = visit_ibind this (#visit_expr vtable this) (new_lvars, false, true) bind1
              val () = output_set lvars (!new_lvars)
              val env = set_has_k env
              val e = #visit_expr vtable this env e
            in
              EIfi (e, bind1, add_AnnoLiveVars (bind2, n_lvars, r), r)
            end
          | ESetModify (b, x, es, e, r) =>
            if b then
              let
                val e = ESetModify (false, x, es, (EApp (e, EGet (x, es, r))), r)
                val e = #visit_expr vtable this env e
                val (es, e, e2) = case e of
                                      ESetModify (false, x, es, (EBinOp (EBApp (), e, e2)), r) =>
                                      (es, e, e2)
                                    | _ => raise Impossible "live-vars/ESetModify/1"
                val n_lvars = case e2 of
                                  EUnOp (EUAnno (EALiveVars n_lvars), _, _) => n_lvars
                                | _ => raise Impossible "live-vars/ESetModify/2"
              in
                ESetModify (b, x, es, EAnnoLiveVars (e, n_lvars, r), r)
              end
            else
              let
                val es = visit_es_left this env $ es @ [e]
                val (e, es) = assert_cons $ rev es
                val es = rev es
              in
                ESetModify (b, x, es, e, r)
              end
          | EGet (x, es, r) => EGet (x, visit_es this env es, r)
      in
        ret
      end
    fun visit_var this (lvars, _, _) data =
      (output lvars $ long_id_to_var data;
       data)
    fun visit_EVar this env data =
      let
        val n_lvars = num_lvars env
        val vtable = cast this
        val (var, eia) = data
        val var = #visit_var vtable this env var
      in
        EAnnoLiveVars (EVar (var, eia), n_lvars, dummy)
      end
    fun visit_EAppI this env (e, i) = 
      let
        val vtable = cast this
        val env = set_has_k env
        val i = #visit_idx vtable this env i
        val e = #visit_expr vtable this env e
      in
        EEI (EEIAppI (), e, i)
      end
    fun visit_EAppT this env (e, t) = 
      let
        val vtable = cast this
        val env = set_has_k env
        val t = #visit_mtype vtable this env t
        val e = #visit_expr vtable this env e
      in
        EET (EETAppT (), e, t)
      end
    fun visit_EConst this env data =
      let
        val vtable = cast this
      in
        EConst data
      end
    fun visit_EUnOp this env data =
      let
        val vtable = cast this
        val (opr, e, r) = data
        val env = set_has_k env
        val e = #visit_expr vtable this env e
      in
        EUnOp (opr, e, r)
      end
    fun visit_EBinOp this env (opr, e1, e2) =
      let
        val vtable = cast this
        val data = (e1, e2)
      in
        case opr of
            EBApp () => #visit_EApp vtable this env data
          | EBPair () => #visit_EPair vtable this env data
          | EBNew () => #visit_ENew vtable this env data
          | EBRead () => #visit_ERead vtable this env data
          | EBPrim (EBPIntAdd ()) => #visit_EAdd vtable this env data
          | EBNat (EBNAdd ()) => #visit_ENatAdd vtable this env data
          | _ =>
            let
              val (e1, e2) = visit_e2 this env (e1, e2)
            in
              EBinOp (opr, e1, e2)
            end
      end
    fun visit_EApp this env (e1, e2) =
      let
        (* val () = println $ "lvars = " ^ (SetU.str_set (str_sum str_int (str_pair (id, str_int))) (!(#1 env))) *)
        (* val () = println $ "has_cont_var = " ^ (str_bool (#3 env)) *)
        val n_lvars = num_lvars env
        (* val () = println $ "n_lvars = " ^ (str_int $ fst n_lvars) *)
        val vtable = cast this
        val (e1, e2) = visit_e2 this env (e1, e2)
      in
        EBinOp (EBApp (), e1, EAnnoLiveVars (e2, n_lvars, dummy))
      end
    fun visit_EAppConstr this env data = 
      let
        val vtable = cast this
        val ((var, eia), ts, is, e, ot) = data
        val env = set_has_k env
        val ot = Option.map (mapSnd (#visit_mtype vtable this env)) ot
        val e = #visit_expr vtable this env e
        val is = map (#visit_idx vtable this env) is
        val ts = map (#visit_mtype vtable this env) ts
        val var = #visit_cvar vtable this env var
      in
        EAppConstr ((var, eia), ts, is, e, ot)
      end
    fun visit_EPair this env data =
      let
        val vtable = cast this
        val (e1, e2) = data
        val (e1, e2) = visit_e2 this env (e1, e2)
      in
        EBinOp (EBPair (), e1, e2)
      end
    fun visit_EAdd this env data =
      let
        val vtable = cast this
        val (e1, e2) = data
        val (e1, e2) = visit_e2 this env (e1, e2)
      in
        EBinOp (EBAdd, e1, e2)
      end
    fun visit_ENatAdd this env data =
      let
        val vtable = cast this
        val (e1, e2) = data
        val (e1, e2) = visit_e2 this env (e1, e2)
      in
        EBinOp (EBNatAdd, e1, e2)
      end
    fun visit_ENew this env data =
      let
        val vtable = cast this
        val (e1, e2) = data
        val (e1, e2) = visit_e2 this env (e1, e2)
      in
        EBinOp (EBNew (), e1, e2)
      end
    fun visit_ERead this env data =
      let
        val vtable = cast this
        val (e1, e2) = data
        val (e1, e2) = visit_e2 this env (e1, e2)
      in
        EBinOp (EBRead (), e1, e2)
      end
    fun visit_ETriOp this env (opr, e1, e2, e3) =
      case opr of
          ETIte _ =>
          let
            val lvars = #1 env
            val n_lvars = num_lvars env
            val vtable = cast this
            val new_lvars = ref Set.empty
            (* In the branches, there will be a live continuation variable. *)
            val e2 = #visit_expr vtable this (new_lvars, false, true) e2
            val () = output_set lvars (!new_lvars)
            val () = new_lvars := Set.empty
            val e3 = #visit_expr vtable this (new_lvars, false, true) e3
            val () = output_set lvars (!new_lvars)
            val env = set_has_k env
            val e1 = #visit_expr vtable this env e1
          in
            ETriOp (opr, e1, e2, EAnnoLiveVars (e3, n_lvars, dummy))
          end
        | _ =>
          let
            val vtable = cast this
            val (e1, e2, e3) = visit_e3 this env (e1, e2, e3)
          in
            ETriOp (opr, e1, e2, e3)
          end
    fun visit_EEI this env data = 
      let
        val vtable = cast this
        val (opr, e, i) = data
        val data = (e, i)
      in
        case opr of
	    EEIAppI () => #visit_EAppI vtable this env data
	  | EEIAscTime () => #visit_EAscTime vtable this env data
	  | EEIAscSpace () =>
            EEI (EEIAscSpace (), #visit_expr vtable this env e, #visit_idx vtable this env i)
      end
    fun visit_EAscTime this env data = 
      let
        val vtable = cast this
        val (e, i) = data
        val e = #visit_expr vtable this env e
        val i = #visit_idx vtable this env i
      in
        EEI (EEIAscTime (), e, i)
      end
    fun visit_EET this env data = 
      let
        val vtable = cast this
        val (opr, e, t) = data
        val data = (e, t)
      in
        case opr of
	    EETAppT () => #visit_EAppT vtable this env data
	  | EETAsc () => #visit_EAsc vtable this env data
          | EETHalt () =>
            let
              val env = set_has_k env
            in
              EET (opr, #visit_expr vtable this env e, #visit_mtype vtable this env t)
            end
      end
    fun visit_EAsc this env data = 
      let
        val vtable = cast this
        val (e, t) = data
        val e = #visit_expr vtable this env e
        val t = #visit_mtype vtable this env t
      in
        EET (EETAsc (), e, t)
      end
    fun visit_ET this env data = 
      let
        val vtable = cast this
        val (opr, t, r) = data
        val t = #visit_mtype vtable this env t
      in
        ET (opr, t, r)
      end
    fun get_num_ebind_pn pn = snd $ PV.count_binder_pn pn
    fun visit_bind visit_body env bind =
      let
        val lvars = #1 env
        val (pn, e) = unBind bind
        val n = get_num_ebind_pn pn
        val () = unop_ref (Set.map (shift n)) lvars
        val e = visit_body env e
        val () = unop_ref (forget n) lvars
      in
        Bind (pn, e)
      end
    fun visit_EAbs this env (st, bind, spec) =
      let
        val lvars = #1 env
        val vtable = cast this
        val spec = visit_option (visit_pair (#visit_idx vtable this) (#visit_idx vtable this)) env spec
        val new_lvars = ref Set.empty
        (* now there will be a live continuation variable *)
        val bind = visit_bind (#visit_expr vtable this) (new_lvars, false, true) bind
        val () = output_set lvars (!new_lvars)
        val st = StMap.map (#visit_idx vtable this env) st
      in
        EAbs (st, bind, spec)
      end
    fun visit_EAbsI this (lvars, _, _) (bind, r) =
      let
        val vtable = cast this
        val new_lvars = ref Set.empty
        (* now there will be a live continuation variable *)
        val bind = visit_ibind_anno this (#visit_sort vtable this) (#visit_expr vtable this) (new_lvars, false, true) bind
        val () = output_set lvars (!new_lvars)
      in
        EAbsI (bind, r)
      end
    fun visit_return this env (t, i, j) =
      let
        val vtable = cast this
        val t = Option.map (#visit_mtype vtable this env) t                                      
        val i = Option.map (#visit_idx vtable this env) i                                     
        val j = Option.map (#visit_idx vtable this env) j
      in
        (t, i, j)
      end
    fun visit_ECase this env (e, return, binds, r) =
      let
        val lvars = #1 env
        val n_lvars = num_lvars env
        val vtable = cast this
        val new_lvars = ref Set.empty
        val binds =
            if length binds >= 2 then
              map (fn bind =>
                      let
                        val () = new_lvars := Set.empty
                        (* In the branches, there will be a live continuation variable. *)
                        val bind = visit_bind (#visit_expr vtable this) (new_lvars, false, true) bind
                        val () = output_set lvars (!new_lvars)
                      in
                        bind
                      end
                  ) binds
            else
              map (visit_bind (#visit_expr vtable this) env) binds
        val return = visit_return this env return
        val env = set_has_k env
        val e = #visit_expr vtable this env e
        val e = EAnnoLiveVars (e, n_lvars, r)
      in
        ECase (e, return, binds, r)
      end
    fun get_num_ebind_decls a = #4 $ count_binder_decls a
    fun visit_ELet this (env as (lvars, _, _)) (return, bind, r) =
      let
        val vtable = cast this
        val (decls, e) = unBind bind
        val n = get_num_ebind_decls decls
        val () = unop_ref (Set.map (shift n)) lvars
        val e = #visit_expr vtable this env e
        val env = set_has_k env
        val decls = visit_decls (#visit_decl vtable this) (env2ctx env) decls
        val bind = Bind (decls, e)
        val return = visit_return this env return
      in
        ELet (return, bind, r)
      end
    fun visit_ECaseSumbool this env (e, bind1, bind2, r) =
      let
        val vtable = cast this
        val bind1 = visit_ibind this (#visit_expr vtable this) env bind1
        val bind2 = visit_ibind this (#visit_expr vtable this) env bind2
        val env = set_has_k env
        val e = #visit_expr vtable this env e
      in
        ECaseSumbool (e, bind1, bind2, r)
      end
    fun visit_decl this env data =
      let
        val vtable = cast this
      in
        case data of
            DVal data => #visit_DVal vtable this env data
          | DValPtrn data => #visit_DValPtrn vtable this env data
          | DRec data => #visit_DRec vtable this env data
          | DIdxDef data => #visit_DIdxDef vtable this env data
          | DAbsIdx2 data => #visit_DAbsIdx2 vtable this env data
          | DAbsIdx data => #visit_DAbsIdx vtable this env data
          | DTypeDef data => #visit_DTypeDef vtable this env data
          | DConstrDef data => #visit_DConstrDef vtable this env data
          | DOpen data => #visit_DOpen vtable this env data
      end
    fun visit_ibinder this env name =
      let
        val vtable = cast this
        val name = visit_binder (#extend_i vtable this) env name
      in
        name
      end
    fun visit_tbinder this env name =
      let
        val vtable = cast this
        val name = visit_binder (#extend_t vtable this) env name
      in
        name
      end
    fun visit_cbinder this env name =
      let
        val vtable = cast this
        val name = visit_binder (#extend_c vtable this) env name
      in
        name
      end
    fun visit_ebinder this (ctx : (Set.set ref * bool * bool) ctx) name =
      let
        val lvars = #1 $ !(#current ctx)
        val () = unop_ref (forget 1) lvars
      in
        name
      end
    fun visit_DVal this ctx (name, bind, r) =
      let
        (* val () = println "visit_DVal" *)
        val vtable = cast this
        val name = visit_ebinder this ctx name
        val (tbinders, e) = unBind $ unOuter bind
        val e = #visit_expr vtable this (#outer ctx) e
        val bind = Outer $ Bind (tbinders, e)
      in
        [DVal (name, bind, r)]
      end
    fun visit_DValPtrn this ctx (pn, e, r) =
      let
        val lvars = #1 $ !(#current ctx)
        val vtable = cast this
        val n = get_num_ebind_pn pn
        val () = unop_ref (forget n) lvars
        val e = visit_outer (#visit_expr vtable this) ctx e
      in
        [DValPtrn (pn, e, r)]
      end
    fun visit_map f env st = StMap.map (f env) st
    fun get_num_ebind_rec_binds (_, stbinds) =
      sum $ map (fn SortingST _ => 0
                | TypingST pn => get_num_ebind_pn pn) $ unTeles $ unRebind stbinds
    fun visit_DRec this ctx (name, bind, r) =
      let
        (* val () = println "visit_DRec" *)
        val env = !(#current ctx)
        val lvars = #1 env
        val vtable = cast this
        val new_lvars = ref Set.empty
        val (p, body) = unBind $ unInner bind
        val body =
            visit_triple (visit_pair (visit_map $ #visit_idx vtable this)
                                     (visit_map $ #visit_idx vtable this))
                         (visit_pair (#visit_mtype vtable this)
                                     (visit_pair (#visit_idx vtable this)
                                                 (#visit_idx vtable this)))
                         (#visit_expr vtable this) (new_lvars, false, true) body
        val n = get_num_ebind_rec_binds p
        val () = unop_ref (forget n) new_lvars
        val () = output_set lvars (!new_lvars)
        val name = visit_ebinder this ctx name
        val bind = Inner $ Bind (p, body)
      in
        [DRec (name, bind, r)]
      end
    fun visit_DIdxDef this env data =
      let
        val vtable = cast this
        val (name, s, i) = data
        val name = visit_ibinder this env name
        val s = visit_outer (visit_option (#visit_sort vtable this)) env s
        val i = visit_outer (#visit_idx vtable this) env i
      in
        [DIdxDef (name, s, i)]
      end
    fun visit_DAbsIdx2 this env data =
      let
        val vtable = cast this
        val (name, s, i) = data
        val name = visit_ibinder this env name
        val s = visit_outer (#visit_sort vtable this) env s
        val i = visit_outer (#visit_idx vtable this) env i
      in
        [DAbsIdx2 (name, s, i)]
      end
    fun visit_DAbsIdx this env data =
      let
        val vtable = cast this
        val ((name, s, i), decls, r) = data
        val name = visit_ibinder this env name
        val s = visit_outer (#visit_sort vtable this) env s
        val i = visit_outer (#visit_idx vtable this) env i
        val decls = visit_rebind (visit_decls (#visit_decl vtable this)) env decls
      in
        [DAbsIdx ((name, s, i), decls, r)]
      end
    fun visit_DTypeDef this env data =
      let
        (* val () = println "default visit_DTypeDef" *)
        val vtable = cast this
        val (name, t) = data
        val name = visit_tbinder this env name
        val t = visit_outer (#visit_mtype vtable this) env t
        val cnames = map (Binder o CName) $ get_constr_names $ unOuter t
        val cnames = visit_list (visit_cbinder this) env cnames
      in
        [DTypeDef (name, t)]
      end
    fun visit_DConstrDef this env data =
      let
        val vtable = cast this
        val (name, x) = data
        val name = visit_cbinder this env name
        val x = visit_outer (#visit_cvar vtable this) env x
      in
        [DConstrDef (name, x)]
      end
    fun visit_scoping_ctx m this ctx (sctx, kctx, cctx, tctx) =
      let
        val _ = visit_list (visit_ibinder this) ctx $ rev sctx
        val _ = visit_list (visit_tbinder this) ctx $ rev kctx
        val _ = visit_list (visit_cbinder this) ctx $ rev cctx
        val _ = visit_list (visit_ebinder this) ctx $ rev tctx
        val (m, _) = unInner m
        val lvars = #1 $ !(#current ctx)
        (* 'open' touches all evars in the module, so all of them should be counted as live evars *)
        val () = appi (fn (i, _) => output lvars $ inr (m, i)) tctx
      in
        (sctx, kctx, cctx, tctx)
      end
    fun visit_DOpen this ctx (m, scp) =
      let
        val vtable = cast this
        val m = visit_inner (#visit_mod_id vtable this) ctx m
        val scp = Option.map (visit_scoping_ctx m this ctx) scp
      in
        [DOpen (m, scp)]
      end
        
    fun visit_cvar_tag this env data =
      let
        val vtable = cast this
      in
        visit_pair (#visit_cvar vtable this) (#visit_ptrn_constr_tag vtable this) env data
      end
    fun this_impls_ptrn_visitor_interface this =
      let
        val vtable = cast this
      in
        {
          visit_ptrn = #visit_ptrn vtable,
          visit_PnVar = #visit_PnVar vtable,
          visit_PnTT = #visit_PnTT vtable,
          visit_PnPair = #visit_PnPair vtable,
          visit_PnAlias = #visit_PnAlias vtable,
          visit_PnAnno = #visit_PnAnno vtable,
          visit_PnConstr = #visit_PnConstr vtable,
          visit_cvar = visit_cvar_tag,
          visit_mtype = #visit_mtype vtable,
          extend_i = #extend_i vtable,
          extend_e = #extend_e vtable
        }
      end
    val pv_vtable =
        PV.default_ptrn_visitor_vtable
          this_impls_ptrn_visitor_interface
          extend_i
          extend_e
          visit_cvar_tag
          visit_mtype
    fun visit_sgn this env data =
      let
        val vtable = cast this
        val (specs, r) = data
        val specs = unTeles $ visit_tele (#visit_spec vtable this) env $ Teles specs
      in
        (specs, r)
      end
    fun visit_spec this env data =
      let
        val vtable = cast this
      in
        case data of
            SpecVal data => #visit_SpecVal vtable this env data
          | SpecIdx data => #visit_SpecIdx vtable this env data
          | SpecType data => #visit_SpecType vtable this env data
          | SpecTypeDef data => #visit_SpecTypeDef vtable this env data
      end
    fun visit_SpecVal this env data =
      let
        val vtable = cast this
        val (ename, t) = data
        val ename = unBinderName $ visit_ebinder this env $ EBinder ename
        val t = unOuter $ visit_outer (#visit_ty vtable this) env $ Outer t
      in
        SpecVal (ename, t)
      end
    fun visit_SpecIdx this env data =
      let
        val vtable = cast this
        val (iname, s) = data
        val iname = unBinderName $ visit_ibinder this env $ IBinder iname
        val s = unOuter $ visit_outer (#visit_sort vtable this) env $ Outer s
      in
        SpecIdx (iname, s)
      end
    fun visit_SpecType this env data =
      let
        val vtable = cast this
        val (tname, k) = data
        val tname = unBinderName $ visit_tbinder this env $ TBinder tname
        val k = unOuter $ visit_outer (#visit_kind vtable this) env $ Outer k
      in
        SpecType (tname, k)
      end
    fun visit_SpecTypeDef this env data =
      let
        val vtable = cast this
        val (tname, t) = data
        val tname = unBinderName $ visit_tbinder this env $ TBinder tname
        val t = unOuter $ visit_outer (#visit_mtype vtable this) env $ Outer t
        val cnames = map (Binder o CName) $ get_constr_names t
        val cnames = visit_list (visit_cbinder this) env cnames
      in
        SpecTypeDef (tname, t)
      end
    fun visit_mod this env data =
      let
        val vtable = cast this
      in
        case data of
            ModComponents data => #visit_ModComponents vtable this env data
          | ModSeal data => #visit_ModSeal vtable this env data
          | ModTransparentAsc data => #visit_ModTransparentAsc vtable this env data
      end
    fun visit_ModComponents this env data =
      let
        val vtable = cast this
        val (decls, r) = data
        val decls = unTeles $ visit_decls (#visit_decl vtable this) env $ Teles decls
      in
        ModComponents (decls, r)
      end
    fun copy_ctx (ctx : 'env ctx) =
      {outer = #outer ctx, current = copy_ref $ #current ctx}
    fun visit_ModSeal this ctx data =
      let
        val vtable = cast this
        val (m, sg) = data
        val ctx' = copy_ctx ctx
        val m = #visit_mod vtable this ctx' m
        val sg = #visit_sgn vtable this ctx sg
      in
        ModSeal (m, sg)
      end
    fun visit_ModTransparentAsc this ctx data =
      let
        val vtable = cast this
        val (m, sg) = data
        val ctx' = copy_ctx ctx
        val m = #visit_mod vtable this ctx m
        val sg = #visit_sgn vtable this ctx' sg
      in
        ModTransparentAsc (m, sg)
      end
  in
    {
      visit_expr = visit_expr,
      visit_EVar = visit_EVar,
      visit_EConst = visit_EConst,
      visit_EUnOp = visit_EUnOp,
      visit_EBinOp = visit_EBinOp,
      visit_ETriOp = visit_ETriOp,
      visit_EEI = visit_EEI,
      visit_EET = visit_EET,
      visit_ET = visit_ET,
      visit_EAbs = visit_EAbs,
      visit_EAbsI = visit_EAbsI,
      visit_EAppConstr = visit_EAppConstr,
      visit_ECase = visit_ECase,
      visit_ELet = visit_ELet,
      visit_ECaseSumbool = visit_ECaseSumbool,
      visit_decl = visit_decl,
      visit_DVal = visit_DVal,
      visit_DValPtrn = visit_DValPtrn,
      visit_DRec = visit_DRec,
      visit_DIdxDef = visit_DIdxDef,
      visit_DAbsIdx2 = visit_DAbsIdx2,
      visit_DAbsIdx = visit_DAbsIdx,
      visit_DTypeDef = visit_DTypeDef,
      visit_DConstrDef = visit_DConstrDef,
      visit_DOpen = visit_DOpen,
      visit_ptrn = #visit_ptrn pv_vtable,
      visit_PnVar = #visit_PnVar pv_vtable,
      visit_PnTT = #visit_PnTT pv_vtable,
      visit_PnPair = #visit_PnPair pv_vtable,
      visit_PnAlias = #visit_PnAlias pv_vtable,
      visit_PnAnno = #visit_PnAnno pv_vtable,
      visit_PnConstr = #visit_PnConstr pv_vtable,
      visit_sgn = visit_sgn,
      visit_spec = visit_spec,
      visit_mod = visit_mod,
      visit_ty = visit_ty,
      visit_kind = visit_kind,
      visit_SpecVal = visit_SpecVal,
      visit_SpecIdx = visit_SpecIdx,
      visit_SpecType = visit_SpecType,
      visit_SpecTypeDef = visit_SpecTypeDef,
      visit_ModComponents = visit_ModComponents,
      visit_ModSeal = visit_ModSeal,
      visit_ModTransparentAsc = visit_ModTransparentAsc,
      visit_EApp = visit_EApp,
      visit_EPair = visit_EPair,
      visit_EAdd = visit_EAdd,
      visit_ENatAdd = visit_ENatAdd,
      visit_ENew = visit_ENew,
      visit_ERead = visit_ERead,
      visit_EAppT = visit_EAppT,
      visit_EAsc = visit_EAsc,
      visit_EAppI = visit_EAppI,
      visit_EAscTime = visit_EAscTime,
      visit_var = visit_var,
      visit_cvar = visit_cvar,
      visit_mod_id = visit_mod_id,
      visit_idx = visit_idx,
      visit_sort = visit_sort,
      visit_mtype = visit_mtype,
      visit_ptrn_constr_tag = visit_ptrn_constr_tag,
      extend_i = extend_i,
      extend_t = extend_t,
      extend_c = extend_c,
      extend_e = extend_e
    }
  end

fun new_live_vars_expr_visitor params = new_expr_visitor live_vars_expr_visitor_vtable params
                                                         
fun live_vars_e b =
  let
    val lvars = ref Set.empty
    val visitor as (ExprVisitor vtable) = new_live_vars_expr_visitor ()
    val b = #visit_expr vtable visitor (lvars, true, false) b
  in
    (b, !lvars)
  end
    
fun live_vars_decls b =
  let
    val lvars = ref Set.empty
    val visitor as (ExprVisitor vtable) = new_live_vars_expr_visitor ()
    val b = visit_decls (#visit_decl vtable visitor) (env2ctx (lvars, true, false)) b
  in
    (b, !lvars)
  end
    
end
