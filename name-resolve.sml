(* name resolving and annotation propogation *)

structure NameResolve = struct
structure S = NamefulExpr
structure T = UnderscoredExpr
open T
open Region
open Gctx
open List
structure SS = NamefulToString
structure SE = NamefulEqual
       
exception Error of region * string

infixr 0 $

(* sorting context *)
type scontext = string list
(* kinding context *)
(* type kinding = kind *)
type kcontext = string list 
(* constructor context *)
type ccontext = (string * string list) list
(* typing context *)
type tcontext = string list
type context = scontext * kcontext * ccontext * tcontext
datatype sgntr =
         Sig of (* ns_sigcontext *  *)context
         | FunctorBind of (string * context) (* list *) * context
                                                            
type ns_sigcontext = sgntr Gctx.map
                                   
fun runError m _ =
    OK (m ())
    handle
    Error e => Failed e

fun on_id ctx (x, r) =
    case find_idx x ctx of
	SOME i => (i, r)
      | NONE => raise Error (r, sprintf "Unbound variable $ in context: $" [x, str_ls id ctx])

fun filter_module gctx =
    Gctx.mapPartial (fn sg => case sg of Sig sg => SOME sg | _ => NONE) gctx

fun ns_lookup_module gctx m =
    nth_error2 (filter_module gctx) m

fun names ctx = map fst ctx

fun ctx_names ((sctx, kctx, cctx, tctx) : context) =
    (sctx, kctx, names cctx, tctx) 

fun gctx_names (gctx : ns_sigcontext) =
    let
      val gctx = filter_module gctx
      val gctx = Gctx.map ctx_names gctx
    in
      gctx
    end
      
fun find_long_id gctx sel eq ctx id =
    case id of
        ID (x, xr) =>
        opt_bind (findOptionWithIdx (eq x) ctx)
                 (fn x => opt_return (NONE, (x, xr)))
      | QID ((m, mr), (x, xr)) =>
        opt_bind (ns_lookup_module gctx m)
                 (fn (m, sg) =>
                     opt_bind (findOptionWithIdx (eq x) $ sel sg)
                              (fn x => opt_return (SOME (m, mr), (x, xr))))

fun to_long_id (m, x) =
  case m of
      NONE => ID x
    | SOME m => QID (m, x)
                    
fun on_long_id gctx sel ctx x =
    case find_long_id gctx sel is_eq_snd ctx x of
        SOME x => to_long_id x
      | NONE => raise Error (S.get_region_long_id x, sprintf "Unbound (long) variable '$' in context: $ $" [SS.str_var #1 empty [] x, str_ls id ctx, str_ls id $ domain gctx])
                      
fun find_constr (gctx : ns_sigcontext) ctx x =
    flip Option.map (find_long_id gctx #3 is_eq_fst_snd ctx x)
         (fn (m, ((i, inames), xr)) => (to_long_id (m, (i, xr)), inames))
         
fun on_quan q =
    case q of
        Forall () => Forall ()
      | Exists _ => Exists NONE

structure IdxVisitor = IdxVisitorFn (structure S = S.Idx
                                     structure T = T.Idx)
(* open IdxVisitor *)
structure IV = IdxVisitor
                           
(***** the "import" (or name-resolving) visitor: converting nameful terms to de Bruijn indices ***)
                 
fun import_idx_visitor_vtable cast gctx : ('this, scontext) IV.idx_visitor_vtable =
  let
    fun extend this env name = (fst name :: env, name)
    fun visit_var this env x =
      on_long_id gctx #1 env x
    fun visit_quan _ _ q = on_quan q
  in
    IV.default_idx_visitor_vtable
      cast
      extend
      visit_var
      visit_noop
      visit_noop
      visit_noop
      visit_quan
  end

fun new_import_idx_visitor a = IV.new_idx_visitor import_idx_visitor_vtable a
    
fun on_basic_sort b =
  let
    val visitor as (IV.IdxVisitor vtable) = new_import_idx_visitor empty
  in
    #visit_basic_sort vtable visitor [] b
  end
    
fun on_idx gctx ctx b =
  let
    val visitor as (IV.IdxVisitor vtable) = new_import_idx_visitor gctx
  in
    #visit_idx vtable visitor ctx b
  end
    
fun on_prop gctx ctx b =
  let
    val visitor as (IV.IdxVisitor vtable) = new_import_idx_visitor gctx
  in
    #visit_prop vtable visitor ctx b
  end
    
fun on_sort gctx ctx b =
  let
    val visitor as (IV.IdxVisitor vtable) = new_import_idx_visitor gctx
  in
    #visit_sort vtable visitor ctx b
  end
    
fun on_kind k = mapSnd (map on_basic_sort) k

open Bind
       
structure TV = TypeVisitorFn (structure S = S.Type
                              structure T = T.Type)
                                         
fun on_i_type_visitor_vtable cast gctx : ('this, scontext * kcontext) TV.type_visitor_vtable =
  let
    fun extend_i this (sctx, kctx) name = ((fst name :: sctx, kctx), name)
    fun extend_t this (sctx, kctx) name = ((sctx, fst name :: kctx), name)
    fun visit_var this (sctx, kctx) x =
      on_long_id gctx #2 kctx x
    fun for_idx f this (sctx, kctx) b = f gctx sctx b
    val vtable = 
        TV.default_type_visitor_vtable
          cast
          extend_i
          extend_t
          visit_var
          (ignore_this_env on_basic_sort)
          (for_idx on_idx)
          (for_idx on_sort)
          (ignore_this_env on_kind)
          visit_noop
    fun visit_TAppI this ctx (data as (t1, i)) =
      let
        val vtable = cast this
        fun default () = TAppI (#visit_mtype vtable this ctx t1, #visit_idx vtable this ctx i)
        val t = S.TAppI data
      in
        case S.is_TAppV t of
            SOME (x, ts, is) =>
            let
              val ts = map (#visit_mtype vtable this ctx) ts
              val is = map (#visit_idx vtable this ctx) is
            in
              if SE.eq_var (x, (ID ("nat", dummy))) andalso length ts = 0 andalso length is = 1 then
                TNat (hd is, S.get_region_mt t)
              else if SE.eq_var (x, (ID ("ibool", dummy))) andalso length ts = 0 andalso length is = 1 then
                TiBool (hd is, S.get_region_mt t)
              else if SE.eq_var (x, (ID ("array", dummy))) andalso length ts = 1 andalso length is = 1 then
                TArray (hd ts, hd is)
              else
                default ()
            end
          | NONE => default ()         
      end
    val vtable = TV.override_visit_TAppI vtable visit_TAppI
  in
    vtable
  end

fun new_on_i_type_visitor a = TV.new_type_visitor on_i_type_visitor_vtable a
    
fun on_mtype gctx ctx b =
  let
    val visitor as (TV.TypeVisitor vtable) = new_on_i_type_visitor gctx
  in
    #visit_mtype vtable visitor ctx b
  end
    
fun on_datatype gctx ctx b =
  let
    val visitor as (TV.TypeVisitor vtable) = new_on_i_type_visitor gctx
  in
    #visit_datatype vtable visitor ctx b
  end
    
fun on_type gctx ctx b =
  let
    val visitor as (TV.TypeVisitor vtable) = new_on_i_type_visitor gctx
  in
    #visit_ty vtable visitor ctx b
  end
    
fun on_constr_info gctx ctx b =
  let
    val visitor as (TV.TypeVisitor vtable) = new_on_i_type_visitor gctx
  in
    #visit_constr_info vtable visitor ctx b
  end
    
val empty_ctx = ([], [], [], [])
      
fun shift_return (sctxn, kctxn) (t, d, j) =
    let
      open UnderscoredSubst
    in
      (Option.map (fn t => shiftx_t_mt 0 kctxn $ shiftx_i_mt 0 sctxn t) t,
       Option.map (fn d => shiftx_i_i 0 sctxn d) d,
       Option.map (fn d => shiftx_i_i 0 sctxn d) j)
    end
      
(* fun copy_anno gctx (anno as (t, d, j)) e = *)
(*     let *)
(*       val copy_anno = copy_anno gctx *)
(*       val copy_anno_rule = copy_anno_rule gctx *)
(*       fun copy a b = case a of *)
(*                          NONE => b *)
(*                        | SOME _ => a *)
(*     in *)
(*       case e of *)
(*           ECase (e, (t', d', j'), es, r) => *)
(*           let *)
(*             fun is_tuple_value e = *)
(*                 (* case e of *) *)
(*                 (*     EVar _ => true *) *)
(*                 (*   (* | EBinOp (EBPair (), e1, e2) => is_tuple_value e1 andalso is_tuple_value e2 *) *) *)
(*                 (*   | _ => false *) *)
(*                 false *)
(*             (* if e is tuple value, we are sure it doesn't cost time, so we can copy time annotation *) *)
(*             val (d, j) = if is_tuple_value e then (d, j) else (NONE, NONE) *)
(*             val (t, d, j) = (copy t' t, copy d' d, copy j' j) *)
(*             (* val es = map (copy_anno_rule (t, d, j)) es *) *)
(*           in *)
(*             ECase (e, (t, d, j), es, r) *)
(*           end *)
(*         | ELet ((t', d', j'), bind, r) => *)
(*           let *)
(*             val (decls, e) = Unbound.unBind bind *)
(*             val decls = unTeles decls *)
(*             val (t, d, j) = (copy t' t, copy d' d, copy j' j) *)
(*             open UnderscoredToString *)
(*             val (_, (sctx, kctx, _, _)) = str_decls gctx ([], [], [], []) decls *)
(*             val (sctxn, kctxn) = (length sctx, length kctx) *)
(*             fun is_match_var decl = *)
(*                 case decl of *)
(*                     DValPtrn (_, Outer (EVar _), _) => true *)
(*                   | DVal (_, Outer bind, _) => *)
(*                     let *)
(*                       val (_, e) = Unbound.unBind bind *)
(*                     in *)
(*                       case e of *)
(*                           EVar _ => true *)
(*                         | _ => false *)
(*                     end *)
(*                   | _ => false *)
(*             val (d', j') = if List.all is_match_var decls then (d, j) else (NONE, NONE) *)
(*           in *)
(*             ELet ((t, d, j), Unbound.Bind (Teles decls, copy_anno (shift_return (sctxn, kctxn) (t, d', j')) e), r) *)
(*           end *)
(*         | EEI (EEIAscTime (), e, d') => *)
(*           let *)
(*             val d = SOME d' *)
(*             val e = copy_anno (t, d, j) e *)
(*           in *)
(*             EAscTime (e, d') *)
(*           end *)
(*         | EEI (EEIAscSpace (), e, j') => *)
(*           let *)
(*             val j = SOME j' *)
(*             val e = copy_anno (t, d, j) e *)
(*           in *)
(*             EAscSpace (e, j') *)
(*           end *)
(*         | EET (EETAsc (), e, t') => *)
(*           let *)
(*             val t = SOME t' *)
(*             val e = copy_anno (t, d, j) e *)
(*           in *)
(*             EAsc (e, t') *)
(*           end *)
(*         | ET (ETNever (), _, _) => e *)
(*         | _ => *)
(*           case t of *)
(*               SOME t => EAsc (e, t) *)
(*             | NONE => e *)
(*     end *)
      
(* and copy_anno_rule gctx return bind = *)
(*     let *)
(*       val (pn, e) = Unbound.unBind bind *)
(*       fun ptrn_names pn : string list * string list = PatternVisitor.collect_binder_pn pn *)
(*       val (sctx, _) = ptrn_names pn *)
(*       val offset = (length sctx, 0) *)
(*     in *)
(*       Unbound.Bind (pn, copy_anno gctx (shift_return offset return) e) *)
(*     end *)
      
fun get_datatype_names (Bind (name, tbinds)) =
    let
      val (_, (_, constr_decls)) = unfold_binds tbinds
      val cnames = map (fn (name, core, _) => (fst name, get_constr_inames core)) constr_decls
    in
      (fst name, cnames)
    end
      
structure EV = ExprVisitorFn (structure S = S
                              structure T = T)

val st_ref = ref SSet.empty
fun add_ref a = binop_ref (curry $ SSet.add) a
infix  9 @%!
fun m @%! k = SSet.member (m, k)
      
fun on_expr_visitor_vtable cast gctx : ('this, context) EV.expr_visitor_vtable =
  let
    fun extend_i this (sctx, kctx, cctx, tctx) name = ((Name2str name :: sctx, kctx, cctx, tctx), name)
    fun extend_t this (sctx, kctx, cctx, tctx) name = ((sctx, Name2str name :: kctx, cctx, tctx), name)
    (* Extending cctx will be performed by extend_c_data. We still need extend_c (can't just throw Impossible) because the default visit_DTypeDef and visit_SpecTypeDef use extend_c. *)
    val extend_c = extend_noop 
    (* fun extend_c this (sctx, kctx, cctx, tctx) name = raise Impossible $ "import_e/extend_c:" ^ Name2str name *)
    (* fun extend_c this (sctx, kctx, cctx, tctx) name = (sctx, kctx, Name2str name :: cctx, tctx) *)
    fun extend_c_data (sctx, kctx, cctx, tctx) a = ((sctx, kctx, a :: cctx, tctx), a)
    fun extend_e this (sctx, kctx, cctx, tctx) name = ((sctx, kctx, cctx, Name2str name :: tctx), name)
    fun visit_cvar this (sctx, kctx, cctx, tctx) x =
      on_long_id gctx (map fst o #3) (map fst cctx) x
    fun for_idx f this (sctx, kctx, cctx, tctx) b = f gctx sctx b
    fun for_type f this (sctx, kctx, cctx, tctx) b = f gctx (sctx, kctx) b
    val vtable = 
        EV.default_expr_visitor_vtable
          cast
          extend_i
          extend_t
          extend_c
          extend_e
          (visit_imposs "import_e/visit_var")
          visit_cvar
          (visit_imposs "import_e/visit_mod_projectible")
          (for_idx on_idx)
          (for_idx on_sort)
          (for_type on_mtype)
          (for_type on_type)
          (ignore_this_env on_kind)
          (visit_imposs "import_e/visit_ptrn_constr_tag")
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
    fun visit_ebinder this env name =
      let
        val vtable = cast this
        val name = visit_binder (#extend_e vtable this) env name
      in
        name
      end
    fun visit_PnConstr this env (Outer ((x, ()), eia), inames, pn, r) =
      let
        val vtable = cast this
        val (_, _, cctx, _) = #outer env
      in
        case find_constr gctx cctx x of
	    SOME (x, c_inames) =>
            let
              val inames =
                  if eia then
                    inames
                  else
                    if length inames = 0 then map (str2ibinder o prefix "__") c_inames
                    else raise Error (r, "Constructor pattern can't have explicit index pattern arguments. Use [@constructor_name] if you want to write explict index pattern arguments.")
              val inames = map (visit_ibinder this env) inames
              val pn = #visit_ptrn vtable this env pn
            in
              PnConstr (Outer ((x, ()), true), inames, pn, r)
            end
	  | NONE =>
            raise Error (S.get_region_long_id x, "Unknown constructor " ^ SS.str_var #1 empty [] x)
      end
    val vtable = EV.override_visit_PnConstr vtable visit_PnConstr
    fun visit_PnVar this env ename =
      let
        val vtable = cast this
        val (_, _, cctx, _) = #outer env
        val name = unBinderName ename
      in
        case find_constr gctx cctx (ID name) of
	    SOME (x, c_inames) =>
            let
              val r = snd name
              val inames = map (str2ibinder o prefix "__") c_inames
              val inames = map (visit_ibinder this env) inames
            in
              PnConstr (Outer ((x, ()), true), inames, PnTT r, r)
            end
	  | NONE =>
            PnVar $ visit_ebinder this env ename
      end
    val vtable = EV.override_visit_PnVar vtable visit_PnVar
    fun visit_EVar this (_, _, cctx, tctx) (x, b) =
      let
        fun is_state_field x =
          case x of
              QID _ => NONE
            | ID (x, r) =>
              if !st_ref @%! x then SOME (x, r)
              else NONE
      in
        case is_state_field x of
            SOME a => EState a
          | NONE =>
            case find_constr gctx cctx x of
                (* Always treat constructors as fully applied. Can't handle partially applied constructors. *)
	        SOME (x, _) => EAppConstr ((x, b), [], [], ETT $ get_region_long_id x, NONE)
	      | NONE => EVar ((on_long_id gctx #4 tctx x), b)
      end
    val vtable = EV.override_visit_EVar vtable visit_EVar
    fun visit_EApp this (ctx as (_, _, cctx, _)) (e1, e2) =
      let
        val vtable = cast this
        val e2 = #visit_expr vtable this ctx e2
	fun default () = 
          EApp (#visit_expr vtable this ctx e1, e2)
	val (e1, is) = S.collect_EAppI e1 
      in
	case e1 of
	    S.EVar (x, b) =>
	    (case find_constr gctx cctx x of
		 SOME (x, _) => EAppConstr ((x, b), [], map (#visit_idx vtable this ctx) is, e2, NONE)
	       | NONE => default ()
            )
	  | _ => default ()
      end
    val vtable = EV.override_visit_EApp vtable visit_EApp
    fun visit_EAppI this (ctx as (_, _, cctx, _)) (data as (e, i)) =
      let
        val super_vtable = vtable
        fun default () = #visit_EAppI super_vtable this ctx data
        val vtable = cast this
	val (e, is) = S.collect_EAppI e
        val is = is @ [i]
      in
	case e of
	    S.EVar (x, b) =>
	    (case find_constr gctx cctx x of
		 SOME (x, _) => EAppConstr ((x, b), [], map (#visit_idx vtable this ctx) is, ETT (S.get_region_i i), NONE)
	       | NONE => default ())
	  | _ => default ()
      end
    val vtable = EV.override_visit_EAppI vtable visit_EAppI
    fun visit_EAscTime this (ctx as (_, _, cctx, _)) (data as (e, i)) =
      let
        val super_vtable = vtable
        val e = #visit_EAscTime super_vtable this ctx data
        val (e, i) = 
            case e of
                EEI (EEIAscTime (), e, i) => (e, i)
              | _ => raise Impossible "import_e/visit_EAscTime"
        (* val e = copy_anno (gctx_names gctx) (NONE, SOME i, NONE) e *)
      in
        EAscTime (e, i)
      end
    val vtable = EV.override_visit_EAscTime vtable visit_EAscTime
    fun visit_EAsc this ctx data =
      let
        val super_vtable = vtable
        val e = #visit_EAsc super_vtable this ctx data
        val (e, t) = 
            case e of
                EET (EETAsc (), e, t) => (e, t)
              | _ => raise Impossible "import_e/visit_EAsc"
        (* val e = copy_anno (gctx_names gctx) (SOME t, NONE, NONE) e *)
      in
        EAsc (e, t)
      end
    val vtable = EV.override_visit_EAsc vtable visit_EAsc
    fun visit_ECase this ctx data =
      let
        val super_vtable = vtable
        val e = #visit_ECase super_vtable this ctx data
        val (e, return, rules, r) =
            case e of
                ECase data => data
              | _ => raise Impossible "import_e/visit_ECase"
        (* val rules = map (copy_anno_rule (gctx_names gctx) return) rules *)
      in
        ECase (e, return, rules, r)
      end
    val vtable = EV.override_visit_ECase vtable visit_ECase
    fun visit_DRec this ctx data =
      let
        val super_vtable = vtable
        val d = #visit_DRec super_vtable this ctx data
        val (name, bind, r) =
            case d of
                [DRec data] => data
              | _ => raise Impossible "import_e/visit_DRec"
        val (names, (sts, (t, (d, j)), e)) = Unbound.unBind $ unInner bind
        (* val e = copy_anno (gctx_names gctx) (SOME t, SOME d, SOME j) e *)
      in
        [DRec (name, Inner $ Unbound.Bind (names, (sts, (t, (d, j)), e)), r)]
      end
    val vtable = EV.override_visit_DRec vtable visit_DRec
    fun visit_DTypeDef this ctx data =
      let
        (* val () = println "new visit_DTypeDef" *)
        val super_vtable = vtable
        val d = #visit_DTypeDef super_vtable this ctx data
        val () =
          case d of
               [DTypeDef (_, Outer (TDatatype (dt, r)))] =>
               let
                 val (_, cnames) = get_datatype_names dt
                 val _ = visit_list (visit_binder extend_c_data) ctx $ map Binder cnames
               in
                 ()
               end
             | _ => ()
      in
        d
      end
    val vtable = EV.override_visit_DTypeDef vtable visit_DTypeDef
    fun visit_SpecTypeDef this ctx data =
      let
        val super_vtable = vtable
        val d = #visit_SpecTypeDef super_vtable this ctx data
        val () =
          case d of
               SpecTypeDef (_, TDatatype (dt, r)) =>
               let
                 val (_, cnames) = get_datatype_names dt
                 val _ = visit_list (visit_binder extend_c_data) ctx $ map Binder cnames
               in
                 ()
               end
             | _ => ()
      in
        d
      end
    val vtable = EV.override_visit_SpecTypeDef vtable visit_SpecTypeDef
    fun visit_DOpen this ctx (m, _) =
      let
        val (m, r) = unInner m
        val (m, ctxd) =
            case ns_lookup_module gctx m of
                SOME a => a
              | NONE => raise Error (r, "Unbound module " ^ m)
        fun visit_scoping_ctx this env (sctx, kctx, cctx, tctx) =
          let
            val _ = visit_list (visit_ibinder this) env $ rev sctx
            val _ = visit_list (visit_tbinder this) env $ rev kctx
            val _ = visit_list (visit_binder extend_c_data) env $ rev cctx
            val _ = visit_list (visit_ebinder this) env $ rev tctx
          in
            ()
          end
        val ctxd = case ctxd of (sctx, kctx, cctx, tctx) =>
                                (map (Binder o IName o attach_snd r) sctx,
                                 map (Binder o TName o attach_snd r) kctx,
                                 map Binder cctx,
                                 map (Binder o EName o attach_snd r) tctx
                                )
        val () = visit_scoping_ctx this ctx ctxd
        val ctxd = case ctxd of (sctx, kctx, cctx, tctx) =>
                                (sctx,
                                 kctx,
                                 map (Binder o CName o attach_snd r o fst o unBinder) cctx,
                                 tctx
                                )
      in
        [DOpen (Inner (m, r), SOME ctxd)]
      end
    val vtable = EV.override_visit_DOpen vtable visit_DOpen
  in
    vtable
  end

fun new_on_expr_visitor a = EV.new_expr_visitor on_expr_visitor_vtable a
    
fun on_expr gctx ctx b =
  let
    val visitor as (EV.ExprVisitor vtable) = new_on_expr_visitor gctx
  in
    #visit_expr vtable visitor ctx b
  end
    
fun on_decls gctx env decls =
  let
    val visitor as (EV.ExprVisitor vtable) = new_on_expr_visitor gctx
  in
    EV.visit_decls_acc visitor (decls, env)
  end
    
fun on_sig gctx decls =
  let
    val visitor as (EV.ExprVisitor vtable) = new_on_expr_visitor gctx
  in
    EV.visit_sgn_acc visitor (decls, empty_ctx)
  end
    
fun on_module gctx decls =
  let
    val visitor as (EV.ExprVisitor vtable) = new_on_expr_visitor gctx
  in
    EV.visit_mod_acc visitor (decls, empty_ctx)
  end
    
fun is_FunctorBind s =
  case s of
      FunctorBind a => SOME a
    | _ => NONE

fun on_top_bind gctx (name, bind) = 
    case bind of
        S.TBMod m =>
        let
          val (m, ctx) = on_module gctx m
        in
          (TBMod m, [(name, Sig ctx)])
        end
      (* | S.TopModSpec ((name, r), sg) => *)
      (*   let *)
      (*     val (sg = on_sig gctx sg *)
      (*     val () = open_module (name, sg) *)
      (*   in *)
      (*     [(name, Sig sg)] *)
      (*   end *)
      | S.TBFunctor (((arg_name, r2), arg), m) =>
        let
          val (arg, arg_ctx) = on_sig gctx arg
          val gctx = Gctx.add (arg_name, Sig arg_ctx) gctx
          val (m, body_ctx) = on_module gctx m
        in
          (TBFunctor (((arg_name, r2), arg), m), [(name, FunctorBind ((arg_name, arg_ctx), body_ctx))])
        end
      | S.TBFunctorApp ((f, f_r), m) =>
        let
          fun lookup_functor (gctx : ns_sigcontext) m =
            opt_bind (Gctx.find (gctx, m)) is_FunctorBind
          fun fetch_functor gctx (m, r) =
              case lookup_functor gctx m of
                  SOME a => a
                | NONE => raise Error (r, "Unbound functor " ^ m)
          val ((formal_arg_name, formal_arg), body) = fetch_functor gctx (f, f_r)
        in
          (TBFunctorApp ((f, f_r), m), [(name, Sig body), (formal_arg_name, Sig formal_arg)])
        end
      | S.TBState (b, t) =>
        let
          val () = add_ref st_ref name
        in
          (TBState (b, on_mtype Gctx.empty ([], []) t), [])
        end
      | S.TBPragma s => (TBPragma s, [])
          
and on_prog gctx binds =
    let
      fun iter (((name, r), bind), (binds, acc, gctx)) =
          let
            val (bind, gctxd) = on_top_bind gctx (name, bind)
          in
            (((name, r), bind) :: binds, gctxd @ acc, addList (gctx, gctxd))
          end
      val (binds, gctxd, gctx) = foldl iter ([], [], gctx) binds
      val binds = rev binds
    in
      (binds, gctxd, gctx)
    end

val resolve_type = on_type
val resolve_expr = on_expr
fun resolve_decls gctx ctx decls = fst (on_decls gctx ctx decls)
val resolve_prog = on_prog

val resolve_constr_info = on_constr_info
val resolve_kind = on_kind

fun resolve_type_opt ctx e = runError (fn () => on_type ctx e) ()
fun resolve_expr_opt ctx e = runError (fn () => on_expr ctx e) ()

fun resolve_constr_info_opt ctx e = runError (fn () => on_constr_info ctx e) ()
fun resolve_kind_opt e = runError (fn () => on_kind e) ()

end
