(* Explicit pair allocation and assignments *)

structure PairAlloc = struct

open Expr
open CompilerUtil
open MicroTiMLVisitor
open MicroTiMLExLongId
open MicroTiMLExLocallyNameless
open MicroTiMLExUtil
open MicroTiMLEx
       
infixr 0 $
         
fun pa_ty_visitor_vtable cast () =
  let
    val vtable =
        default_ty_visitor_vtable
          cast
          extend_noop
          extend_noop
          visit_noop
          visit_noop
          visit_noop
          visit_noop
    fun visit_TBinOp this env (data as (opr, t1, t2)) =
      case opr of
          TBProd =>
          let
            val pa_t = #visit_ty (cast this) this env
            val t1 = pa_t t1
            val t2 = pa_t t2
          in
            TProdEx ((t1, true), (t2, true))
          end
        | _ => #visit_TBinOp vtable this env data (* call super *)
    val vtable = override_visit_TBinOp vtable visit_TBinOp
  in
    vtable
  end

fun new_pa_ty_visitor a = new_ty_visitor pa_ty_visitor_vtable a
    
fun pa_t t =
  let
    val visitor as (TyVisitor vtable) = new_pa_ty_visitor ()
  in
    #visit_ty vtable visitor () t
  end
    
fun pa_expr_visitor_vtable cast () =
  let
    val vtable = 
        default_expr_visitor_vtable
          cast
          extend_noop
          extend_noop
          extend_noop
          extend_noop
          visit_noop
          visit_noop
          visit_noop
          visit_noop
          (ignore_this_env pa_t)
    fun visit_EUnOp this env (data as (opr, e)) =
      case opr of
          EUProj proj => EProjProtected (proj, #visit_expr (cast this) this env e)
        | _ => #visit_EUnOp vtable this env data (* call super *)
    (* fun visit_EBinOp this env (data as (opr, e1, e2)) = *)
    (*   case opr of *)
    (*       EBPair => *)
    (*       let *)
    (*         val pa = #visit_expr (cast this) this env *)
    (*         val (e1, t_e1) = assert_EAscType e1 *)
    (*         val (e2, t_e2) = assert_EAscType e2 *)
    (*         val e1 = pa e1 *)
    (*         val e2 = pa e2 *)
    (*         val t_e1 = pa_t t_e1 *)
    (*         val t_e2 = pa_t t_e2 *)
    (*         val x1 = fresh_evar () *)
    (*         val x2 = fresh_evar () *)
    (*         val y0 = fresh_evar () *)
    (*         val y1 = fresh_evar () *)
    (*         val y2 = fresh_evar () *)
    (*         val () = println $ "e2=" ^ (ExportPP.pp_e_to_string (NONE, NONE) $ ExportPP.export ([], [], [], []) e2) *)
    (*         val e = ELetManyClose ( *)
    (*               [(x1, "px1", e1), *)
    (*                (x2, "px2", e2), *)
    (*                (y0, "y0", EMallocPair (t_e1, t_e2)), *)
    (*                (y1, "y1", EPairAssign (EV y0, ProjFst, EV x1)), *)
    (*                (y2, "y2", EPairAssign (EV y1, ProjSnd, EV x2)) *)
    (*               ], EV y2)                   *)
    (*       in *)
    (*         e *)
    (*       end *)
    (*     | _ => #visit_EBinOp vtable this env data (* call super *) *)
    fun visit_EBinOp this env (data as (opr, e1, e2)) =
      case opr of
          EBPair =>
          let
            val pa = #visit_expr (cast this) this env
            val (e1, t_e1) = assert_EAscType e1
            val (e2, t_e2) = assert_EAscType e2
            val e1 = pa e1
            val e2 = pa e2
            val t_e1 = pa_t t_e1
            val t_e2 = pa_t t_e2
            (* val () = println $ "e2=" ^ (ExportPP.pp_e_to_string (NONE, NONE) $ ExportPP.export ([], [], [], []) e2) *)
            (* EV-bounded *)
            fun EVB n = EVar $ ID (n, dummy)
            val e = ELets (
                  map (mapFst $ attach_snd dummy) $
                  [("x1", e1),
                   ("x2", shift01_e_e e2),
                   ("y0", EMallocPair (t_e1, t_e2)),
                   ("y1", EPairAssign (EVB 0, ProjFst, EVB 2)),
                   ("y2", EPairAssign (EVB 0, ProjSnd, EVB 2))
                  ], EVB 0)                  
          in
            e
          end
        | _ => #visit_EBinOp vtable this env data (* call super *)
    val vtable = override_visit_EUnOp vtable visit_EUnOp
    val vtable = override_visit_EBinOp vtable visit_EBinOp
  in
    vtable
  end

fun new_pa_expr_visitor params = new_expr_visitor pa_expr_visitor_vtable params

fun pa b =
  let
    val visitor as (ExprVisitor vtable) = new_pa_expr_visitor ()
  in
    #visit_expr vtable visitor () b
  end

datatype 'expr decl =
         DLet of free_e * string * 'expr
         | DUnpack of (free_t * string) * (free_e * string) * 'expr
         | DUnpackI of (free_i * string) * (free_e * string) * 'expr

fun close_EDecl (d, e2) =
  case d of
      DLet d => ELetClose (d, e2)
    | DUnpack (a, x, e1) => EUnpackClose (e1, a, x, e2)
    | DUnpackI (a, x, e1) => EUnpackIClose (e1, a, x, e2)
      
fun close_EDecls (decls, e) = foldr close_EDecl e decls
                                                                 
fun anf_decls_expr_visitor_vtable cast output =
  let
    val vtable = 
        default_expr_visitor_vtable
          cast
          extend_noop
          extend_noop
          extend_noop
          extend_noop
          visit_noop
          visit_noop
          visit_noop
          visit_noop
          visit_noop
    fun visit_ELet this env (data as (e1, bind)) =
      let
        val loop = #visit_expr (cast this) this env
        val e1 = loop e1
        val (name_x, e2) = unBindSimpName bind
        val x = fresh_evar ()
        val e2 = open0_e_e x e2
        val () = output $ DLet (x, fst name_x, e1)
        val e2 = loop e2
      in
        e2
      end
    fun visit_EUnpack this env (data as (e1, bind)) =
      let
        val loop = #visit_expr (cast this) this env
        val e1 = loop e1
        val (name_a, bind) = unBindSimpName bind
        val (name_x, e2) = unBindSimpName bind
        val a = fresh_tvar ()
        val x = fresh_evar ()
        val e2 = open0_t_e a e2
        val e2 = open0_e_e x e2
        val () = output $ DUnpack ((a, fst name_a), (x, fst name_x), e1)
        val e2 = loop e2
      in
        e2
      end
    fun visit_EUnpackI this env (data as (e1, bind)) =
      let
        val loop = #visit_expr (cast this) this env
        val e1 = loop e1
        val (name_a, bind) = unBindSimpName bind
        val (name_x, e2) = unBindSimpName bind
        val a = fresh_ivar ()
        val x = fresh_evar ()
        val e2 = open0_i_e a e2
        val e2 = open0_e_e x e2
        val () = output $ DUnpackI ((a, fst name_a), (x, fst name_x), e1)
        val e2 = loop e2
      in
        e2
      end
    fun visit_ERec this env bind =
      let
        val (t_x, (name_x, e)) = unBindAnnoName bind
        val x = fresh_evar ()
        val e = open0_e_e x e
        val (binds, e) = open_collect_EAbsIT e
        val (t_y, (name_y, e)) = assert_EAbs e
        val y = fresh_evar ()
        val e = open0_e_e y e
        val e = anf e
        val e = EAbs $ close0_e_e_anno ((y, fst name_y, t_y), e)
        val e = close_EAbsITs (binds, e)
        val e = ERec $ close0_e_e_anno ((x, fst name_x, t_x), e)
      in
        e
      end
    fun visit_ECase this env (e, bind1, bind2) =
      let
        fun on_bind bind =
          let
            val (name_x, e) = unBindSimpName bind
            val x = fresh_evar ()
            val e = open0_e_e x e
            val e = anf e
            val bind = EBind (name_x, close0_e_e x e)
          in
            bind
          end
        val e = #visit_expr (cast this) this env e
        val bind1 = on_bind bind1         
        val bind2 = on_bind bind2        
      in
        ECase (e, bind1, bind2)
      end
    (* this relies on form invariants after CPS *)
    fun visit_EAscTime this env (e, i) =
      let
        val e = anf e
      in
        EAscTime (e, i)
      end
    fun visit_EAppI this env (e, i) =
      let
        val (e, is) = collect_EAppI e
        val is = is
        val e = #visit_expr (cast this) this env e
        val e = EAppIs (e, is)
      in
        EAppI (e, i)
      end
    fun visit_expr this env e =
      let
        fun is_add_decl e =
          case e of
              ELet _ => false
            | EUnpack _ => false
            | EUnpackI _ => false
            | ERec bind => false
            | ECase _ => false
            | EConst _ => false
            | EVar _ => false
            | EAscType _ => false
            | EAscTime _ => false
            | EBinOp (EBApp, _, _) => false
            | EHalt _ => false
            | _ => true
        val add_decl = is_add_decl e
        val e = #visit_expr vtable this env e (* call super *)
      in
        if add_decl then
          let
            val x = fresh_evar ()
            val () = output $ DLet (x, "x", e)
          in
            EV x
          end
        else
          e
      end
    val vtable = override_visit_ELet vtable visit_ELet
    val vtable = override_visit_EUnpack vtable visit_EUnpack
    val vtable = override_visit_EUnpackI vtable visit_EUnpackI
    val vtable = override_visit_ERec vtable visit_ERec
    val vtable = override_visit_ECase vtable visit_ECase
    val vtable = override_visit_EAscTime vtable visit_EAscTime
    val vtable = override_visit_EAppI vtable visit_EAppI
    val vtable = override_visit_expr vtable visit_expr
  in
    vtable
  end

and new_anf_decls_expr_visitor params = new_expr_visitor anf_decls_expr_visitor_vtable params

and anf_decls output b =
  let
    val visitor as (ExprVisitor vtable) = new_anf_decls_expr_visitor output
  in
    #visit_expr vtable visitor () b
  end

and anf e =
    let
      val decls = ref []
      fun output d = push_ref decls d
      val e = anf_decls output e
      val decls = !decls
      val decls = rev decls
      val e = close_EDecls (decls, e)
    in
      e
    end

fun pair_alloc e =
  let
    val e = pa e
    val e = anf e
    val e = MicroTiMLExPostProcess.post_process e
  in
    e
  end

val pair_alloc_tc_flags =
    let
      open MicroTiMLTypecheck
    in
      [AnnoEPair]
    end
                     
structure UnitTest = struct

structure TestUtil = struct

open CPS
open CC
open LongId
open Util
open MicroTiML
open MicroTiMLVisitor
open MicroTiMLExLongId
open MicroTiMLEx
       
infixr 0 $
infixr 0 !!
         
fun short_to_long_id x = ID (x, dummy)
fun export_var (sel : 'ctx -> string list) (ctx : 'ctx) id =
  let
    fun unbound s = "__unbound_" ^ s
    (* fun unbound s = raise Impossible $ "Unbound identifier: " ^ s *)
  in
    case id of
        ID (x, _) =>
        short_to_long_id $ nth_error (sel ctx) x !! (fn () => unbound $ str_int x)
        (* short_to_long_id $ str_int x *)
      | QID _ => short_to_long_id $ unbound $ CanToString.str_raw_var id
  end
(* val export_i = return2 *)
fun export_i a = ToString.export_i Gctx.empty a
fun export_s a = ToString.export_s Gctx.empty a
fun export_t a = export_t_fn (export_var snd, export_i, export_s) a
fun export a = export_e_fn (export_var #4, export_var #3, export_i, export_s, export_t) a
val str = PP.string
fun str_var x = LongId.str_raw_long_id id(*str_int*) x
fun str_i a =
  (* ToStringRaw.str_raw_i a *)
  ToString.SN.strn_i a
  (* const_fun "<idx>" a *)
fun str_bs a =
  ToStringRaw.str_raw_bs a
fun str_s a =
  (* ToStringRaw.str_raw_s a *)
  ToString.SN.strn_s a
  (* const_fun "<sort>" a *)
fun pp_t_to s b =
  MicroTiMLPP.pp_t_to_fn (str_var, str_bs, str_i, str_s, const_fun "<kind>") s b
  (* str s "<ty>" *)
fun pp_t b = MicroTiMLPP.pp_t_fn (str_var, str_bs, str_i, str_s, const_fun "<kind>") b
fun pp_e a = MicroTiMLExPP.pp_e_fn (
    str_var,
    str_i,
    str_s,
    const_fun "<kind>",
    pp_t_to
  ) a
fun fail () = OS.Process.exit OS.Process.failure
                   
end

open TestUtil
       
fun test1 dirname =
  let
    val () = println "PairAlloc.UnitTest started"
    val filename = join_dir_file (dirname, "pair-alloc-test1.pkg")
    val filenames = ParseFilename.expand_pkg (fn msg => raise Impossible msg) filename
    open Parser
    val prog = concatMap parse_file filenames
    open Elaborate
    val prog = elaborate_prog prog
    open NameResolve
    val (prog, _, _) = resolve_prog empty prog
                                    
    open TypeCheck
    val () = TypeCheck.turn_on_builtin ()
    val () = println "Started TiML typechecking ..."
    val ((prog, _, _), (vcs, admits)) = typecheck_prog empty prog
    val vcs = VCSolver.vc_solver filename vcs
    val () = if null vcs then ()
             else
               raise curry TypeCheck.Error dummy $ (* str_error "Error" filename dummy *) [sprintf "Typecheck Error: $ Unproved obligations:" [str_int $ length vcs], ""] @ (
               (* concatMap (fn vc => str_vc true filename vc @ [""]) $ map fst vcs *)
               concatMap (VCSolver.print_unsat true filename) vcs
             )
    val () = println "Finished TiML typechecking"
                     
    open MergeModules
    val decls = merge_prog prog []
    open TiML2MicroTiML
    val e = SMakeELet (Teles decls, Expr.ETT dummy)
    val () = println "Simplifying ..."
    val e = SimpExpr.simp_e [] e
    val () = println "Finished simplifying"
    (* val () = println $ str_e empty ToStringUtil.empty_ctx e *)
    (* val () = println "" *)
    val () = println "Started translating ..."
    val e = trans_e e
    val () = println "Finished translating"
    (* val () = pp_e $ export ToStringUtil.empty_ctx e *)
    (* val () = println "" *)
                     
    open MicroTiMLTypecheck
    open TestUtil
    val () = println "Started MicroTiML typechecking #1 ..."
    val ((e, t, i), vcs, admits) = typecheck cps_tc_flags ([], [], [](* , HeapMap.empty *)) e
    val () = println "Finished MicroTiML typechecking #1"
    val () = println "Type:"
    val () = pp_t NONE $ export_t ([], []) t
    val () = println "Time:"
    val i = simp_i i
    val () = println $ ToString.str_i Gctx.empty [] i
    (* val () = println $ "#VCs: " ^ str_int (length vcs) *)
    (* val () = println "VCs:" *)
    (* val () = app println $ concatMap (fn ls => ls @ [""]) $ map (str_vc false "") vcs *)
    (* val () = pp_e $ export ToStringUtil.empty_ctx e *)
    (* val () = println "" *)
                     
    val () = println "Started CPS conversion ..."
    val (e, _) = cps (e, TUnit) (EHaltFun TUnit, T_0)
    (* val (e, _) = cps (e, TUnit) (Eid TUnit, T_0) *)
    val () = println "Finished CPS conversion"
    (* val () = pp_e $ export ToStringUtil.empty_ctx e *)
    (* val () = println "" *)
    val e_str = ExportPP.pp_e_to_string (NONE, NONE) $ export ToStringUtil.empty_ctx e
    val () = write_file ("pair-alloc-unit-test-after-cps.tmp", e_str)
    (* val () = println e_str *)
    (* val () = println "" *)
    val () = println "Started MicroTiML typechecking #2 ..."
    val ((e, t, i), vcs, admits) = typecheck cc_tc_flags ([], [], [](* , HeapMap.empty *)) e
    val () = println "Finished MicroTiML typechecking #2"
    val () = println "Type:"
    val () = pp_t NONE $ export_t ([], []) t
    val () = println "Time:"
    val i = simp_i i
    val () = println $ ToString.str_i Gctx.empty [] i
    (* val () = pp_e (NONE, NONE) $ export ToStringUtil.empty_ctx e *)
    (* val () = println "" *)
                     
    val () = println "Started CC ..."
    val e = cc e
    val () = println "Finished CC"
    (* val () = pp_e $ export ToStringUtil.empty_ctx e *)
    (* val () = println "" *)
    val e_str = ExportPP.pp_e_to_string (NONE, NONE) $ export ToStringUtil.empty_ctx e
    val () = write_file ("pair-alloc-unit-test-after-cc.tmp", e_str)
    (* val () = println e_str *)
    (* val () = println "" *)
    (* val () = println "Done" *)
    (* val () = println "Checking closed-ness of ERec's" *)
    (* val () = check_ERec_closed e *)
    val () = println "Started MicroTiML typechecking #3 ..."
    val ((e, t, i), vcs, admits) = typecheck pair_alloc_tc_flags ([], [], [](* , HeapMap.empty *)) e
    val () = println "Finished MicroTiML typechecking #3"
    val () = println "Type:"
    val () = pp_t NONE $ export_t ([], []) t
    val () = println "Time:"
    val i = simp_i i
    val () = println $ ToString.str_i Gctx.empty [] i
    val () = pp_e (NONE, NONE) $ export ToStringUtil.empty_ctx e
    val () = println ""
                     
    val () = println "Started Pair Alloc ..."
    (* val e = pa e *)
    val e = pair_alloc e
    val () = println "Finished Pair Alloc"
    (* val () = pp_e $ export ToStringUtil.empty_ctx e *)
    (* val () = println "" *)
    val e_str = ExportPP.pp_e_to_string (NONE, NONE) $ export ToStringUtil.empty_ctx e
    val () = write_file ("pair-alloc-unit-test-after-pair-alloc.tmp", e_str)
    val () = println e_str
    val () = println ""
    val () = println "Started post-pair-allocation form checking"
    val () = check_CPSed_expr e
    val () = println "Finished post-pair-allocation form checking"
    val () = println "Started MicroTiML typechecking #4 ..."
    val ((e, t, i), vcs, admits) = typecheck [] ([], [], [](* , HeapMap.empty *)) e
    val () = println "Finished MicroTiML typechecking #4"
    val () = println "Type:"
    val () = pp_t NONE $ export_t ([], []) t
    val () = println "Time:"
    val i = simp_i i
    val () = println $ ToString.str_i Gctx.empty [] i
                     
    val () = println "PairAlloc.UnitTest passed"
  in
    ((* t, e *))
  end
  handle MicroTiMLTypecheck.MTCError msg => (println $ "MTiMLTC.MTCError: " ^ substr 0 1000 msg; fail ())
       | TypeCheck.Error (_, msgs) => (app println $ "TC.Error: " :: msgs; fail ())
       | NameResolve.Error (_, msg) => (println $ "NR.Error: " ^ msg; fail ())
    
val test_suites = [
      test1
]
                            
end
                       
end
