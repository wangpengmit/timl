(* Code generation to TiTAL *)

structure CodeGen = struct

open CompilerUtil
open TiTAL

infixr 0 $
         
fun collect_ELetRec e =
  case e of
      ELet (e1, bind) =>
      (case fst $ collect_EAscType e1 of
           ERec bind1 =>
           let
             val (name, e) = unBindSimpName bind
             val (decls, e) = collect_ELetRec e
           in
             ((name, bind1) :: decls, e)
           end
         | _ => ([], e))
    | _ => ([], e)
             
structure RctxUtil = MapUtilFn (Rctx)

val rctx_single = RctxUtil.single
                    
infixr 5 @::
infixr 5 @@
infix  6 @+

fun m @+ a = Rctx.insert' (a, m)

fun cg_ty_visitor_vtable cast () =
  let
    fun visit_TArrow this env (data as (t1, i, t2)) =
      let
        val () = assert_TUnit "cg_t(): result type of TArrow must be TUnit" t2
        val cg_t = #visit_ty (cast this) this env
        val t1 = cg_t t1
      in
        TArrowTAL (rctx_single (1, t1), i)
      end
    val vtable =
        default_ty_visitor_vtable
          cast
          extend_noop
          extend_noop
          visit_noop
          visit_noop
          visit_noop
          visit_noop
    val vtable = override_visit_TArrow vtable visit_TArrow
  in
    vtable
  end

fun new_cg_ty_visitor a = new_ty_visitor cg_ty_visitor_vtable a
    
fun cg_t t =
  let
    val visitor as (TyVisitor vtable) = new_cg_ty_visitor ()
  in
    #visit_ty vtable visitor () t
  end
    
val reg_counter = ref 0
                      
fun fresh_reg () =
  let
    val v = !reg_counter
    val () = inc_ref reg_counter
  in
    v
  end

fun fresh_reg_until p =
  let
    val v = fresh_reg ()
  in
    if p v then v
    else fresh_reg_until p
  end
    
val label_counter = ref 0
                      
fun fresh_label () =
  let
    val v = !label_counter
    val () = inc_ref label_counter
  in
    v
  end

type idx = Expr.idx
type bsort = Expr.bsort
type sort = Expr.sort
type ty = (Expr.var, bsort, idx, sort) ty
type kind = bsort kind
                  
val heap_ref = ref ([] : (label * (idx, sort, kind, ty) hval) list)
fun output_heap pair = push_ref heap_ref pair
                                
fun cg_v ectx v =
  case v of
      EVar (ID (x, _)) =>
      (case nth_error ectx x of
           SOME (name, v) =>
           (case v of
                inl r => VReg r
              | inr l => VLabel l)
         | NONE => raise Impossible $ "no mapping for variable " ^ str_int x)
    | EConst c => VConst c
    | EAppT (v, t) => VAppT (cg_v ectx v, cg_t t)
    | EAppI (v, i) => VAppI (cg_v ectx v, i)
    | EPack (t_pack, t, v) => VPack (cg_t t_pack, cg_t t, cg_v ectx v)
    | EPackI (t_pack, i, v) => VPackI (cg_t t_pack, i, cg_v ectx v)
    | EUnOp (EUFold t, v) => VFold (cg_t t, cg_v ectx v)
    | ENever t => VNever $ cg_t t
    | EBuiltin t => VBuiltin $ cg_t t
    | _ =>
      let
        val ectxn = map (fst o fst) ectx
      in
        raise Impossible $ "cg_v() on:\n" ^ (ExportPP.pp_e_to_string (NONE, NONE) $ ExportPP.export (NONE, NONE) ([], [], [], ectxn) v)
      end

fun cg_e (params as (ectx, itctx, rctx)) e =
  let
    (* val () = print $ "cg_e() started:\n" *)
    val ectxn = map (fst o fst) ectx
    fun split_inl_inr ls = foldr (fn (s, (acc1, acc2)) =>
                                     case s of
                                         inl a => (a :: acc1, acc2)
                                       | inr a => (acc1, a :: acc2)) ([], []) ls
    val (ictxn, tctxn) = mapPair (map $ fst o fst, map $ fst o fst) $ split_inl_inr itctx
    (* val e_str = ExportPP.pp_e_to_string (NONE, NONE) $ ExportPP.export (SOME 2, SOME 3) (ictxn, tctxn, [], ectxn) e *)
    (* val () = println $ e_str *)
    fun main () =
  case e of
      ELet (e1, bind) =>
      let
        val (e1, t) = assert_EAscType e1
        val t = cg_t t
        val r = fresh_reg ()
        val I1 =
            case fst $ collect_EAscType e1 of
                EProjProtected (proj, v) =>
                [IMov' (r, cg_v ectx v),
                 ILd (r, (r, proj))]
              | EBinOp (EBPrim opr, v1, v2) =>
                [IMov' (r, cg_v ectx v1),
                 IBinOp' (IBPrim opr, r, r, cg_v ectx v2)]
              | EBinOp (EBNatAdd, v1, v2) =>
                [IMov' (r, cg_v ectx v1),
                 IBinOp' (IBNatAdd, r, r, cg_v ectx v2)]
              | EBinOp (EBNew, v1, v2) =>
                [IMov' (r, cg_v ectx v1),
                 IBinOp' (IBNew, r, r, cg_v ectx v2)]
              | EBinOp (EBRead, v1, v2) =>
                [IMov' (r, cg_v ectx v1),
                 IBinOp' (IBRead, r, r, cg_v ectx v2)]
              | EWrite (v1, v2, v3) =>
                let
                  val r' = fresh_reg ()
                in
                  [IMov' (r, cg_v ectx v1),
                   IMov' (r', cg_v ectx v2),
                   IBinOp' (IBWrite, r, r', cg_v ectx v3)]
                end
              | EUnOp (EUInj (inj, _), v) =>
                [IInj' (r, inj, cg_v ectx v)]
              | EUnOp (EUUnfold, v) =>
                [IUnfold' (r, cg_v ectx v)]
              | EMallocPair (v1, v2) =>
                [IMallocPair' (r, (cg_v ectx v1, cg_v ectx v2))]
              | EPairAssign (v1, proj, v2) =>
                let
                  val r' = fresh_reg ()
                in
                  [IMov' (r, cg_v ectx v1),
                   IMov' (r', cg_v ectx v2),
                   ISt ((r, proj), r')]
                end
              | v => [IMov' (r, cg_v ectx v)]
        val (name, e2) = unBindSimpName bind
        val I = cg_e ((name, inl r) :: ectx, itctx, rctx @+ (r, t)) e2
      in
        I1 @@ I
      end
    | EUnpack (v, bind) =>
      let
        val (v, t) = assert_EAscType v
        val ((_, k), t) = assert_TExists t
        val t = cg_t t
        val (name_x, bind) = unBindSimpName bind
        val (name_a, e2) = unBindSimpName bind
        val r = fresh_reg ()
        val i = IUnpack' (name_a, r, cg_v ectx v)
        val I = cg_e ((name_x, inl r) :: ectx, inr (name_a, k) :: itctx, rctx @+ (r, t)) e2
      in
        i @:: I
      end
    | EUnpackI (v, bind) =>
      let
        val (v, t) = assert_EAscType v
        val ((_, s), t) = assert_TExistsI t
        val t = cg_t t
        val (name_x, bind) = unBindSimpName bind
        val (name_a, e2) = unBindSimpName bind
        val r = fresh_reg ()
        val i = IUnpackI' (name_a, r, cg_v ectx v)
        val I = cg_e ((name_x, inl r) :: ectx, inl (name_a, s) :: itctx, rctx @+ (r, t)) e2
      in
        i @:: I
      end
    | EBinOp (EBApp, v1, v2) =>
      let
        val r = fresh_reg_until (fn r => r <> 1)
      in
        IMov' (r, cg_v ectx v1) @::
        IMov' (1, cg_v ectx v2) @::
        ISJmp (VReg r)
      end
    | ECase (v, bind1, bind2) =>
      let
        val (v, t) = assert_EAscType v
        val t = cg_t t
        val (t1, t2) = assert_TSum t
        val (name1, e1) = unBindSimpName bind1
        val (name2, e2) = unBindSimpName bind2
        val (e2, i_e2) = assert_EAscTime e2
        val r = fresh_reg ()
        val v = cg_v ectx v
        val I1 = cg_e ((name1, inl r) :: ectx, itctx, rctx @+ (r, t1)) e1
        val rctx2 = rctx @+ (r, t2)
        val I2 = cg_e ((name2, inl r) :: ectx, itctx, rctx2) e2
        val itbinds = rev itctx
        val hval = HCode' (itbinds, ((rctx2, i_e2), I2))
        val l = fresh_label ()
        val () = output_heap (l, hval)
        fun VAppITs_ctx (e, itctx) =
          let
            fun IV n = VarI (ID (n, dummy), [])
            fun TV n = TVar (ID (n, dummy), [])
            val itargs = fst $ foldl
                             (fn (bind, (acc, (ni, nt))) =>
                                 case bind of
                                     inl _ => (inl (IV ni) :: acc, (ni+1, nt))
                                   | inr _ => (inr (TV nt) :: acc, (ni, nt+1))
                             ) ([], (0, 0)) itctx
          in
            VAppITs (e, itargs)
          end
      in
        IMov' (r, v) @::
        IBr' (r, VAppITs_ctx (VLabel l, itctx)) @::
        I1
      end
    | EHalt v =>
      let
        val (v, t) = assert_EAscType v
        val t = cg_t t
      in
        IMov' (1, cg_v ectx v) @::
        ISHalt t
      end
    | EAscTime (e, i) => IAscTime' i @:: cg_e params e
    | EAscType (e, _) => cg_e params e
    | _ => raise Impossible $ "cg_e() on:\n" ^ (ExportPP.pp_e_to_string (NONE, NONE) $ ExportPP.export (NONE, NONE) ([], [], [], []) e)
    fun extra_msg () = "\nwhen code-gen-ing:\n" ^ (ExportPP.pp_e_to_string (NONE, NONE) $ ExportPP.export (SOME 1, SOME 5) (ictxn, tctxn, [], ectxn) e)
    val ret = main ()
              handle Impossible m => raise Impossible (m ^ extra_msg ())
    (* val () = println $ "cg_e() finished:\n" ^ e_str *)
  in
    ret
  end
        
                       
(* ectx: variable mapping, maps variables to registers or labels *)
fun cg_hval ectx (e, t_all) =
  let
    val (itbinds, e) = collect_EAbsIT e
    val (t, (name, e)) = assert_EAbs e
    val t = cg_t t
    (* input argument is always stored in r1 *)
    val ectx = (name, inl 1) :: ectx
    val rctx = rctx_single (1, t)
    val I = cg_e (ectx, rev itbinds, rctx) e
    fun get_time t =
      let
        val (_, t) = collect_TForallIT t
        val (_, i, _) = assert_TArrow t
      in
        i
      end
    val hval = HCode' (itbinds, ((rctx, get_time t_all), I))
  in
    hval
  end
  
fun cg_prog e =
  let
    val () = heap_ref := []
    val (binds, e) = collect_ELetRec e
    val len = length binds
    fun on_bind ((_, bind), ectx) =
      let
        val (t, (name, e)) = unBindAnnoName bind
        val () = println $ "cg() on " ^ fst name
        (* val t = cg_t t *)
        val l = fresh_label ()
        val ectx = (name, inr l) :: ectx
        val hval = cg_hval ectx (e, t)
        val () = output_heap (l, hval)
      in
        ectx
      end
    val ectx = foldl on_bind [] binds
    val I = cg_e (ectx, [], Rctx.empty) e
    val H = !heap_ref
  in
    (H, I)
  end

val code_gen_tc_flags =
    let
      open MicroTiMLTypecheck
    in
      [Anno_ELet, Anno_EUnpack, Anno_EUnpackI, Anno_ECase, Anno_EHalt, Anno_ECase_e2_time]
    end
                     
structure UnitTest = struct

structure TestUtil = struct

open CPS
open CC
open PairAlloc
open LongId
open Util
open MicroTiML
open MicroTiMLVisitor
open MicroTiMLExLongId
open MicroTiMLEx
       
infixr 0 $
infixr 0 !!
         
fun fail () = OS.Process.exit OS.Process.failure
                   
end

open TestUtil
       
fun test1 dirname =
  let
    val () = println "CodeGen.UnitTest started"
    val filename = join_dir_file (dirname, "code-gen-test1.pkg")
    val filenames = map snd $ ParseFilename.expand_pkg (fn msg => raise Impossible msg) (true, filename)
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
    open ExportPP
    val () = pp_t NONE $ export_t (SOME 1) ([], []) t
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
    val e_str = ExportPP.pp_e_to_string (NONE, NONE) $ export (SOME 1, NONE) ToStringUtil.empty_ctx e
    val () = write_file ("unit-test-after-cps.tmp", e_str)
    (* val () = println e_str *)
    (* val () = println "" *)
    val () = println "Started MicroTiML typechecking #2 ..."
    val ((e, t, i), vcs, admits) = typecheck cc_tc_flags ([], [], [](* , HeapMap.empty *)) e
    val () = println "Finished MicroTiML typechecking #2"
    val () = println "Type:"
    val () = pp_t NONE $ export_t (SOME 1) ([], []) t
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
    val e_str = ExportPP.pp_e_to_string (NONE, NONE) $ export (SOME 1, NONE) ToStringUtil.empty_ctx e
    val () = write_file ("unit-test-after-cc.tmp", e_str)
    (* val () = println e_str *)
    (* val () = println "" *)
    (* val () = println "Done" *)
    (* val () = println "Checking closed-ness of ERec's" *)
    (* val () = check_ERec_closed e *)
    val () = println "Started MicroTiML typechecking #3 ..."
    val ((e, t, i), vcs, admits) = typecheck pair_alloc_tc_flags ([], [], [](* , HeapMap.empty *)) e
    val () = println "Finished MicroTiML typechecking #3"
    val () = println "Type:"
    val () = pp_t NONE $ export_t (SOME 1) ([], []) t
    val () = println "Time:"
    val i = simp_i i
    val () = println $ ToString.str_i Gctx.empty [] i
    (* val () = pp_e (NONE, NONE) $ export ((* (SOME 1) *)NONE, NONE) ToStringUtil.empty_ctx e *)
    (* val () = println "" *)
                     
    val () = println "Started Pair Alloc ..."
    (* val e = pa e *)
    val e = pair_alloc e
    val () = println "Finished Pair Alloc"
    (* val () = pp_e $ export ToStringUtil.empty_ctx e *)
    (* val () = println "" *)
    val e_str = ExportPP.pp_e_to_string (NONE, NONE) $ export ((* SOME 1 *)NONE, NONE) ToStringUtil.empty_ctx e
    val () = write_file ("unit-test-after-pair-alloc.tmp", e_str)
    val () = println e_str
    val () = println ""
    val () = println "Started post-pair-allocation form checking"
    val () = check_CPSed_expr e
    val () = println "Finished post-pair-allocation form checking"
    val () = println "Started MicroTiML typechecking #4 ..."
    val ((e, t, i), vcs, admits) = typecheck code_gen_tc_flags ([], [], []) e
    val () = println "Finished MicroTiML typechecking #4"
    val () = println "Type:"
    val () = pp_t NONE $ export_t (SOME 1) ([], []) t
    val () = println "Time:"
    val i = simp_i i
    val () = println $ ToString.str_i Gctx.empty [] i
                     
    val () = println "Started Code Generation ..."
    (* val e = pa e *)
    val P as (H, I) = cg_prog e
    val () = println "Finished Code Generation"
    (* val () = pp_e $ export ToStringUtil.empty_ctx e *)
    (* val () = println "" *)
    (* val e_str = ExportPP.pp_e_to_string (NONE, NONE) $ export ((* SOME 1 *)NONE, NONE) ToStringUtil.empty_ctx e *)
    (* val () = write_file ("unit-test-after-code-gen.tmp", e_str) *)
    (* val () = println e_str *)
    (* val () = println "" *)
    (* val () = println "Started MicroTiML typechecking #4 ..." *)
    (* val ((e, t, i), vcs, admits) = typecheck [] ([], [], [](* , HeapMap.empty *)) e *)
    (* val () = println "Finished MicroTiML typechecking #4" *)
    (* val () = println "Type:" *)
    (* val () = pp_t NONE $ export_t (SOME 1) ([], []) t *)
    (* val () = println "Time:" *)
    (* val i = simp_i i *)
    (* val () = println $ ToString.str_i Gctx.empty [] i *)
                     
    val () = println "CodeGen.UnitTest passed"
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
