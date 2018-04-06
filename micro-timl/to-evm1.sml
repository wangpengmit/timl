(* Code generation to TiTAL *)

structure ToEVM1 = struct

open CompilerUtil
open EVM1

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
             
val rctx_single = RctxUtil.single
                    
infixr 5 @::
infixr 5 @@
infix  6 @+
infix  9 @!

fun cg_ty_visitor_vtable cast () =
  let
    fun visit_TArrow this env (data as (t1, i, t2)) =
      let
        val () = assert_TUnit "cg_t(): result type of TArrow must be TUnit" t2
        val cg_t = #visit_ty (cast this) this env
        val t1 = cg_t t1
      in
        TArrowTAL (rctx_single (0, t1), i)
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
                  
val heap_ref = ref ([] : ((label * string) * (idx, sort, kind, ty) hval) list)
fun output_heap pair = push_ref heap_ref pair

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

(* fun get_reg r = [PUSH_REG $ RegAddr r, MLOAD] *)
val array_ptr = [PUSH1 $ WCNat 32, MUL, ADD]

fun cg_c c =
  case c of
      ECTT => WCTT
    | ECNat n => WCNat n
    | ECInt n => WCInt n
    | ECBool n => WCBool n
    | ECString s => raise Impossible $ "cg_c() on ECString"
                                
fun impl_prim_expr_un_opr opr =
  case opr of
      EUPIntNeg => [PUSH1 0, SUB]
    | EUPBoolNeg => [ISZERO]
    | EUPStrLen => [PUSH1 32, SWAP1, SUB, MLOAD]
    | _ => raise Impossible $ "impl_prim_expr_up_op() on " ^ str_prim_expr_un_op opr
      
fun impl_prim_expr_bin_op opr =
  case opr of
       EBPIntAdd => [ADD]
     | EBPIntMul => [MUL]
     | EBPIntMinus => [SWAP1, SUB]
     | EBPIntDiv => [SWAP1, SDIV]
     | EBPIntLt => [SWAP1, LT]
     | EBPIntGt => [SWAP1, GT]
     | EBPIntLe => [GT, ISZERO]
     | EBPIntGe => [LT, ISZERO]
     | EBPIntEq => [EQ]
     | EBPIntNEq => [EQ, ISZERO]
     | EBPBoolAnd => [AND]
     | EBPBoolOr => [OR]
     | EBPStrConcat => raise Impossible "impl_prim_expr_bin_op() on EBPStrConcat"
                  
fun impl_expr_un_op opr =
  case opr of
      EUPrim opr => impl_prim_expr_un_opr opr
    | EUNat2Int => [NAT2INT]
    | EUPrint => [PRINT]
    | EUArrayLen => [PUSH1 32, SWAP1, SUB, MLOAD]
    | EUProj proj => [PUSH_tuple_offset $ 32 * choose (0, 1) proj, ADD, MLOAD]
                        
fun impl_nat_expr_bin_op opr =
  case opr of
      EBNAdd => [ADD]
    | EBNMult => [MUL]
    | EBNDiv => [SWAP1, DIV]
    | EBNMinus => [SWAP1, SUB]
    | EBNBoundedMinus => raise Impossible "impl_nat_expr_bin_op() on EBNBoundedMinus"

fun impl_nat_cmp opr =
  case opr of
     NCLt => [SWAP1, LT]
   | NCGt => [SWAP1, GT]
   | NCLe => [GT, ISZERO]
   | NCGe => [LT, ISZERO]
   | NCEq => [EQ]
   | NCNEq => [EQ, ISZERO]
      
fun compile ectx e =
  let
    val compile = compile ectx
  in
  case e of
      EBinOp (EBPrim opr, e1, e2) =>
      compile e1 @ compile e2 @ impl_prim_expr_bin_op opr
    | EVar (ID (x, _)) =>
      (case nth_error ectx x of
           SOME (name, v) =>
           (case v of
                inl r => get_reg r
              | inr l => [PUSH_value $ VLabel l])
         | NONE => raise Impossible $ "no mapping for variable " ^ str_int x)
    | EConst c => [PUSH_value $ VConst $ cg_c c]
    | EAppT (e, t) => compile e @ VALUE_VAppT (cg_t t)
    | EAppI (e, i) => compile e @ VALUE_VAppI i
    | EPack (t_pack, t, e) => compile e @ VALUE_VPack (cg_t t_pack, cg_t t)
    (* | EPackI (t_pack, i, v) => VPackI (cg_t t_pack, i, cg_v ectx v) *)
    | EUnOp (EUFold t, e) => compile e @ [VALUE_VFold $ cg_t t]
    | EAscType (e, t) => compile e @ VALUE_VAscType (cg_t t)
    | ENever t => [PUSH_value $ VNever $ cg_t t]
    | EBuiltin (name, t) => [PUSH_value $ VBuiltin (name, cg_t t)]
    | EBinOp (EBPair, e1, e2) =>
      let
        val (e1, t1) = assert_EAscType e1
        val (e2, t2) = assert_EAscType e2
        val t1 = cg_t t1
        val t2 = cg_t t2
      in
        compile e1 @ compile e2 @ malloc_tuple [t1, t2] @ [PUSH_tuple_offset (2*32), ADD] @ concat $ repeat 2 [PUSH1 32, SWAP1, SUB, SWAP1] @ tuple_assign
      end
    | EUnOp (EUInj (inj, t_other), e) =>
      let
        val (e, t_e) = assert_EAscType e
        val t_e = cg_t t_e
        val t_other = cg_t t_other
        val b = choose_inj (false, true) inj
      in
        compile e @ malloc_tuple [TiBool $ ICBool b, t_e] @ [PUSH1 b, DUP2, MSTORE, SWAP1, DUP2, PUSH1 32, ADD, MSTORE, PACK_SUM (inj, t_other)]
      end
    | EEmptyArray t =>
      PUSH1 0 :: malloc_array $ cg_t t
    | ENewArrayValues es =>
      let
        val n = length es
      in
        [PUSH_tuple_offset n] @
        malloc_array @
        [DUP1] @
        map (fn e => compile e @ [DUP2, MSTORE, PUSH1 32, ADD]) es @
        [POP]
      end
    | EBinOp (EBRead, e1, e2) =>
      compile e1 @
      compile e2 @
      array_ptr @
      MLOAD
    | ETriOp (ETWrite, e1, e2, e3) =>
      compile e1 @
      compile e2 @
      compile e3 @
      [SWAP2, SWAP1] @
      array_ptr @
      MSTORE
    | EUnOp (EUUnfold, e) =>
      compile e @ [UNFOLD]
    | EUnOp (EUTiML opr, e) =>
      compile e @ impl_expr_un_opr opr
    | EBinOp (EBNat opr, e1, e2) =>
      compile e1 @ 
      compile e2 @
      impl_nat_expr_bin_op opr
    | EBinOp (EBNatCmp opr, v1, v2) =>
      compile e1 @ 
      compile e2 @
      impl_nat_cmp opr
  end

fun cg_e reg_counter (params as (ectx, itctx, rctx)) e =
  let
    (* val () = print $ "cg_e() started:\n" *)
    val cg_e = cg_e reg_counter
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
      (case e1 of
          EBinOp (EBNew, e1, e2) =>
          let
            val (e1, t_e1) = assert_EAscType e1
            val len = assert_TNat t_e1
            val (e2, t) = assert_EAscType e2
            val t = cg_t t
            val (name, e) = unBindSimpName bind
            val (e, i_e) = assert_EAscTime e
            val post_loop_label = fresh_label ()
            val loop_label = fresh_label ()
            val pre_loop_code =
                [SWAP1, DUP1] @
                malloc_array t @
                [SWAP1, PUSH1 32, MUL, PUSH_value $ VAppITs (VAppITs_ctx (VLabel loop_label, itctx), [inl len]), JUMP]
            (* val pre_loop_label = fresh_label () *)
            (* val pre_loop_block = *)
            (*     let *)
            (*     in *)
            (*       HCode' ([inr ("t", KType), inl ("j", STime), inl ("len", SNat)], ((rctx, [TNat T0, TPreArray (t, len, T0), t], T1 %+ i_e), post_loop_code)) *)
            (*     end *)
            val loop_block =
                let
                  val s = Subset ("i", Nat, IV 0 %<= shift01_i_i len)
                  val i = fresh_ivar ()
                  val loop_code = [DUP1, ISZERO, PUSH_value $ VAppITs_ctx (VLabel post_loop_label, itctx), JUMPI, PUSH1 32, SWAP1, SUB] @ array_assign @ [PUSH_value $ VAppITs (VAppITs_ctx (VLabel loop_label, itctx), [inl $ i %- N1]), JUMP]
                  val block = ((rctx, [TNat (ConstIN 32 %* i), TPreArray (t, len, i), t], ToReal (i %* ConstIN 8) + T1 %+ i_e), loop_code)
                  val block = close0_i_block i block
                in
                  HCode' (rev $ inl ("i", s) :: itctx, block)
                end
            val () = output_heap ((l, "new_array_loop"), loop_block)
            val post_loop_block =
                let
                  val r = fresh_reg ()
                  val post_loop_code = [POP, SWAP1, POP] @ set_reg r @ cg_e ((name, inl r) :: ectx, itctx, rctx @+ (r, TArrow (t, len))) e
                in
                  HCode' (rev itctx, ((rctx, [TNat T0, TPreArray (t, len, T0), t], T1 %+ i_e), post_loop_code))
                end
            val () = output_heap ((l, "new_array_post_loop"), post_loop_block)
          in
            compile e1 @
            compile e2 @
            pre_loop_code
          end
        | _ =>
          let
            val (e1, t) = assert_EAscType e1
            val t = cg_t t
            val (name, e2) = unBindSimpName bind
            val I = cg_e ((name, inl r) :: ectx, itctx, rctx @+ (r, t)) e2
          in
            compile e1 @ set_reg r @ I
          end)
    | EUnpack (e1, bind) =>
      let
        val (e1, t) = assert_EAscType e1
        val ((_, k), t) = assert_TExists t
        val t = cg_t t
        val (name_a, bind) = unBindSimpName bind
        val (name_x, e2) = unBindSimpName bind
        val r = fresh_reg ()
        val I = cg_e ((name_x, inl r) :: ectx, inr (name_a, k) :: itctx, Rctx.map shift01_t_t rctx @+ (r, t)) e2
      in
        compile e1 @ [UNPACK] @ set_reg r @ I
      end
    (* | EUnpackI (v, bind) => *)
    (*   let *)
    (*     val (v, t) = assert_EAscType v *)
    (*     val ((_, s), t) = assert_TExistsI t *)
    (*     val t = cg_t t *)
    (*     val (name_a, bind) = unBindSimpName bind *)
    (*     val (name_x, e2) = unBindSimpName bind *)
    (*     val r = fresh_reg () *)
    (*     val i = IUnpackI' (name_a, r, cg_v ectx v) *)
    (*     val I = cg_e ((name_x, inl r) :: ectx, inl (name_a, s) :: itctx, Rctx.map shift01_i_t rctx @+ (r, t)) e2 *)
    (*   in *)
    (*     i @:: I *)
    (*   end *)
    | EBinOp (EBApp, e1, e2) =>
      compile e1 @ compile e2 @ set_reg 0 @ [JUMP]
    | ECase (e, bind1, bind2) =>
      let
        val (e, t) = assert_EAscType e
        val t = cg_t t
        val (t1, t2) = assert_TSum t
        val (name1, e1) = unBindSimpName bind1
        val (name2, e2) = unBindSimpName bind2
        val (e2, i_e2) = assert_EAscTime e2
        val r = fresh_reg ()
        val I1 = cg_e ((name1, inl r) :: ectx, itctx, rctx @+ (r, t1)) e1
        val I2 = cg_e ((name2, inl r) :: ectx, itctx, rctx @+ (r, t2)) e2
        val branch_prelude = [PUSH1 32, ADD, MLOAD] @ set_reg r
        val itbinds = rev itctx
        val hval = HCode' (itbinds, ((rctx, [TProd (TiBool TrueI, t2)](*the stack spec*), i_e2), branch_prelude @ I2))
        val l = fresh_label ()
        val () = output_heap ((l, "inr_branch"), hval)
      in
        compile e @
        [PUSH_value $ VAppITs_ctx (VLabel l, itctx)] @
        br_sum @
        branch_prelude @
        I1
      end
    | ETriOp (ETIte, e, e1, e2) =>
      let
        val (e2, i_e2) = assert_EAscTime e2
        val I1 = cg_e (ectx, itctx, rctx) e1
        val I2 = cg_e (ectx, itctx, rctx) e2
        val itbinds = rev itctx
        val hval = HCode' (itbinds, ((rctx, [], i_e2), I2))
        val l = fresh_label ()
        val () = output_heap ((l, "else_branch"), hval)
      in
        compile e @
        [PUSH_value $ VAppITs_ctx (VLabel l, itctx)] @
        JUMPI @
        I1
      end
    | EHalt e =>
      let
        val (e, t) = assert_EAscType e
        val t = cg_t t
      in
        compile e @ [PUSH1 32, SWAP1, RETURN (* t *)]
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
    val ectx = (name, inl 0) :: ectx
    val rctx = rctx_single (0, t)
    val I = cg_e (ref 1) (ectx, rev itbinds, rctx) e
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
        val () = output_heap ((l, fst name), hval)
      in
        ectx
      end
    val ectx = foldl on_bind [] binds
    val I = cg_e (ref 0) (ectx, [], Rctx.empty) e
    val H = !heap_ref
    val H = rev H
  in
    (H, I)
  end

val code_gen_tc_flags =
    let
      open MicroTiMLTypecheck
    in
      [Anno_ELet, Anno_EUnpack, Anno_EUnpackI, Anno_ECase, Anno_EHalt, Anno_ECase_e2_time, Anno_EIte_e2_time]
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
    (* val i = simp_i i *)
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
    (* val i = simp_i i *)
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
    (* val i = simp_i i *)
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
    (* val i = simp_i i *)
    val () = println $ ToString.str_i Gctx.empty [] i
                     
    open TiTALExportPP
    val () = println "Started Code Generation ..."
    val prog = cg_prog e
    val () = println "Finished Code Generation"
    val prog_str = TiTALExportPP.pp_prog_to_string $ export_prog ((* SOME 1 *)NONE, NONE, NONE) prog
    val () = write_file ("unit-test-after-code-gen.tmp", prog_str)
    val () = println prog_str
    val () = println ""
    open TiTALTypecheck
    val () = println "Started TiTAL typechecking ..."
    val (i, vcs, admits) = tital_typecheck prog
    val () = println "Finished TiTAL typechecking"
    val () = println "Time:"
    (* val i = simp_i i *)
    val () = println $ ToString.str_i Gctx.empty [] i

    open TiTALEval
    val (H, I) = prog
    fun get_max_k H = max_ls ~1 $ map (fst o fst) H
    val P = ((RctxUtil.fromList $ map (fn ((l, _), c) => (l, HVCode c)) H, get_max_k H), (Rctx.empty, 0), I)
    val () = println "Started TiTAL evaluation"              
    val w = eval P
    val () = assert_WVTT w
    val () = println "Finished TiTAL evaluation"              
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
