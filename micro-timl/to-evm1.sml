(* Code generation to EVM1 *)

structure ToEVM1 = struct

open Expr
open CompilerUtil
open EVM1Visitor
open EVM1

infixr 0 $
         
infix 9 %@
infix 8 %^
infix 7 %*
infix 6 %+ 
infix 4 %<=
infix 4 %<
infix 4 %>=
infix 4 %>
infix 4 %=
infixr 3 /\
infixr 2 \/
infixr 1 -->
infix 1 <->

infix 6 %-
fun a %- b = BinOpI (BoundedMinusI, a, b)
        
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

fun close_i_insts a = shift_i_insts_fn (close_i_i, close_i_s, close_i_t) a
fun close_t_insts a = shift_t_insts_fn close_t_t a

fun close0_i_insts a = close_i_insts 0 a
fun close0_t_insts a = close_t_insts 0 a

fun cg_ty_visitor_vtable cast () =
  let
    fun visit_TArrow this env (data as (t1, i, t2)) =
      let
        val () = assert_TUnit "cg_t(): result type of TArrow must be TUnit" t2
        val cg_t = #visit_ty (cast this) this env
        val t1 = cg_t t1
      in
        TArrowEVM (rctx_single (1, t1), [], i)
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

fun IV n = VarI (ID (n, dummy), [])
fun TV n = TVar (ID (n, dummy), [])
fun FIV x = VarI (make_Free_i x, [])
val T0 = T0 dummy
val T1 = T1 dummy
val N1 = N1 dummy
                
fun VAppITs_ctx (e, itctx) =
  let
    val itargs = fst $ foldl
                     (fn (bind, (acc, (ni, nt))) =>
                         case bind of
                             inl _ => (inl (IV ni) :: acc, (ni+1, nt))
                           | inr _ => (inr (TV nt) :: acc, (ni, nt+1))
                     ) ([], (0, 0)) itctx
  in
    VAppITs (e, itargs)
  end

fun reg_addr r = 32 * (r + 1)
(* use r0 as scratch space *)
(* val scratch = 32 *)
val scratch = reg_addr 0
fun get_reg r = [PUSH_reg $ reg_addr r, MLOAD]
fun set_reg r = [PUSH_reg $ reg_addr r, MSTORE]
val array_ptr = [PUSH1nat 32, MUL, ADD]
fun malloc_tuple ts = [PUSH1nat 0, MLOAD, DUP1, PUSH_tuple_offset $ 32 * (length ts), ADD, PUSH1 $WNat 0, MSTORE]
fun malloc_array t = [PUSH1nat 0, MLOAD, DUP2, DUP2, MSTORE, PUSH1nat 32, ADD, DUP1, SWAP2, PUSH1nat 32, MUL, ADD, PUSH1nat 0, MSTORE]
val tuple_assign = [DUP2, MSTORE]
val array_assign = [DUP3, DUP3, DUP3, ADD, MSTORE]
val br_sum = [DUP2, MLOAD, SWAP1, JUMPI]
(* val int2byte = [] (* noop, relying on type discipline *) *)
val int2byte = [PUSH1nat 31, BYTE]
val byte2int = [BYTE2INT]
(* val printc = [PRINTC] *)
val printc = [PUSH_reg scratch, MSTORE, PUSH1nat 1, PUSH_reg scratch, PUSH1nat 31, ADD, LOG0, PUSH1 WTT]
fun impl_inj t_tuple inj t_other =
  malloc_tuple t_tuple @
  [SWAP1, DUP2, MSTORE, SWAP1, DUP2, PUSH1nat 32, ADD, MSTORE(* , PACK_SUM (inj, Inner t_other) *)]
fun halt t =
  [PUSH_reg scratch, SWAP1, DUP2, MSTORE, PUSH1nat 32, SWAP1] @@ RETURN (* t *)

fun impl_nat_cmp opr =
  let
    val cmp =
        case opr of
            NCLt => [GT] (* a<b <-> b>a *)
          | NCGt => [LT]
          | NCLe => [LT, ISZERO] (* a<=b <-> ~(a>b) <-> ~(b<a) *)
          | NCGe => [GT, ISZERO]
          | NCEq => [EQ]
          | NCNEq => [EQ, ISZERO]
  in
    cmp @ [ISZERO, PUSH1 WTT, SWAP1] @ impl_inj [TUnit, TUnit] InjInl TUnit
  end
      
fun concatRepeat n v = List.concat $ repeat n v
fun TiBoolConst b =
  TiBool $ IConst (ICBool b, dummy)
               
fun cg_c c =
  case c of
      ECTT => WCTT
    | ECNat n => WCNat n
    | ECInt n => WCInt n
    | ECBool n => WCBool n
    | ECByte c => WCByte c
    (* | ECString s => raise Impossible $ "cg_c() on ECString" *)
                                
fun impl_prim_expr_un_opr opr =
  case opr of
      EUPIntNeg => [PUSH1 $ WInt 0, SUB]
    | EUPBoolNeg => [ISZERO]
    | EUPInt2Byte => int2byte
    | EUPByte2Int => byte2int
    (* | EUPStrLen => [PUSH1nat 32, SWAP1, SUB, MLOAD] *)
    (* | _ => raise Impossible $ "impl_prim_expr_up_op() on " ^ str_prim_expr_un_op opr *)
      
fun impl_prim_expr_bin_op opr =
  case opr of
       EBPIntAdd => [ADD]
     | EBPIntMult => [MUL]
     | EBPIntMinus => [SWAP1, SUB]
     | EBPIntDiv => [SWAP1, SDIV]
     | EBPIntMod => [SWAP1, MOD]
     | EBPIntLt => [SWAP1, LT]
     | EBPIntGt => [SWAP1, GT]
     | EBPIntLe => [GT, ISZERO]
     | EBPIntGe => [LT, ISZERO]
     | EBPIntEq => [EQ]
     | EBPIntNEq => [EQ, ISZERO]
     | EBPBoolAnd => [AND]
     | EBPBoolOr => [OR]
     (* | EBPStrConcat => raise Impossible "impl_prim_expr_bin_op() on EBPStrConcat" *)
                  
fun impl_expr_un_op opr =
  case opr of
      EUPrim opr => impl_prim_expr_un_opr opr
    | EUNat2Int => [NAT2INT]
    | EUInt2Nat => [INT2NAT, VALUE_Fold $ Inner $ TSomeNat ()]
    | EUArrayLen => [PUSH1nat 32, SWAP1, SUB, MLOAD]
    | EUProj proj => [PUSH_tuple_offset $ 32 * choose (0, 1) proj, ADD, MLOAD]
    | EUPrintc => printc
    (* | EUPrint => [PRINT] *)
                        
fun impl_nat_expr_bin_op opr =
  case opr of
      EBNAdd => [ADD]
    | EBNMult => [MUL]
    | EBNDiv => [SWAP1, DIV]
    | EBNBoundedMinus => [SWAP1, SUB]

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
              | inr l => PUSH_value $ VLabel l)
         | NONE => raise Impossible $ "no mapping for variable " ^ str_int x)
    | EConst c => PUSH_value $ VConst $ cg_c c
    | EAppT (e, t) => compile e @ [VALUE_AppT $ Inner $ cg_t t]
    | EAppI (e, i) => compile e @ [VALUE_AppI $ Inner i]
    | EPack (t_pack, t, e) => compile e @ [VALUE_Pack (Inner $ cg_t t_pack, Inner $ cg_t t)]
    | EPackI (t_pack, i, e) => compile e @ [VALUE_PackI (Inner $ cg_t t_pack, Inner i)]
    | EUnOp (EUFold t, e) => compile e @ [VALUE_Fold $ Inner $ cg_t t]
    | EAscType (e, t) => compile e @ [VALUE_AscType $ Inner $ cg_t t]
    | ENever t => PUSH_value $ VNever $ cg_t t
    | EBuiltin (name, t) => PUSH_value $ VBuiltin (name, cg_t t)
    | EBinOp (EBPair, e1, e2) =>
      let
        val (e1, t1) = assert_EAscType e1
        val (e2, t2) = assert_EAscType e2
        val t1 = cg_t t1
        val t2 = cg_t t2
      in
        compile e1 @ compile e2 @ malloc_tuple [t1, t2] @ [PUSH_tuple_offset (2*32), ADD] @ concatRepeat 2 ([PUSH1nat 32, SWAP1, SUB, SWAP1] @ tuple_assign)
      end
    | EUnOp (EUInj (inj, t_other), e) =>
      let
        val (e, t_e) = assert_EAscType e
        val t_e = cg_t t_e
        val t_other = cg_t t_other
        val b = choose_inj (false, true) inj
      in
        compile e @
        [PUSH1 $ WiBool b] @
        impl_inj [TiBoolConst b, t_e] inj t_other
      end
    | ENewArrayValues (t, es) =>
      let
        val t = cg_t t
        val n = length es
      in
        [PUSH_tuple_offset n] @
        malloc_array t @
        [DUP1] @
        concatMap (fn e => compile e @ [DUP2, MSTORE, PUSH1nat 32, ADD]) es @
        [POP]
      end
    | EBinOp (EBRead, e1, e2) =>
      compile e1 @
      compile e2 @
      array_ptr @
      [MLOAD]
    | ETriOp (ETWrite, e1, e2, e3) =>
      compile e1 @
      compile e2 @
      compile e3 @
      [SWAP2, SWAP1] @
      array_ptr @
      [MSTORE, PUSH1 WTT]
    | EUnOp (EUUnfold, e) =>
      compile e @ [UNFOLD]
    | EUnOp (EUTiML opr, e) =>
      compile e @ impl_expr_un_op opr
    | EBinOp (EBNat opr, e1, e2) =>
      compile e1 @ 
      compile e2 @
      impl_nat_expr_bin_op opr
    | EBinOp (EBNatCmp opr, e1, e2) =>
      compile e1 @ 
      compile e2 @
      impl_nat_cmp opr
    | _ => raise Impossible $ "compile() on:\n" ^ (ExportPP.pp_e_to_string (NONE, NONE) $ ExportPP.export (NONE, NONE) ([], [], [], []) e)
  end

fun cg_e reg_counter (params as (ectx, itctx, rctx)) e =
  let
    (* val () = print $ "cg_e() started:\n" *)
    val compile = compile ectx
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
      let
        val (e1, t) = assert_EAscType e1
        val t = cg_t t
        val r = fresh_reg ()
      in        
        case e1 of
            EBinOp (EBNew, e1, e2) =>
            let
              val (t, len) = assert_TArr t
              val (name, e) = unBindSimpName bind
              val (e, i_e) = assert_EAscTime e
              val post_loop_label = fresh_label ()
              val loop_label = fresh_label ()
              val pre_loop_code =
                  [SWAP1, DUP1] @@
                  malloc_array t @@
                  [SWAP1, PUSH1nat 32, MUL] @@
                  PUSH_value (VAppITs (VAppITs_ctx (VLabel loop_label, itctx), [inl len])) @@
                  JUMP
              (* val pre_loop_label = fresh_label () *)
              (* val pre_loop_block = *)
              (*     let *)
              (*     in *)
              (*       HCode' ([inr ("t", KType), inl ("j", STime), inl ("len", SNat)], ((rctx, [TNat T0, TPreArray (t, len, T0), t], T1 %+ i_e), post_loop_code)) *)
              (*     end *)
              val loop_block =
                  let
                    fun MakeSubset (name, s, p) = Subset ((s, dummy), Bind.Bind ((name, dummy), p), dummy)
                    val s = MakeSubset ("i", BSNat, IV 0 %<= shift01_i_i len)
                    val i = fresh_ivar ()
                    val loop_code =
                        [DUP1, ISZERO] @@
                        PUSH_value (VAppITs_ctx (VLabel post_loop_label, itctx)) @@
                        [JUMPI, PUSH1nat 32, SWAP1, SUB] @@
                        array_assign @@
                        PUSH_value (VAppITs (VAppITs_ctx (VLabel loop_label, itctx), [inl $ FIV i %- N1])) @@
                        JUMP
                    fun IToReal i = UnOpI (ToReal, i, dummy)
                    fun close0_i_block x ((rctx, ts, i), I) = ((Rctx.map (close0_i_t x) rctx, map (close0_i_t x) ts, close0_i_i x i), close0_i_insts x I)
                    val block = ((rctx, [TNat (ConstIN (32, dummy) %* FIV i), TPreArray (t, len, FIV i), t], IToReal (FIV i %* ConstIN (8, dummy)) %+ T1 %+ i_e), loop_code)
                    val block = close0_i_block i block
                  in
                    HCode' (rev $ inl (("i", dummy), s) :: itctx, block)
                  end
              val () = output_heap ((loop_label, "new_array_loop"), loop_block)
              val post_loop_block =
                  let
                    val post_loop_code =
                        [POP, SWAP1, POP] @@
                        set_reg r @@
                        cg_e ((name, inl r) :: ectx, itctx, rctx @+ (r, TArr (t, len))) e
                  in
                    HCode' (rev itctx, ((rctx, [TNat T0, TPreArray (t, len, T0), t], T1 %+ i_e), post_loop_code))
                  end
              val () = output_heap ((post_loop_label, "new_array_post_loop"), post_loop_block)
            in
              compile e1 @@
              compile e2 @@
              pre_loop_code
            end
        | _ =>
          let
            val (name, e2) = unBindSimpName bind
            val I = cg_e ((name, inl r) :: ectx, itctx, rctx @+ (r, t)) e2
          in
            compile e1 @@ set_reg r @@ I
          end
      end
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
        compile e1 @@ [UNPACK $ TBinder name_a] @@ set_reg r @@ I
      end
    | EUnpackI (e1, bind) =>
      let
        val (e1, t) = assert_EAscType e1
        val ((_, s), t) = assert_TExistsI t
        val t = cg_t t
        val (name_a, bind) = unBindSimpName bind
        val (name_x, e2) = unBindSimpName bind
        val r = fresh_reg ()
        val I = cg_e ((name_x, inl r) :: ectx, inl (name_a, s) :: itctx, Rctx.map shift01_i_t rctx @+ (r, t)) e2
      in
        compile e1 @@ [UNPACKI $ IBinder name_a] @@ set_reg r @@ I
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
      compile e1 @@ compile e2 @@ set_reg 0 @@ JUMP
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
        val branch_prelude = [PUSH1nat 32, ADD, MLOAD] @ set_reg r
        val itbinds = rev itctx
        val hval = HCode' (itbinds, ((rctx, [TProd (TiBoolConst true, t2)](*the stack spec*), i_e2), branch_prelude @@ I2))
        val l = fresh_label ()
        val () = output_heap ((l, "inr_branch"), hval)
      in
        compile e @@
        PUSH_value (VAppITs_ctx (VLabel l, itctx)) @@
        br_sum @@
        branch_prelude @@
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
        compile e @@
        [ISZERO] @@
        PUSH_value (VAppITs_ctx (VLabel l, itctx)) @@
        [JUMPI] @@
        I1
      end
    | EHalt (e, _) =>
      let
        val (e, t) = assert_EAscType e
        val t = cg_t t
      in
        compile e @@ halt t
      end
    | EAscTime (e, i) => ASCTIME (Inner i) @:: cg_e params e
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
    val reg_counter = ref 2
    val I = cg_e reg_counter (ectx, rev itbinds, rctx) e
    fun get_time t =
      let
        val (_, t) = collect_TForallIT t
        val (_, i, _) = assert_TArrow t
      in
        i
      end
    val hval = HCode' (itbinds, ((rctx, [], get_time t_all), I))
  in
    (hval, !reg_counter)
  end
  
fun cg_prog e =
  let
    val () = heap_ref := []
    val (binds, e) = collect_ELetRec e
    val len = length binds
    fun on_bind ((_, bind), (ectx, num_regs)) =
      let
        val (t, (name, e)) = unBindAnnoName bind
        val () = println $ "cg() on " ^ fst name
        (* val t = cg_t t *)
        val l = fresh_label ()
        val ectx = (name, inr l) :: ectx
        val (hval, mr) = cg_hval ectx (e, t)
        val () = output_heap ((l, fst name), hval)
      in
        (ectx, max num_regs mr)
      end
    val (ectx, num_regs) = foldl on_bind ([], 0) binds
    val reg_counter = ref 1
    val I = cg_e reg_counter (ectx, [], Rctx.empty) e
    val H = !heap_ref
    val H = rev H
    val num_regs = max num_regs (!reg_counter)
    val I = [PUSH_reg $ reg_addr num_regs, PUSH1nat 0, MSTORE] @@ I
  in
    ((H, I), num_regs)
  end

val code_gen_tc_flags =
    let
      open MicroTiMLTypecheck
    in
      [Anno_ELet, Anno_EUnpack, Anno_EUnpackI, Anno_ECase, Anno_EHalt, Anno_ECase_e2_time, Anno_EIte_e2_time, Anno_EPair, Anno_EInj]
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
open MicroTiMLLongId
open MicroTiML
       
infixr 0 $
infixr 0 !!
         
fun fail () = OS.Process.exit OS.Process.failure
                   
end

open TestUtil
       
fun test1 dirname =
  let
    val () = println "ToEVM1.UnitTest started"
    val join_dir_file' = curry join_dir_file
    val filename = join_dir_file' dirname "to-evm1-test.pkg"
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
    val (e, _) = cps (e, TUnit) (EHaltFun TUnit TUnit, T_0)
    (* val (e, _) = cps (e, TUnit) (Eid TUnit, T_0) *)
    val () = println "Finished CPS conversion"
    (* val () = pp_e $ export ToStringUtil.empty_ctx e *)
    (* val () = println "" *)
    val e_str = ExportPP.pp_e_to_string (NONE, NONE) $ export (SOME 1, NONE) ToStringUtil.empty_ctx e
    val () = write_file (join_dir_file' dirname $ "unit-test-after-cps.tmp", e_str)
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
    val e = MicroTiMLPostProcess.post_process e
    val () = println "Finished CC"
    (* val () = pp_e $ export ToStringUtil.empty_ctx e *)
    (* val () = println "" *)
    val e_str = ExportPP.pp_e_to_string (NONE, NONE) $ export (SOME 1, NONE) ToStringUtil.empty_ctx e
    val () = write_file (join_dir_file' dirname $ "unit-test-after-cc.tmp", e_str)
    (* val () = println e_str *)
    (* val () = println "" *)
    (* val () = println "Started MicroTiML typechecking #3 ..." *)
    (* val ((e, t, i), vcs, admits) = typecheck pair_alloc_tc_flags ([], [], [](* , HeapMap.empty *)) e *)
    (* val () = println "Finished MicroTiML typechecking #3" *)
    (* val () = println "Type:" *)
    (* val () = pp_t NONE $ export_t (SOME 1) ([], []) t *)
    (* val () = println "Time:" *)
    (* (* val i = simp_i i *) *)
    (* val () = println $ ToString.str_i Gctx.empty [] i *)
    (* (* val () = pp_e (NONE, NONE) $ export ((* (SOME 1) *)NONE, NONE) ToStringUtil.empty_ctx e *) *)
    (* (* val () = println "" *) *)
                     
    (* val () = println "Started Pair Alloc ..." *)
    (* (* val e = pa e *) *)
    (* val e = pair_alloc e *)
    (* val () = println "Finished Pair Alloc" *)
    (* (* val () = pp_e $ export ToStringUtil.empty_ctx e *) *)
    (* (* val () = println "" *) *)
    (* val e_str = ExportPP.pp_e_to_string (NONE, NONE) $ export ((* SOME 1 *)NONE, NONE) ToStringUtil.empty_ctx e *)
    (* val () = write_file (join_dir_file' dirname $ "unit-test-after-pair-alloc.tmp", e_str) *)
    (* val () = println e_str *)
    (* val () = println "" *)
    (* val () = println "Started post-pair-allocation form checking" *)
    (* val () = check_CPSed_expr e *)
    (* val () = println "Finished post-pair-allocation form checking" *)
    val () = println "Started MicroTiML typechecking #4 ..."
    val ((e, t, i), vcs, admits) = typecheck code_gen_tc_flags ([], [], []) e
    val () = println "Finished MicroTiML typechecking #4"
    val () = println "Type:"
    val () = pp_t NONE $ export_t (SOME 1) ([], []) t
    val () = println "Time:"
    (* val i = simp_i i *)
    val () = println $ ToString.str_i Gctx.empty [] i
                     
    open EVM1ExportPP
    val () = println "Started Code Generation ..."
    val (prog, num_regs) = cg_prog e
    val () = println "Finished Code Generation"
    val () = println $ "# of registers: " ^ str_int num_regs
    val prog_str = EVM1ExportPP.pp_prog_to_string $ export_prog ((* SOME 1 *)NONE, NONE, NONE) prog
    val () = write_file (join_dir_file' dirname $ "unit-test-after-code-gen.tmp", prog_str)
    (* val () = println prog_str *)
    (* val () = println "" *)
    open EVM1Typecheck
    val () = println "Started EVM1 typechecking ..."
    val (i, vcs, admits) = evm1_typecheck num_regs prog
    val () = println "Finished EVM1 typechecking"
    val () = println "Time:"
    (* val i = simp_i i *)
    val () = println $ ToString.str_i Gctx.empty [] i
    open EVM1Assemble
    val prog_bytes = ass2str prog
    val () = write_file (join_dir_file' dirname $ "evm-bytecode.tmp", prog_bytes)
    (* val () = println "EVM Bytecode:" *)
    (* val () = println prog_bytes *)
    (* val () = println "" *)

    val () = println "ToEVM1.UnitTest passed"
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
