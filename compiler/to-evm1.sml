(* Code generation to EVM1 *)

structure ToEVM1 = struct

open EVM1Util
open UVarExprUtil
open Expr
open CompilerUtil
open EVM1Visitor
open EVM1

infixr 0 $
         
infix 9 %@
infix 8 %^
infix 7 %*
infix 6 %+ 
infix 6 %-
infix 4 %<=
infix 4 %<
infix 4 %>=
infix 4 %>
infix 4 %=
infix 4 %=?
infixr 3 /\
infixr 2 \/
infixr 1 -->
infix 1 <->

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

infix  9 @!!
infix  9 @%!!
infix  6 @%+
         
val T0 = T0 dummy
val T1 = T1 dummy
val N0 = N0 dummy
val N1 = N1 dummy
            
val STime = STime dummy
val SNat = SNat dummy
val SBool = SBool dummy
val SUnit = SUnit dummy

fun close_i_insts a = shift_i_insts_fn (close_i_i, close_i_s, close_i_t) a
fun close_t_insts a = shift_t_insts_fn close_t_t a

fun close0_i_insts a = close_i_insts 0 a
fun close0_t_insts a = close_t_insts 0 a

fun close0_i_block x ((st, rctx, ts, (j, i)), I) = ((close0_i_i x st, Rctx.map (close0_i_t x) rctx, map (close0_i_t x) ts, (close0_i_i x j, close0_i_i x i)), close0_i_insts x I)
                                            
fun shift_i_insts a = shift_i_insts_fn (shiftx_i_i, shiftx_i_s, shift_i_t) a
fun shift_t_insts a = shift_t_insts_fn shift_t_t a

fun shift01_i_insts a = shift_i_insts 0 1 a
fun shift01_t_insts a = shift_t_insts 0 1 a

fun shift01_i_block ((st, rctx, ts, (j, i)), I) = ((shift_i_i st, Rctx.map shift01_i_t rctx, map shift01_i_t ts, (shift_i_i j, shift_i_i i)), shift01_i_insts I)
                                            
fun reg_addr r = 32 * (r + 1)
(* use r0 as scratch space *)
(* val scratch = 32 *)
val scratch = reg_addr 0
val FIRST_GENERAL_REG = 2
val ARG_REG = FIRST_GENERAL_REG
               
fun assert_EState e =
  case e of
      EState a => a
    | _ => raise assert_fail "assert_EState"

fun TProd (a, b) = TMemTuplePtr ([a, b], N 0)

fun cg_ty_visitor_vtable cast () =
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
    fun visit_TArrow this env (data as ((pre, t1), i, (_, t2))) =
      let
        (* val () = assert_TUnit "cg_t(): result type of TArrow must be TUnit" t2 *)
        val cg_t = #visit_ty (cast this) this env
        val t1 = cg_t t1
      in
        TArrowEVM (pre, rctx_single (ARG_REG, t1), [], i)
      end
    val vtable = override_visit_TArrow vtable visit_TArrow
    fun visit_TBinOp this env (data as (opr, t1, t2)) =
      case opr of
          TBProd () =>
          let
            val cg_t = #visit_ty (cast this) this env
            val t1 = cg_t t1
            val t2 = cg_t t2
          in
            TProd (t1, t2)
          end
        | _ => #visit_TBinOp vtable this env data (* call super *)
    val vtable = override_visit_TBinOp vtable visit_TBinOp
    fun visit_TArr this env (data as (t, i)) =
      let
        val cg_t = #visit_ty (cast this) this env
        val t = cg_t t
      in
        TArrayPtr (t, i, INat 32)
      end
    val vtable = override_visit_TArr vtable visit_TArr
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
type basic_sort = Expr.basic_sort
type sort = Expr.sort
type ty = (Expr.var, basic_sort, idx, sort) ty
type kind = basic_sort kind
                  
val heap_ref = ref ([] : ((label * string) * (idx, sort, kind, ty) hval) list)
fun output_heap pair = push_ref heap_ref pair

fun IV n = IVar (ID (n, dummy), [])
fun TV n = TVar (ID (n, dummy), [])
fun FIV x = IVar (make_Free_i x, [])
                
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

fun PUSH_tuple_offset n = PUSH (2, Inner $ WNat n)
fun PUSH_array_offset n = PUSH (32, Inner $ WNat n)
fun PUSH_reg n = PUSH (2, Inner $ WNat n)
    
fun get_reg r = [PUSH_reg $ reg_addr r, MLOAD ()]
fun set_reg r = [PUSH_reg $ reg_addr r, MSTORE ()]
val array_ptr = [PUSH1nat 32, MUL (), ADD ()]
val byte2int = [BYTE2INT ()]
                  
fun init_free_ptr num_regs = [MACRO_init_free_ptr num_regs]
fun tuple_malloc ts = [MACRO_tuple_malloc $ Inner ts]
val tuple_assign = [MACRO_tuple_assign ()]
val printc = [MACRO_printc ()]
fun array_malloc t b = [MACRO_array_malloc (Inner t, b)]
val array_init_assign = [MACRO_array_init_assign ()]
val array_init_len = [MACRO_array_init_len ()]
(* val int2byte = [] (* noop, relying on type discipline *) *)
val int2byte = [MACRO_int2byte ()]
fun make_inj t_other = [MACRO_inj $ Inner t_other]
val br_sum = [MACRO_br_sum ()]
fun halt t = MACRO_halt t

val inline_macro_inst = inline_macro_inst (PUSH_reg, PUSH_tuple_offset, scratch, reg_addr, TUnit)
val inline_macro_insts = inline_macro_insts (inline_macro_inst, PUSH_reg, scratch)
                                          
fun inline_macro_hval code =
  let
    val (binds, (spec, I)) = unBind code
    val I = inline_macro_insts I
  in
    Bind (binds, (spec, I))
  end

fun inline_macro_prog (H, I) =
  (map (mapSnd inline_macro_hval) H, inline_macro_insts I)

fun impl_nat_cmp opr =
  case opr of
      NCLt () => [GT ()] (* a<b <-> b>a *)
    | NCGt () => [LT ()]
    | NCLe () => [LT (), ISZERO ()] (* a<=b <-> ~(a>b) <-> ~(b<a) *)
    | NCGe () => [GT (), ISZERO ()]
    | NCEq () => [EQ ()]
    | NCNEq () => [EQ (), ISZERO ()]
      
fun concatRepeat n v = List.concat $ repeat n v
               
fun cg_c c =
  case c of
      ECTT () => WCTT ()
    | ECNat n => WCNat n
    | ECInt n => WCInt n
    | ECBool n => WCBool n
    | ECiBool n => WCiBool n
    | ECByte c => WCByte c
    (* | ECString s => raise Impossible $ "cg_c() on ECString" *)
                                
fun impl_prim_expr_un_opr opr =
  case opr of
      EUPIntNeg () => [PUSH1 $ WInt 0, SUB ()]
    | EUPBoolNeg () => [ISZERO ()]
    | EUPInt2Byte () => int2byte
    | EUPByte2Int () => byte2int
    (* | EUPStrLen () => [PUSH1nat 32, SWAP1, SUB, MLOAD] *)
    (* | _ => raise Impossible $ "impl_prim_expr_up_op() on " ^ str_prim_expr_un_op opr *)
      
fun impl_prim_expr_bin_op opr =
  case opr of
       EBPIntAdd () => [ADD ()]
     | EBPIntMult () => [MUL ()]
     | EBPIntMinus () => [SWAP1, SUB ()]
     | EBPIntDiv () => [SWAP1, SDIV ()]
     | EBPIntMod () => [SWAP1, MOD ()]
     | EBPIntLt () => [SWAP1, LT ()]
     | EBPIntGt () => [SWAP1, GT ()]
     | EBPIntLe () => [GT (), ISZERO ()]
     | EBPIntGe () => [LT (), ISZERO ()]
     | EBPIntEq () => [EQ ()]
     | EBPIntNEq () => [EQ (), ISZERO ()]
     | EBPBoolAnd () => [AND ()]
     | EBPBoolOr () => [OR ()]
     (* | EBPStrConcat () => raise Impossible "impl_prim_expr_bin_op() on EBPStrConcat" *)
                  
fun impl_expr_un_op opr =
  case opr of
      EUPrim opr => impl_prim_expr_un_opr opr
    | EUNat2Int () => [NAT2INT ()]
    | EUInt2Nat () => [INT2NAT ()]
    | EUArrayLen () => [PUSH1nat 32, SWAP1, SUB (), MLOAD ()]
    | EUProj proj => [PUSH_tuple_offset $ 32 * choose (0, 1) proj, ADD (), MLOAD ()]
    | EUPrintc () => printc
    (* | EUPrint () => [PRINT] *)
    | EUStorageGet () => [SLOAD ()]
    | EUVectorClear () => [PUSH1nat 0, SWAP1, SSTORE (), PUSH1 WTT] (* should also zero out the contents, in order to save storage *)
    | EUVectorLen () => [SLOAD ()]
                        
fun impl_nat_expr_bin_op opr =
  case opr of
      EBNAdd () => [ADD ()]
    | EBNMult () => [MUL ()]
    | EBNDiv () => [SWAP1, DIV ()]
    | EBNBoundedMinus () => [SWAP1, SUB ()]

val st_ref = ref IEmptyState
                 
fun compile st_name2int ectx e =
  let
    val compile = compile st_name2int ectx
    fun err () = raise Impossible $ "compile() on:\n" ^ (ExportPP.pp_e_to_string (NONE, NONE) $ ExportPP.export (NONE, NONE) ([], [], [], []) e)
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
    | EState x => PUSH_value $ VState $ st_name2int @!! x
    | EAppT (e, t) => compile e @ [VALUE_AppT $ Inner $ cg_t t]
    | EAppI (e, i) => compile e @ [VALUE_AppI $ Inner i]
    | EPack (t_pack, t, e) => compile e @ [VALUE_Pack (Inner $ cg_t t_pack, Inner $ cg_t t)]
    | EPackI (t_pack, i, e) => compile e @ [VALUE_PackI (Inner $ cg_t t_pack, Inner i)]
    | EUnOp (EUFold t, e) => compile e @ [VALUE_Fold $ Inner $ cg_t t]
    | EAscType (e, t) => compile e @ [VALUE_AscType $ Inner $ cg_t t]
    | EAscState (e, st) => compile e
    | ENever t => PUSH_value $ VNever $ cg_t t
    | EBuiltin (name, t) => PUSH_value $ VBuiltin (name, cg_t t)
    | EBinOp (EBPair (), e1, e2) =>
      let
        val (e1, t1) = assert_EAscType e1
        val (e2, t2) = assert_EAscType e2
        val t1 = cg_t t1
        val t2 = cg_t t2
      in
        compile e1 @ compile e2 @ tuple_malloc [t1, t2] @ [PUSH_tuple_offset (2*32), ADD ()] @ concatRepeat 2 ([PUSH1nat 32, SWAP1, SUB (), SWAP1] @ tuple_assign) @ [MARK_PreTuple2TuplePtr ()]
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
        make_inj t_other
      end
    | ENewArrayValues (t, es) =>
      let
        val t = cg_t t
        val n = length es
      in
        [PUSH_array_offset n, DUP1] @
        array_malloc t true @
        [SWAP1] @
        array_init_len @
        [PUSH1nat 0] @
        concatMap (fn e => compile e @ [SWAP2, SWAP1] @ array_init_assign @ [SWAP2, POP (), SWAP1, PUSH1nat 32, ADD ()]) es @
        [POP (), MARK_PreArray2ArrayPtr ()]
      end
    | EBinOp (EBRead (), e1, e2) =>
      compile e1 @
      compile e2 @
      array_ptr @
      [MLOAD ()]
    | ETriOp (ETWrite (), e1, e2, e3) =>
      compile e1 @
      compile e2 @
      compile e3 @
      [SWAP2, SWAP1] @
      array_ptr @
      [MSTORE (), PUSH1 WTT]
    | EUnOp (EUUnfold (), e) =>
      compile e @ [UNFOLD ()]
    | EUnOp (EUTiML opr, e) =>
      compile e @
      impl_expr_un_op opr
    | EBinOp (EBNat opr, e1, e2) =>
      compile e1 @ 
      compile e2 @
      impl_nat_expr_bin_op opr
    | EBinOp (EBNatCmp opr, e1, e2) =>
      compile e1 @ 
      compile e2 @
      impl_nat_cmp opr
    | EBinOp (EBMapPtr (), e1, e2) =>
      compile e1 @ 
      compile e2 @
      [MACRO_map_ptr ()]
    | EBinOp (EBStorageSet (), e1, e2) =>
      compile e1 @ 
      compile e2 @
      [SWAP1, SSTORE (), PUSH1 WTT]
    | EBinOp (EBVectorGet (), e1, e2) =>
      compile e1 @ 
      compile e2 @
      [SWAP1, MACRO_vector_ptr (), SLOAD ()]
    | ETriOp (ETVectorSet (), e1, e2, e3) =>
      compile e1 @ 
      compile e2 @
      compile e3 @
      [SWAP2, MACRO_vector_ptr (), SSTORE (), PUSH1 WTT]
    | EBinOp (EBVectorPushBack (), e1, e2) =>
      let
        val I = compile e1 @
                compile e2 @
                [MACRO_vector_push_back (), PUSH1 WTT]
        val x = assert_EState e1
        val st = !st_ref
        val len = st @%!! x
        val () = st_ref := st @%+ (x, len %+ N1)
      in
        I
      end
    | ETriOp (ETIte (), _, _, _) => err ()
    | EBinOp (EBApp (), _, _) => err ()
    | EBinOp (EBNew (), _, _) => err ()
    | ECase _ => err ()
    | EAbs _ => err ()
    | ERec _ => err ()
    | EAbsT _ => err ()
    | EAbsI _ => err ()
    | EUnpack _ => err ()
    | EUnpackI _ => err ()
    | EAscTime _ => err ()
    | EAscSpace _ => err ()
    | ELet _ => err ()
    | ELetIdx _ => err ()
    | ELetType _ => err ()
    | ELetConstr _ => err ()
    | EAbsConstr _ => err ()
    | EAppConstr _ => err ()
    | EVarConstr _ => err ()
    | EPackIs _ => err ()
    | EMatchSum _ => err ()
    | EMatchPair _ => err ()
    | EMatchUnfold _ => err ()
    | EIfi _ => err ()
    | EHalt _ => err ()
    | EMallocPair _ => err ()
    | EPairAssign _ => err ()
    | EProjProtected _ => err ()
    | EVar (QID _) => err ()
  end

val compile = fn (st_name2int, ectx, e, st) =>
                 let
                   val () = st_ref := st
                   val I = compile st_name2int ectx e
                 in
                   (I, !st_ref)
                 end

fun cg_e (reg_counter, st_name2int) (params as (ectx, itctx, rctx, st)) e : (idx, mtiml_ty) insts =
  let
    (* val () = print $ "cg_e() started:\n" *)
    val compile = fn (e, st) => compile (st_name2int, ectx, e, st)
    val cg_e = cg_e (reg_counter, st_name2int)
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
    fun err () = raise Impossible $ "unknown case of cg_e() on:\n" ^ (ExportPP.pp_e_to_string (NONE, NONE) $ ExportPP.export (NONE, NONE) ([], [], [], []) e)

    fun main () =
  case e of
      ELet (e1, bind) =>
      let
        val (e1, t) = assert_EAscType e1
        val t = cg_t t
        val r = fresh_reg ()
      in        
        case e1 of
            EBinOp (EBNew (), e1, e2) =>
            let
              open EVMCosts
              fun to_real n = IToReal (N n, dummy)
              val (I_e1, st) = compile (e1, st) 
              val (I_e2, st) = compile (e2, st)
              val (t, len, _) = assert_TArrayPtr t
              val (name, e) = unBindSimpName bind
              val (e, space_e) = assert_EAscSpace e
              val (e, i_e) = assert_EAscTime e
              val post_loop_label = fresh_label ()
              val loop_label = fresh_label ()
              val pre_loop_code =
                  [SWAP1, DUP1] @@
                  array_malloc t false @@
                  [DUP2] @@
                  array_init_len @@
                  [SWAP1, PUSH1nat 32, MUL ()] @@
                  PUSH_value (VAppITs (VAppITs_ctx (VLabel loop_label, itctx), [inl len])) @@
                  JUMP ()
              (* val pre_loop_label = fresh_label () *)
              (* val pre_loop_block = *)
              (*     let *)
              (*     in *)
              (*       HCode' ([inr ("t", KType), inl ("j", STime), inl ("len", SNat)], ((rctx, [TNat T0, TPreArray (t, len, T0), t], T1 %+ i_e), post_loop_code)) *)
              (*     end *)
              val loop_block =
                  let
                    fun MakeSubset (name, s, p) = SSubset ((s, dummy), Bind.Bind ((name, dummy), p), dummy)
                    fun IToReal i = IUnOp (IUToReal (), i, dummy)
                    val s = MakeSubset ("i", BSNat, IV 0 %<= shift01_i_i len)
                    val i = fresh_ivar ()
                    val loop_code =
                        [PUSH1 WTT, DUP2, ISZERO ()] @@
                        PUSH_value (VAppITs (VAppITs_ctx (VLabel post_loop_label, itctx), [inl $ FIV i])) @@
                        [JUMPI (), UNPACKI $ IBinder ("__n_neq0", dummy)] @@
                        (shift01_i_insts $
                        [POP (), PUSH1nat 32, SWAP1, SUB ()] @@
                        array_init_assign @@
                        PUSH_value (VAppITs (VAppITs_ctx (VLabel loop_label, itctx), [inl $ FIV i %- N1])) @@
                        JUMP ())
                    val block = ((st, rctx, [TNat (INat 32 %* FIV i), TPreArray (t, len, FIV i, (true, false)), t], (IToReal (FIV i %* INat C_New_loop) %+ to_real (C_New_loop_test + C_New_post_loop) %+ i_e, space_e)), loop_code)
                    val block = close0_i_block i $ shift01_i_block block
                  in
                    HCode' (rev $ inl (("i", dummy), s) :: itctx, block)
                  end
              val () = output_heap ((loop_label, "new_array_loop"), loop_block)
              val post_loop_block =
                  let
                    val s = SNat
                    val i = fresh_ivar ()
                    val post_loop_code =
                        [UNPACKI $ IBinder ("__n_eq0", dummy)] @@
                        (shift01_i_insts $
                        [POP (), POP (), SWAP1, POP (), MARK_PreArray2ArrayPtr ()] @@
                        set_reg r @@
                        cg_e ((name, inl r) :: ectx, itctx, rctx @+ (r, TArr (t, len)), st) e)
                    val t_ex = make_exists "__p" $ SSubset_from_prop dummy $ (FIV i %* N32 %=? N0) %= Itrue
                    val block = ((st, rctx, [t_ex, TNat $ FIV i %* N32, TPreArray (t, len, FIV i, (true, false)), t], (to_real C_New_post_loop %+ i_e, space_e)), post_loop_code)
                    val block = close0_i_block i $ shift01_i_block block
                  in
                    HCode' (rev $ inl (("i", dummy), s) :: itctx, block)
                  end
              val () = output_heap ((post_loop_label, "new_array_post_loop"), post_loop_block)
            in
              I_e1 @@ I_e2 @@
              pre_loop_code
            end
        | _ =>
          let
            val (I_e1, st) = compile (e1, st)
            val (name, e2) = unBindSimpName bind
            val I = cg_e ((name, inl r) :: ectx, itctx, rctx @+ (r, t), st) e2
          in
            I_e1 @@ set_reg r @@ I
          end
      end
    | EUnpack (e1, bind) =>
      let
        val (e1, t) = assert_EAscType e1
        val (I_e1, st) = compile (e1, st)
        val ((_, k), t) = assert_TExists t
        val t = cg_t t
        val (name_a, bind) = unBindSimpName bind
        val (name_x, e2) = unBindSimpName bind
        val r = fresh_reg ()
        val I = cg_e ((name_x, inl r) :: ectx, inr (name_a, k) :: itctx, Rctx.map shift01_t_t rctx @+ (r, t), st) e2
      in
        I_e1 @@ [UNPACK $ TBinder name_a] @@ set_reg r @@ I
      end
    | EUnpackI (e1, bind) =>
      let
        val (e1, t) = assert_EAscType e1
        val (I_e1, st) = compile (e1, st)
        val ((_, s), t) = assert_TExistsI t
        val t = cg_t t
        val (name_a, bind) = unBindSimpName bind
        val (name_x, e2) = unBindSimpName bind
        val r = fresh_reg ()
        val I = cg_e ((name_x, inl r) :: ectx, inl (name_a, s) :: itctx, Rctx.map shift01_i_t rctx @+ (r, t), shift_i_i st) e2
      in
        I_e1 @@ [UNPACKI $ IBinder name_a] @@ set_reg r @@ I
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
    | EBinOp (EBApp (), e1, e2) =>
      let
        val (I_e1, st) = compile (e1, st) 
        val (I_e2, st) = compile (e2, st)
      in
        I_e1 @@ I_e2 @@ set_reg ARG_REG @@ JUMP ()
      end
    | ECase (e, bind1, bind2) =>
      let
        val (e, t) = assert_EAscType e
        val (I_e, st) = compile (e, st)
        val t = cg_t t
        val (t1, t2) = assert_TSum t
        val (name1, e1) = unBindSimpName bind1
        val (name2, e2) = unBindSimpName bind2
        val (e2, space_e2) = assert_EAscSpace e2
        val (e2, i_e2) = assert_EAscTime e2
        val r = fresh_reg ()
        val I1 = cg_e ((name1, inl r) :: ectx, itctx, rctx @+ (r, t1), st) e1
        val I2 = cg_e ((name2, inl r) :: ectx, itctx, rctx @+ (r, t2), st) e2
        val branch_prelude = [PUSH1nat 32, ADD (), MLOAD ()] @ set_reg r
        val itbinds = rev itctx
        val hval = HCode' (itbinds, ((st, rctx, [TProd (TiBoolConst true, t2)](*the stack spec*), (i_e2, space_e2)), branch_prelude @@ I2))
        val l = fresh_label ()
        val () = output_heap ((l, "inr_branch"), hval)
      in
        I_e @@
        PUSH_value (VAppITs_ctx (VLabel l, itctx)) @@
        br_sum @@
        branch_prelude @@
        I1
      end
    | EIfi (e, bind1, bind2) =>
      let
        val (e, t) = assert_EAscType e
        val (I_e, st) = compile (e, st)
        val t = cg_t t
        val i = assert_TiBool t
        val make_exists = make_exists "__p"
        val t1 = make_exists (SSubset_from_prop dummy $ i %= Itrue)
        val t2 = make_exists (SSubset_from_prop dummy $ i %= Ifalse)
        val (name1, e1) = unBindSimpName bind1
        val (name2, e2) = unBindSimpName bind2
        val (e2, space_e2) = assert_EAscSpace e2
        val (e2, i_e2) = assert_EAscTime e2
        val r = fresh_reg ()
        val I1 = cg_e ((name1, inl r) :: ectx, itctx, rctx @+ (r, t1), st) e1
        val I2 = cg_e ((name2, inl r) :: ectx, itctx, rctx @+ (r, t2), st) e2
        val branch_prelude = set_reg r
        val itbinds = rev itctx
        val hval = HCode' (itbinds, ((st, rctx, [t2], (i_e2, space_e2)), branch_prelude @@ I2))
        val l = fresh_label ()
        val () = output_heap ((l, "ifi_else_branch"), hval)
      in
        I_e @@
        [ISZERO (), PUSH1 WTT, SWAP1] @@
        PUSH_value (VAppITs_ctx (VLabel l, itctx)) @@
        [JUMPI ()] @@
        branch_prelude @@
        I1
      end
    | ETriOp (ETIte (), e, e1, e2) =>
      let
        val (I_e, st) = compile (e, st)
        val (e2, space_e2) = assert_EAscSpace e2
        val (e2, i_e2) = assert_EAscTime e2
        val I1 = cg_e (ectx, itctx, rctx, st) e1
        val I2 = cg_e (ectx, itctx, rctx, st) e2
        val itbinds = rev itctx
        val hval = HCode' (itbinds, ((st, rctx, [], (i_e2, space_e2)), I2))
        val l = fresh_label ()
        val () = output_heap ((l, "else_branch"), hval)
      in
        I_e @@
        [ISZERO ()] @@
        PUSH_value (VAppITs_ctx (VLabel l, itctx)) @@
        [JUMPI ()] @@
        I1
      end
    | EHalt (e, _) =>
      let
        val (e, t) = assert_EAscType e
        val (I_e, st) = compile (e, st)
        val t = cg_t t
      in
        I_e @@ halt t
      end
    | EAscTime (e, i) => ASCTIME (Inner i) @:: cg_e params e
    | EAscSpace (e, i) => ASCSPACE (Inner i) @:: cg_e params e
    | EAscType (e, _) => cg_e params e
    | EAscState (e, _) => cg_e params e
    | EBinOp (EBPair (), _, _) => err ()
    | EBinOp (EBNew (), _, _) => err ()
    | EBinOp (EBRead (), _, _) => err ()
    | EBinOp (EBPrim _, _, _) => err ()
    | EBinOp (EBNat _, _, _) => err ()
    | EBinOp (EBNatCmp _, _, _) => err ()
    | EBinOp (EBVectorGet (), _, _) => err ()
    | EBinOp (EBVectorPushBack (), _, _) => err ()
    | EBinOp (EBMapPtr (), _, _) => err ()
    | EBinOp (EBStorageSet (), _, _) => err ()
    | ETriOp (ETWrite (), _, _, _) => err ()
    | ETriOp (ETVectorSet (), _, _, _) => err ()
    | EVar _ => err ()
    | EConst _ => err ()
    | EState _ => err ()
    | EUnOp _ => err ()
    | EAbs _ => err ()
    | ERec _ => err ()
    | EAbsT _ => err ()
    | EAppT _ => err ()
    | EAbsI _ => err ()
    | EAppI _ => err ()
    | EPack _ => err ()
    | EPackI _ => err ()
    (* | EAscState _ => err () *)
    (* | EAscType _ => err () *)
    | ENever _ => err ()
    | EBuiltin _ => err ()
    | ENewArrayValues _ => err ()
    | ELetIdx _ => err ()
    | ELetType _ => err ()
    | ELetConstr _ => err ()
    | EAbsConstr _ => err ()
    | EAppConstr _ => err ()
    | EVarConstr _ => err ()
    | EPackIs _ => err ()
    | EMatchSum _ => err ()
    | EMatchPair _ => err ()
    | EMatchUnfold _ => err ()
    | EMallocPair _ => err ()
    | EPairAssign _ => err ()
    | EProjProtected _ => err ()
    fun extra_msg () = "\nwhen code-gen-ing:\n" ^ (ExportPP.pp_e_to_string (NONE, NONE) $ ExportPP.export (SOME 1, SOME 5) (ictxn, tctxn, [], ectxn) e)
    val ret = main ()
              handle Impossible m => raise Impossible (m ^ extra_msg ())
    (* val () = println $ "cg_e() finished:\n" ^ e_str *)
  in
    ret
  end
        
                       
(* ectx: variable mapping, maps variables to registers or labels *)
fun cg_hval (st_name2int, ectx) (e, t_all) =
  let
    val (itbinds, e) = collect_EAbsIT e
    val (st, (t, (name, e))) = assert_EAbs e
    val t = cg_t t
    (* input argument is always stored in ARG_REG *)
    val ectx = (name, inl ARG_REG) :: ectx
    val rctx = rctx_single (ARG_REG, t)
    val reg_counter = ref $ ARG_REG+1
    val I = cg_e (reg_counter, st_name2int) (ectx, rev itbinds, rctx, st) e
    fun get_time_space t =
      let
        val (_, t) = collect_TForallIT t
        val (_, i, _) = assert_TArrow t
      in
        i
      end
    val hval = HCode' (itbinds, ((st, rctx, [], get_time_space t_all), I))
  in
    (hval, !reg_counter)
  end
  
fun cg_prog (st_name2int, init_st) e =
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
        val (hval, mr) = cg_hval (st_name2int, ectx) (e, t)
        val () = output_heap ((l, fst name), hval)
      in
        (ectx, max num_regs mr)
      end
    val (ectx, num_regs) = foldl on_bind ([], 0) binds
    val reg_counter = ref FIRST_GENERAL_REG
    val I = cg_e (reg_counter, st_name2int) (ectx, [], Rctx.empty, init_st) e
    val H = !heap_ref
    val H = rev H
    val num_regs = max num_regs (!reg_counter)
    val I = init_free_ptr num_regs @@ I
  in
    ((H, I : (idx, mtiml_ty) insts), num_regs)
  end

val code_gen_tc_flags =
    let
      open MicroTiMLTypecheck
    in
      [Anno_ELet, Anno_EUnpack, Anno_EUnpackI, Anno_ECase, Anno_EIfi, Anno_EHalt, Anno_ECase_e2_time, Anno_EIte_e2_time, Anno_EIfi_e2_time, Anno_EPair, Anno_EInj]
    end
                     
structure UnitTest = struct

structure TestUtil = struct

open CPS
open CC
(* open PairAlloc *)
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
    val () = println "Started TiML typechecking ..."
    val () = TypeCheck.turn_on_builtin ()
    val () = TypeCheck.clear_st_types ()
    val ((prog, _, _), (vcs, admits)) = typecheck_prog empty prog
    val (st_name2ty, st_name2int) = TypeCheck.get_st_types ()
    fun check_vcs vcs = 
        (* case VCSolver.vc_solver filename vcs of *)
        (*     [] => () *)
        (*   | vcs => *)
        (*     raise curry TypeCheck.Error dummy $ (* str_error "Error" filename dummy *) [sprintf "Typecheck Error: $ Unproved obligations:" [str_int $ length vcs], ""] @ ( *)
        (*       (* concatMap (fn vc => str_vc true filename vc @ [""]) $ map fst vcs *) *)
        (*       concatMap (VCSolver.print_unsat true filename) vcs *)
    (*     ) *)
      ()
    val () = check_vcs vcs
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
    val st_name2ty = StMap.map (mapSnd trans_mt) st_name2ty
    val () = println "Finished translating"
    open ExportPP
    val e_str = ExportPP.pp_e_to_string (NONE, NONE) $ export (NONE, NONE) ToStringUtil.empty_ctx e
    val () = write_file (join_dir_file' dirname $ "unit-test-after-translation.tmp", e_str)
    (* val () = println e_str *)
    (* val () = println "" *)
                     
    open MicroTiMLTypecheck
    open TestUtil
    val init_st = IState $ StMap.map (fn _ => INat 0) st_name2ty
    val () = println "Started MicroTiML typechecking #1 ..."
    val (e, _) = LiveVars.live_vars e
    val e = set_EAbs_is_rec e
    val ((e, t, i, st), (vcs, admits)) = typecheck (Allow_substate_call :: cps_tc_flags, st_name2ty) (([], [], []), init_st) e
    val () = check_vcs vcs
    val () = println "Finished MicroTiML typechecking #1"
    open ExportPP
    val () = println "Type:"
    val () = pp_t NONE $ export_t (SOME 1) ([], []) t
    fun print_time_space (i, j) =
        let
          val () = print "Time:"
          val i = simp_i i
          val () = println $ ToString.str_i Gctx.empty [] i
          val () = print "Space:"
          val j = simp_i j
          val () = println $ ToString.str_i Gctx.empty [] j
        in
          (i, j)
        end
    val _ = print_time_space i
    (* val () = println $ "#VCs: " ^ str_int (length vcs) *)
    (* val () = println "VCs:" *)
    (* val () = app println $ concatMap (fn ls => ls @ [""]) $ map (str_vc false "") vcs *)
    (* val () = pp_e $ export ToStringUtil.empty_ctx e *)
    (* val () = println "" *)
                     
    val () = println "Started CPS conversion ..."
    open MicroTiMLUtil
    val (e, _) = cps (e, TUnit, IEmptyState) (EHaltFun TUnit TUnit, TN0 dummy)
    (* val (e, _) = cps (e, TUnit) (Eid TUnit, T_0) *)
    val () = println "Finished CPS conversion"
    val e_str = ExportPP.pp_e_to_string (NONE, NONE) $ export (NONE, NONE) ToStringUtil.empty_ctx e
    val () = write_file (join_dir_file' dirname $ "unit-test-after-cps.tmp", e_str)
    (* val () = println e_str *)
    (* val () = println "" *)
    val () = println "Started MicroTiML typechecking #2 ..."
    val ((e, t, i, st), (vcs, admits)) = typecheck (cc_tc_flags, st_name2ty) (([], [], []), init_st) e
    val () = app println $ concatMap (fn vc => VC.str_vc false filename vc @ [""]) vcs
    val () = check_vcs vcs
    val () = println "Finished MicroTiML typechecking #2"
    (* val () = println "Type:" *)
    (* val () = pp_t NONE $ export_t (SOME 1) ([], []) t *)
    val _ = print_time_space i
                     
    val () = println "Started CC ..."
    val e = cc e
    val e = MicroTiMLPostProcess.post_process e
    val () = println "Finished CC"
    val e_str = ExportPP.pp_e_to_string (NONE, NONE) $ export (NONE, NONE) ToStringUtil.empty_ctx e
    val () = write_file (join_dir_file' dirname $ "unit-test-after-cc.tmp", e_str)
    (* val () = println e_str *)
    (* val () = println "" *)
    val () = println "Started MicroTiML typechecking #4 ..."
    val ((e, t, i, st), (vcs, admits)) = typecheck (code_gen_tc_flags, st_name2ty) (([], [], []), init_st) e
    val () = check_vcs vcs
    val () = println "Finished MicroTiML typechecking #4"
    (* val () = println "Type:" *)
    (* val () = pp_t NONE $ export_t (SOME 1) ([], []) t *)
    val _ = print_time_space i
                     
    open EVM1ExportPP
    val () = println "Started Code Generation ..."
    val (prog, num_regs) = cg_prog (st_name2int, init_st) e
    val () = println "Finished Code Generation"
    val prog_str = EVM1ExportPP.pp_prog_to_string $ export_prog ((* SOME 1 *)NONE, NONE, NONE) prog
    val () = write_file (join_dir_file' dirname $ "unit-test-after-code-gen.tmp", prog_str)
    (* val () = println prog_str *)
    (* val () = println "" *)
    val inlined_prog = inline_macro_prog prog
    val inlined_prog_str = EVM1ExportPP.pp_prog_to_string $ export_prog ((* SOME 1 *)NONE, NONE, NONE) inlined_prog
    val () = write_file (join_dir_file' dirname $ "unit-test-after-inline-macro.tmp", inlined_prog_str)
    (* val () = println inlined_prog_str *)
    (* val () = println "" *)
    open EVM1Assemble
    val prog_bytes = ass2str inlined_prog
    val () = write_file (join_dir_file' dirname $ "evm-bytecode.tmp", prog_bytes)
    (* val () = println "EVM Bytecode:" *)
    (* val () = println prog_bytes *)
    (* val () = println "" *)
    open EVM1Typecheck
    val () = println "Started EVM1 typechecking ..."
    fun invert_map m = StMap.foldli (fn (k, v, acc) => IMap.insert (acc, v, k)) IMap.empty m
    val st_int2name = invert_map st_name2int
    val (i, (vcs, admits)) = evm1_typecheck (num_regs, st_name2ty, st_int2name, init_st) prog
    val () = app println $ concatMap (fn vc => VC.str_vc false filename vc @ [""]) vcs
    val () = check_vcs vcs
    val () = println "Finished EVM1 typechecking"
    val () = println $ "num-of-registers: " ^ str_int num_regs
    val i = print_time_space i
    val () = case i of
                 (IConst (ICTime t, _), IConst (ICNat s, _)) =>
                 let
                   val total_mem = s + num_regs + 1
                   fun C_mem a = C_memory * a + a * a div 512
                   open TimeType
                   val total_gas = t + fromInt (C_mem total_mem)
                 in
                   println $ "Gas-bound: " ^ str_time total_gas 
                 end
               | _ => ()

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
