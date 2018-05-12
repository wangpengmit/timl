(* TiTAL evaluator (i.e. simulator) *)

structure TiTALEval = struct

open UVarExprUtil
open Expr
open MicroTiMLUtilTiML
open MicroTiMLUtil
open MicroTiMLLongId
open TiTAL
open TiTALVisitor

infixr 0 $
       
infix 9 %@
infix 8 %^
infix 7 %*
infix 6 %+ 
infix 4 %<=
infix 4 %<
infix 4 %>=
infix 4 %=
infixr 3 /\
infixr 2 \/
infixr 1 -->
infix 1 <->

fun adapt f d x v env = f (d + env) (x + env) v
fun subst_i_insts d x v = subst_i_insts_fn (adapt substx_i_i d x v, adapt subst_i_t d x v)
fun subst0_i_insts a = subst_i_insts 0 0 a
fun adapt f d x v env b =
  let
    fun add_depth (di, dt) (di', dt') = (idepth_add (di, di'), tdepth_add (dt, dt'))
  in
    f (add_depth d env) (x + unTDepth (snd env)) v b
  end
fun subst_t_insts d x v = subst_t_insts_fn (adapt subst_t_t d x v)
fun subst0_t_insts a = subst_t_insts (IDepth 0, TDepth 0) 0 a

fun subst0_its_insts itargs b =
  let
    val (len_i, len_t) = foldl
                           (fn (v, (ni, nt)) =>
                               case v of
                                   inl _ => (ni+1, nt)
                                 | inr _ => (ni, nt+1)
                           ) (0, 0) itargs
    val b = fst $ foldl
                (fn (v, (b, (ni, nt))) =>
                    case v of
                        inl v => (subst_i_insts (ni-1) (ni-1) v b, (ni-1, nt))
                      | inr v => (subst_t_insts (IDepth ni, TDepth (nt-1)) (nt-1) v b, (ni, nt-1))
                ) (b, (len_i, len_t)) itargs
  in
    b
  end
                    
infixr 5 @::
infixr 5 @@
infix  6 @+
infix  9 @!
       
(* word values *)
datatype ('idx, 'ty) wordv =
         WVLabel of label
         | WVConst of word_const
         | WVUninit
         (* | WVBuiltin of 'ty *)
         (* | WVNever of 'ty *)
         | WVAppT of ('idx, 'ty) wordv * 'ty
         | WVAppI of ('idx, 'ty) wordv * 'idx
         | WVPack of 'ty * 'ty * ('idx, 'ty) wordv
         | WVPackI of 'ty * 'idx * ('idx, 'ty) wordv
         | WVFold of 'ty * ('idx, 'ty) wordv
                                       
(* heap value *)
datatype ('idx, 'sort, 'kind, 'ty) heapv =
         HVCode of ('idx, 'sort, 'kind, 'ty) hval
         | HVPair of ('idx, 'ty) wordv * ('idx, 'ty) wordv
         | HVInj of injector * ('idx, 'ty) wordv
         | HVArray of ('idx, 'ty) wordv list
         | HVString of string

fun must_find (m, _) k = assert_SOME $ Rctx.find (m, k)
                                       
infix  9 @!!
fun m @!! k = must_find m k

fun add (m, max_k) (k, v) = (m @+ (k, v), max max_k k)
fun m @+ p = add m p

fun fresh_key (_, max_k) = max_k + 1

val fresh_label = fresh_key
                  
fun read_v R v =
  case v of
      VReg r => R @!! r
    | VWord w =>
      (case w of
           WLabel l => WVLabel l
         | WConst c => WVConst c
         | WUninit t => WVUninit
         | WBuiltin (name, _) => raise Impossible $ "unknown WBuiltin: " ^ name
         | WNever _ => raise Impossible "WNever is not a legal word value"
      )
      | VAppI (v, i) => WVAppI (read_v R v, i)
      | VAppT (v, t) => WVAppT (read_v R v, t)
      | VPack (t', t, v) => WVPack (t', t, read_v R v)
      | VPackI (t', i, v) => WVPackI (t', i, read_v R v)
      | VFold (t, v) => WVFold (t, read_v R v)
      | VAscType (v, t) => read_v R v

infix  9 @^
fun R @^ v = read_v R v                               

fun collect_WVAppIT_rev t =
  let
    val self = collect_WVAppIT_rev
  in
    case t of
        WVAppI (t, i) =>
        let
          val (t, args) = self t
        in
          (t, inl i :: args)
        end
      | WVAppT (t, t') =>
        let
          val (t, args) = self t
        in
          (t, inr t' :: args)
        end
      | _ => (t, [])
  end
fun collect_WVAppIT t = mapSnd rev $ collect_WVAppIT_rev t

fun assert_fail msg = Impossible $ "Assert failed: " ^ msg
                             
fun assert_VAscType t =
  case t of
      VAscType a => a
    | _ => raise assert_fail "assert_VAscType"

fun assert_WVLabel t =
  case t of
      WVLabel a => a
    | _ => raise assert_fail "assert_WVLabel"

fun assert_WVPack t =
  case t of
      WVPack a => a
    | _ => raise assert_fail "assert_WVPack"

fun assert_WVPackI t =
  case t of
      WVPackI a => a
    | _ => raise assert_fail "assert_WVPackI"

fun assert_WVFold t =
  case t of
      WVFold a => a
    | _ => raise assert_fail "assert_WVFold"

fun WVInt n = WVConst $ WCInt n
fun assert_WVInt t =
  case t of
      WVConst (WCInt a) => a
    | _ => raise assert_fail "assert_WVInt"

fun WVByte n = WVConst $ WCByte n
fun assert_WVByte t =
  case t of
      WVConst (WCByte a) => a
    | _ => raise assert_fail "assert_WVByte"

fun WVNat n = WVConst $ WCNat n
fun assert_WVNat t =
  case t of
      WVConst (WCNat a) => a
    | _ => raise assert_fail "assert_WVNat"

val WVTT = WVConst WCTT
fun assert_WVTT t =
  case t of
      WVConst WCTT => ()
    | _ => raise assert_fail "assert_WVTT"

fun WVBool n = WVConst $ WCBool n
fun assert_WVBool t =
  case t of
      WVConst (WCBool a) => a
    | _ => raise assert_fail "assert_WVBool"

fun WViBool n = WVConst $ WCiBool n
fun assert_WViBool t =
  case t of
      WVConst (WCiBool a) => a
    | _ => raise assert_fail "assert_WViBool"

fun assert_HVCode t =
  case t of
      HVCode a => a
    | _ => raise assert_fail "assert_HVCode"

fun assert_HVPair t =
  case t of
      HVPair a => a
    | _ => raise assert_fail "assert_HVPair"

fun assert_HVInj t =
  case t of
      HVInj a => a
    | _ => raise assert_fail "assert_HVInj"

fun assert_HVArray t =
  case t of
      HVArray a => a
    | _ => raise assert_fail "assert_HVArray"

fun assert_HVString t =
  case t of
      HVString a => a
    | _ => raise assert_fail "assert_HVString"

fun choose_update proj (b1, b2) new =
  case proj of
      ProjFst => (new, b2)
    | ProjSnd => (b1, new)

fun interp_prim_expr_un_op opr a =
  case opr of
      EUPIntNeg => WVInt $ ~ (assert_WVInt a)
    | EUPBoolNeg => WVBool $ not (assert_WVBool a)
    | EUPInt2Byte => WVByte $ Char.chr $ assert_WVInt a mod 256
    | EUPByte2Int => WVInt $ Char.ord $ assert_WVByte a
    (* | _ => raise Impossible $ "interp_prim_expr_un_op() on: " ^ str_prim_expr_un_op opr *)
                   
fun interp_prim_expr_bin_op opr (a, b) =
  case opr of
      EBPIntAdd => WVInt $ assert_WVInt a + assert_WVInt b
    | EBPIntMult => WVInt $ assert_WVInt a * assert_WVInt b
    | EBPIntMinus => WVInt $ assert_WVInt a - assert_WVInt b
    | EBPIntDiv => WVInt $ assert_WVInt a div assert_WVInt b
    | EBPIntMod => WVInt $ assert_WVInt a mod assert_WVInt b
    | EBPIntLt => WVBool $ assert_WVInt a < assert_WVInt b
    | EBPIntGt => WVBool $ assert_WVInt a > assert_WVInt b
    | EBPIntLe => WVBool $ assert_WVInt a <= assert_WVInt b
    | EBPIntGe => WVBool $ assert_WVInt a >= assert_WVInt b
    | EBPIntEq => WVBool $ assert_WVInt a = assert_WVInt b
    | EBPIntNEq => WVBool $ assert_WVInt a <> assert_WVInt b
    | EBPBoolAnd => WVBool (assert_WVBool a andalso assert_WVBool b)
    | EBPBoolOr => WVBool (assert_WVBool a orelse assert_WVBool b)
    (* | EBPStrConcat => raise Impossible "interp_prim_expr_bin_op() on EBPStrConcat" *)
                            
fun interp_nat_expr_bin_op opr (a, b) =
  case opr of
      EBNAdd => WVNat $ assert_WVNat a + assert_WVNat b
    | EBNBoundedMinus => WVNat $ max 0 $ assert_WVNat a - assert_WVNat b
    | EBNMult => WVNat $ assert_WVNat a * assert_WVNat b
    | EBNDiv => WVNat $ assert_WVNat a div assert_WVNat b

fun upd n v ls = update n (const_fun v) ls
                                                           
fun get_code (H, R) v =
  let
    val w = R @^ v
    val (w, itargs) = collect_WVAppIT w
    val l = assert_WVLabel w
    val c = assert_HVCode $ H @!! l
    val (itbinds, (_, I')) = unBind c
    val itbinds = unTeles itbinds
    val () = assert_b "#itargs = #itbinds" $ length itargs = length itbinds
    val I' = subst0_its_insts itargs I'
  in
    I'
  end

fun char2str c = String.implode [c]
                               
fun step (H, R, I) =
  case I of
      ISHalt _ => raise Impossible "can't step() on ISHalt"
    | ISJmp v =>
      let
      in
        (H, R, get_code (H, R) v)
      end
    | ISDummy _ => raise Impossible "can't step() on ISDummy"
    | ISCons bind =>
      let
        val (inst, I') = unBind bind
      in
        case inst of
            IUnOp (IUBrSum, r, v) =>
            let
              val (inj, w) = assert_HVInj $ must_find H $ assert_WVLabel $ R @!! r
            in
              case inj of
                  InjInl => (H, R @+ (r, w), I')
                | InjInr => (H, R @+ (r, w), get_code (H, R) $ unInner v)
            end
          | IUnOp (IUBrI, r, v) =>
            let
              val b = assert_WViBool $ R @!! r
              val make_exists = make_exists "__p"
              val t = make_exists (Subset_from_prop dummy $ IBool b %= IBool b)
              (* val t = TUnit (* type doesn't matter, so just a placeholder *) *)
              val w = WVPackI (t, TTI dummy, WVTT)
            in
              if b then (H, R @+ (r, w), I')
              else (H, R @+ (r, w), get_code (H, R) $ unInner v)
            end
          | IUnOp (IUBrBool, r, v) =>
            if assert_WVBool $ R @!! r then
              (H, R, I')
            else
              (H, R, get_code (H, R) $ unInner v)
          | IUnOp (IUMov, rd, v) =>
            (H, R @+ (rd, R @^ unInner v), I')
          | IUnOp (IUPrintc, rd, v) =>
            (print $ char2str $ assert_WVByte $ R @^ unInner v;
            (H, R @+ (rd, WVTT), I'))
          (* | IUnOp (IUPrint, rd, v) => *)
          (*   (print $ assert_HVString $ must_find H $ assert_WVLabel $ R @^ unInner v; *)
          (*   (H, R @+ (rd, WVTT), I')) *)
          | IUnOp (IUUnfold, rd, v) =>
            let
              val (t, w) = assert_WVFold $ R @^ unInner v
            in
              (H, R @+ (rd, w), I')
            end
          | IUnOp (IUArrayLen, rd, v) =>
            (H, R @+ (rd, WVNat $ length $ assert_HVArray $ must_find H $ assert_WVLabel $ R @^ unInner v), I')
          (* | IUnOp (IUPrim EUPInt2Str, rd, v) => *)
          (*   let *)
          (*     val l = fresh_label H *)
          (*   in *)
          (*     (H @+ (l, HVString $ str_int $ assert_WVInt $ R @^ unInner v), R @+ (rd, WVLabel l), I') *)
          (*   end *)
          (* | IUnOp (IUPrim EUPStrLen, rd, v) => *)
          (*   (H, R @+ (rd, WVInt $ String.size $ assert_HVString $ must_find H $ assert_WVLabel $ R @^ unInner v), I') *)
          | IUnOp (IUPrim opr, rd, v) =>
            (H, R @+ (rd, interp_prim_expr_un_op opr $ R @^ unInner v), I')
          | IUnOp (IUNat2Int, rd, v) =>
            (H, R @+ (rd, WVInt $ assert_WVNat $ R @^ unInner v), I')
          | IUnOp (IUInt2Nat, rd, v) =>
            let
              val n = assert_WVInt $ R @^ unInner v
              val v = WVNat n
              val v = WVPackI (TSomeNat_packed (), TTI dummy, v)
              val v = WVPackI (TSomeNat_packed2 (), ConstIN (n, dummy), v)
              val v = WVFold (TSomeNat (), v)
            in
              (H, R @+ (rd, v), I')
            end
          (* | IBinOp (IBPrim EBPStrConcat, rd, rs, v) => *)
          (*   let *)
          (*     val l = fresh_label H *)
          (*     val s1 = assert_HVString $ must_find H $ assert_WVLabel $ R @!! rs *)
          (*     val s2 = assert_HVString $ must_find H $ assert_WVLabel $ R @^ unInner v *)
          (*   in *)
          (*     (H @+ (l, HVString $ s1 ^ s2), R @+ (rd, WVLabel l), I') *)
          (*   end *)
          | IBinOp (IBPrim opr, rd, rs, v) =>
            (H, R @+ (rd, interp_prim_expr_bin_op opr (R @!! rs, R @^ unInner v)), I')
          | IBinOp (IBNat opr, rd, rs, v) =>
            (H, R @+ (rd, interp_nat_expr_bin_op opr (R @!! rs, R @^ unInner v)), I')
          | IBinOp (IBNatCmp opr, rd, rs, v) =>
            let
              val n1 = assert_WVNat $ R @!! rs
              val n2 = assert_WVNat $ R @^ unInner v
              val i1 = INat n1
              val i2 = INat n2
              fun eval_nat_cmp opr =
                case opr of
                    NCLt => op<
                  | NCGt => op>
                  | NCLe => op<=
                  | NCGe => op>=
                  | NCEq => op=
                  | NCNEq => op<>
              val b = eval_nat_cmp opr (n1, n2)
            in
              (H, R @+ (rd, WViBool b), I')
            end
          | IMallocPair (rd, (v1, v2)) =>
            let
              (* val (v1, t1) = assert_VAscType $ unInner v1 *)
              (* val (v2, t2) = assert_VAscType $ unInner v2 *)
              val l = fresh_label H
            in
              (H @+ (l, HVPair (WVUninit, WVUninit)), R @+ (rd, WVLabel l), I')
            end
          | ILd (rd, (rs, proj)) =>
            (H, R @+ (rd, flip choose proj $ assert_HVPair $ must_find H $ assert_WVLabel $ R @!! rs), I')
          | ISt ((rd, proj), rs) =>
            let
              val l = assert_WVLabel $ R @!! rd
              val pair = assert_HVPair $ H @!! l
              val pair = choose_update proj pair $ R @!! rs
            in
              (H @+ (l, HVPair pair), R, I')
            end
          | IUnpack (name, rd, v) =>
            let
              val (_, t, w) = assert_WVPack $ R @^ unOuter v
            in
              (H, R @+ (rd, w), subst0_t_insts t I')
            end
          | IUnpackI (name, rd, v) =>
            let
              val (_, i, w) = assert_WVPackI $ R @^ unOuter v
            in
              (H, R @+ (rd, w), subst0_i_insts i I')
            end
          | IBinOp (IBNew, rd, rs, v) =>
            let
              val n = assert_WVNat $ R @!! rs
              val l = fresh_label H
            in
              (H @+ (l, HVArray $ repeat n $ R @^ unInner v), R @+ (rd, WVLabel l), I')
            end
          | INewArrayValues (rd, t, vs) =>
            let
              val l = fresh_label H
            in
              (H @+ (l, HVArray $ map (fn v => R @^ unInner v) vs), R @+ (rd, WVLabel l), I')
            end
          | IBinOp (IBRead, rd, rs, v) =>
            let
              val l = assert_WVLabel $ R @!! rs
              val n = assert_WVNat $ R @^ unInner v
              val ls = assert_HVArray $ H @!! l
              val () = assert_b "step()/IRead/n<#ls" $ n < length ls
              val w = List.nth (ls, n)
            in
              (H, R @+ (rd, w), I')
            end
          | IBinOp (IBWrite, rd, rs, v) =>
            let
              val l = assert_WVLabel $ R @!! rd
              val n = assert_WVNat $ R @!! rs
              val v = R @^ unInner v
              val ls = assert_HVArray $ H @!! l
              val () = assert_b "step()/IWrite/n<#ls" $ n < length ls
            in
              (H @+ (l, HVArray $ upd n v ls), R @+ (rd, WVTT), I')
            end
          | IInj (rd, inj, v, t_other) =>
            let
              val l = fresh_label H
            in
              (H @+ (l, HVInj (inj, R @^ unInner v)), R @+ (rd, WVLabel l), I')
            end
          (* | IString (rd, s) => *)
          (*   let *)
          (*     val l = fresh_label H *)
          (*   in *)
          (*     (H @+ (l, HVString s), R @+ (rd, WVLabel l), I') *)
          (*   end *)
          | IAscTime _ => (H, R, I')
      end

fun eval (P as (H, R, I)) =
  case I of
      ISHalt t => (* trace "" $  *)R @!! 1
    | _ => eval $ (* trace_noln "." $  *)step P
                
end
