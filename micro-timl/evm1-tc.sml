(* EVM1 typechecking *)

structure EVM1Typecheck = struct

open Simp
open EVM1Util
open EVMCosts
open MicroTiMLTypecheck
open CompilerUtil
open EVM1

infixr 0 $

infix 9 %@
infix 8 %^
infix 7 %*
infix 7 %/
infix 6 %+ 
infix 6 %-
infix 4 %<
infix 4 %>
infix 4 %<=
infix 4 %>=
infix 4 %=
infix 4 %<?
infix 4 %>?
infix 4 %<=?
infix 4 %>=?
infix 4 %=?
infix 4 %<>?
infixr 3 /\
infixr 2 \/
infixr 3 /\?
infixr 2 \/?
infixr 1 -->
infix 1 <->

infix 6 %%-

fun a %/ b =
  case simp_i b of
      IConst (ICNat b, r) => DivI (a, (b, r))
    | _ => raise Impossible "a %/ b: b must be IConst"

fun INeg i = UnOpI (Neg, i, dummy)
fun a %<>? b = INeg $ a %=? b
                     
infixr 5 @::
infixr 5 @@
infix  6 @+
infix  9 @!

val T0 = T0 dummy
val T1 = T1 dummy
val N0 = INat 0
val N1 = INat 1

fun TProd (a, b) = TTuplePtr ([a, b], N0)

fun add_sorting_full new ((ictx, tctx), rctx, sctx) = ((new :: ictx, tctx), Rctx.map (* lazy_ *)shift01_i_t rctx, map shift01_i_t sctx)
fun add_kinding_full new ((ictx, tctx), rctx, sctx) = ((ictx, new :: tctx), Rctx.map (* lazy_ *)shift01_t_t rctx, map shift01_t_t sctx)
fun add_r p (itctx, rctx, sctx) = (itctx, rctx @+ p, sctx)
fun add_stack t (itctx, rctx, sctx) = (itctx, rctx, t :: sctx)

fun get_word_const_type hctx c =
  case c of
      WCTT => TUnit
    | WCNat n => TNat $ INat n
    | WCInt _ => TInt
    | WCBool _ => TBool
    | WCiBool b => TiBool $ IBool b
    | WCByte _ => TByte
    | WCLabel l =>
      (case hctx @! l of
           SOME t => t
         | NONE => raise Impossible $ "unbound label: " ^ str_int l
      )

fun tc_w hctx (ctx as (itctx as (ictx, tctx))) w =
  case w of
      WConst c => get_word_const_type hctx c
    | WUninit t => kc_against_kind itctx (t, KType)
    | WBuiltin (name, t) => kc_against_kind itctx (t, KType)
    | WNever t => kc_against_kind itctx (t, KType)

fun is_mult32 n =
  if n mod 32 = 0 then SOME $ n div 32
  else NONE
         
fun is_reg_addr num_regs n =
  case is_mult32 n of
      SOME n =>
      (* r0 (n=1) is for scratch space of builtin macros and can't be explicitly accessed as a register *)
      if (* 1 *)2 <= n andalso n <= num_regs then SOME $ n-1
      else NONE
    | NONE => NONE
         
fun is_tuple_offset num_fields n =
  case is_mult32 n of
      SOME n =>
      if 0 <= n andalso n < num_fields then SOME n
      else NONE
    | NONE => NONE
         
fun tc_inst (hctx, num_regs) (ctx as (itctx as (ictx, tctx), rctx, sctx)) inst =
  let
    fun itctxn () = itctx_names itctx
    val str_t = fn t => ExportPP.pp_t_to_string NONE $ ExportPP.export_t NONE (itctxn ()) t
    fun arith int_result nat_result name f time =
      let
        val (t0, t1, sctx) = assert_cons2 sctx
        val t =
            case (t0, t1) of
                (TConst (TCTiML Int), TConst (TCTiML Int)) => int_result
              | (TNat i0, TNat i1) => nat_result $ f (i0, i1)
              | _ => raise Impossible $ sprintf "$: can't operate on operands of types ($) and ($)" [name, str_t t0, str_t t1]
      in
        ((itctx, rctx, t :: sctx), time)
      end
    fun mul_div a = arith TInt TNat a
    fun cmp a = arith TBool TiBool a
    fun and_or name f time =
      let
        val (t0, t1, sctx) = assert_cons2 sctx
        val t =
            case (t0, t1) of
                (TConst (TCTiML Bool), TConst (TCTiML Bool)) => TBool
              | (TiBool i0, TiBool i1) => TiBool $ f (i0, i1)
              | _ => raise Impossible $ sprintf "$: can't operate on operands of types ($) and ($)" [name, str_t t0, str_t t1]
      in
        ((itctx, rctx, t :: sctx), time)
      end
  in
  case inst of
      ADD =>
      let
        val (t0, t1, sctx) = assert_cons2 sctx
        val t =
            case (t0, t1) of
                (TConst (TCTiML Int), TConst (TCTiML Int)) => TInt
              | (TNat i0, TNat i1) => TNat $ i1 %+ i0
              | (TNat i, TTuplePtr (ts, offset)) => TTuplePtr (ts, offset %+ i)
              | (TTuplePtr (ts, offset), TNat i) => TTuplePtr (ts, offset %+ i)
              | (TNat i, TPreTuple (ts, offset, inited)) => TPreTuple (ts, offset %+ i, inited)
              | (TPreTuple (ts, offset, inited), TNat i) => TPreTuple (ts, offset %+ i, inited)
              | (TNat i, TArrayPtr (t, len, offset)) => TArrayPtr (t, len, offset %+ i)
              | (TArrayPtr (t, len, offset), TNat i) => TArrayPtr (t, len, offset %+ i)
              | _ => raise Impossible $ sprintf "ADD: can't add operands of types ($) and ($)" [str_t t0, str_t t1]
      in
        ((itctx, rctx, t :: sctx), T_ADD)
      end
    | SUB =>
      let
        val (t0, t1, sctx) = assert_cons2 sctx
        fun a %%- b = (check_prop ictx (a %>= b); a %- b)
        val t =
            case (t0, t1) of
                (TConst (TCTiML Int), TConst (TCTiML Int)) => TInt
              | (TNat i0, TNat i1) => TNat $ i0 %%- i1
              | (TTuplePtr (ts, offset), TNat i) => TTuplePtr (ts, offset %%- i)
              | (TPreTuple (ts, offset, inited), TNat i) => TPreTuple (ts, offset %%- i, inited)
              | (TArrayPtr (t, len, offset), TNat i) => TArrayPtr (t, len, offset %%- i)
              | _ => raise Impossible $ sprintf "SUB: can't subtract operands of types ($) and ($)" [str_t t0, str_t t1]
      in
        ((itctx, rctx, t :: sctx), T_SUB)
      end
    | MUL => mul_div "MUL" op%* T_MUL
    | DIV => mul_div "DIV" op%/ T_DIV
    | SDIV => mul_div "SDIV" op%/ T_SDIV
    | MOD => mul_div "MOD" IMod T_MOD
    | LT => cmp "LT" op%<? T_LT
    | GT => cmp "GT" op%>? T_GT
    | SLT => cmp "LT" op%<=? T_SLT
    | SGT => cmp "GT" op%>=? T_SGT
    | EQ => cmp "EQ" op%=? T0
    | ISZERO =>
      let
        val (t0, sctx) = assert_cons sctx
        val t =
            case t0 of
                TConst (TCTiML Bool) => TBool
              | TConst (TCTiML Int) => TBool
              | TiBool i0 => TiBool $ INeg i0
              | _ => raise Impossible $ sprintf "ISZERO: can't operate on operand of type ($)" [str_t t0]
      in
        ((itctx, rctx, t :: sctx), T0)
      end
    | AND => cmp "AND" op/\? T0
    | OR => cmp "OR" op\/? T0
    | POP =>
      let
        val (t0, sctx) = assert_cons sctx
      in
        ((itctx, rctx, sctx), T0)
      end
    | MLOAD => 
      let
        val (t0, sctx) = assert_cons sctx
        fun def () = raise Impossible $ sprintf "MLOAD: can't read from address of type ($)" [str_t t0]
        val t =
            case t0 of
                TNat i0 =>
                (case simp_i i0 of
                    IConst (ICNat n, _) =>
                    (case is_reg_addr num_regs n of
                         SOME n =>
                         (case rctx @! n of
                              SOME t => t
                            | NONE => raise Impossible $ sprintf "MLOAD: reg$'s type is unknown" [str_int n])
                       | NONE => def ())
                  | _ => def ())
              | TTuplePtr (ts, offset) =>
                (case simp_i offset of
                     IConst (ICNat n, _) =>
                     (case is_tuple_offset (length ts) n of
                          SOME n => List.nth (ts, n)
                        | NONE => raise Impossible $ sprintf "MLOAD: bad offset in type ($)" [str_t t0])
                   | _ => raise Impossible $ sprintf "MLOAD: unknown offset in type ($)" [str_t t0])
              | TArrayPtr (t, len, offset) =>
                let
                  fun read () = (check_prop ictx (IMod (offset, N32) %= N0 /\ N1 %<= offset %/ N32 /\ offset %/ N32 %<= len); t)
                in
                  case simp_i offset of
                     IConst (ICNat n, _) =>
                     if n = 0 then TNat len
                     else read ()
                   | _ => read ()
                end
              | _ => def ()
      in
        ((itctx, rctx, t :: sctx), T_MLOAD)
      end
    | MSTORE => 
      let
        val (t0, t1, sctx) = assert_cons2 sctx
        fun def () = raise Impossible $ sprintf "MSTORE: can't write to address of type ($)" [str_t t0]
        val rctx =
            case t0 of
                TNat i0 =>
                let
                in
                  case simp_i i0 of
                      IConst (ICNat n, _) =>
                      (case is_reg_addr num_regs n of
                           SOME n => rctx @+ (n, t1)
                         | NONE => def ())
                    | _ => def ()
                end
              | TArrayPtr (t, len, offset) =>
                (is_eq_ty itctx (t1, t); check_prop ictx (IMod (offset, N32) %= N0 /\ N1 %<= offset %/ N32 /\ offset %/ N32 %<= len); rctx)
              | _ => def ()
      in
        ((itctx, rctx, sctx), T_MSTORE)
      end
    | JUMPDEST => (ctx, T0)
    | PUSH (n, w) =>
      (assert_b "tc/PUSH/n" (1 <= n andalso n <= 32); ((itctx, rctx, tc_w hctx itctx (unInner w) :: sctx), T_PUSH))
    | DUP n => 
      let
        val () = assert_b "tc/DUP/n" (1 <= n andalso n <= 16)
        val () = assert_b "tc/DUP/stack-length" (length sctx >= n)
      in
        ((itctx, rctx, List.nth (sctx, n-1) :: sctx), T0)
      end
    | SWAP n => 
      let
        val () = assert_b "tc/SWAP/n" (1 <= n andalso n <= 16)
        val () = assert_b "tc/SWAP/stack-length" (length sctx >= n+1)
        fun swap n ls =
          let
            val ls1 = take n ls
            val ls2 = drop n ls
            val (a1, ls1) = assert_cons ls1
            val (a2, ls2) = assert_cons ls2
          in
            a2 :: ls1 @ (a1 :: ls2)
          end
      in
        ((itctx, rctx, swap n sctx), T0)
      end
    | VALUE_AppT t =>
      let
        val (t0, sctx) = assert_cons sctx
        val t0 = whnf itctx t0
        val ((_, k), t2) = assert_TForall t0
        val t = kc_against_kind itctx (unInner t, k)
        val t = subst0_t_t t t2
      in
        ((itctx, rctx, t :: sctx), T0)
      end
    | VALUE_Pack (t_pack, t) =>
      let
        val t_pack = kc_against_kind itctx (unInner t_pack, KType)
        val t_pack = whnf itctx t_pack
        val ((_, k), t') = assert_TExists t_pack
        val t = kc_against_kind itctx (unInner t, k)
        val t_v = subst0_t_t t t'
        val (t0, sctx) = assert_cons sctx
        val () = is_eq_ty itctx (t0, t_v)
      in
        ((itctx, rctx, t_pack :: sctx), T0)
      end
    | VALUE_Fold t_fold =>
      let
        val t_fold = kc_against_kind itctx (unInner t_fold, KType)
        val t_fold = whnf itctx t_fold
        val (t, args) = collect_TAppIT t_fold
        val ((_, k), t1) = assert_TRec t
        val t = TAppITs (subst0_t_t t t1) args
        val (t0, sctx) = assert_cons sctx
        val () = is_eq_ty itctx (t0, t)
      in
        ((itctx, rctx, t_fold :: sctx), T0)
      end
    | VALUE_AscType t =>
      let
        val t = kc_against_kind itctx (unInner t, KType)
        val (t0, sctx) = assert_cons sctx
        val () = is_eq_ty itctx (t0, t)
      in
        ((itctx, rctx, t :: sctx), T0)
      end
    | UNPACK name =>
      let
        val (t0, sctx) = assert_cons sctx
        val t0 = whnf itctx t0
        val ((_, k), t) = assert_TExists t0
      in
        (add_stack t $ add_kinding_full (binder2str name, k) (itctx, rctx, sctx), T0)
      end
    | UNFOLD =>
      let
        val (t0, sctx) = assert_cons sctx
        val t0 = whnf itctx t0
        val (t, args) = collect_TAppIT t0
        val ((_, k), t1) = assert_TRec t
        val t = TAppITs (subst0_t_t t t1) args
      in
        ((itctx, rctx, t :: sctx), T0)
      end
    | NAT2INT =>
      let
        val (t0, sctx) = assert_cons sctx
        val _ = assert_TNat $ whnf itctx t0
      in
        ((itctx, rctx, TInt :: sctx), T0)
      end
    | INT2NAT =>
      let
        val (t0, sctx) = assert_cons sctx
        val _ = assert_TInt $ whnf itctx t0
      in
        ((itctx, rctx, TSomeNat () :: sctx), T0)
      end
    | BYTE2INT =>
      let
        val (t0, sctx) = assert_cons sctx
        val _ = assert_TByte $ whnf itctx t0
      in
        ((itctx, rctx, TInt :: sctx), T0)
      end
    | MACRO_printc =>
      let
        val (t0, sctx) = assert_cons sctx
        val _ = assert_TByte $ whnf itctx t0
      in
        ((itctx, rctx, TUnit :: sctx), T0)
      end
    | MACRO_int2byte =>
      let
        val (t0, sctx) = assert_cons sctx
        val _ = assert_TInt $ whnf itctx t0
      in
        ((itctx, rctx, TByte :: sctx), T0)
      end
    | MACRO_init_free_ptr _ => (ctx, T0)
    | MACRO_array_malloc t =>
      let
        val t = kc_against_kind itctx (unInner t, KType)
        val (t0, sctx) = assert_cons sctx
        val len = assert_TNat $ whnf itctx t0
      in
        ((itctx, rctx, TPreArray (t, len, len, false) :: sctx), T0)
      end
    | MACRO_array_init_assign =>
      let
        val (t0, t1, t2, sctx) = assert_cons3 sctx
        val offset = assert_TNat $ whnf itctx t0
        val (t, len, lowest_inited, len_inited) = assert_TPreArray $ whnf itctx t1
        val () = is_eq_ty itctx (t2, t)
        val () = check_prop ictx (IMod (offset, N32) %= N0 /\ offset %/ N32 %+ N1 %= lowest_inited)
      in
        ((itctx, rctx, TNat len :: TPreArray (t, len, lowest_inited %- N1, len_inited) :: t2 :: sctx), T0)
      end
    | MACRO_array_init_len =>
      let
        val (t0, t1, sctx) = assert_cons2 sctx
        val len' = assert_TNat $ whnf itctx t0
        val (t, len, lowest_inited, _) = assert_TPreArray $ whnf itctx t1
        val () = check_prop ictx (len' %= len)
      in
        ((itctx, rctx, TPreArray (t, len, lowest_inited, true) :: sctx), T0)
      end
    | MARK_PreArray2ArrayPtr =>
      let
        val (t0, sctx) = assert_cons sctx
        val (t, len, lowest_inited, len_inited) = assert_TPreArray $ whnf itctx t0
        val () = assert_b "len_inited = true" (len_inited = true)
        val () = check_prop ictx (lowest_inited %= N0)
      in
        ((itctx, rctx, TArrayPtr (t, len, N32) :: sctx), T0)
      end
    | MACRO_tuple_malloc ts =>
      let
        val ts = map (kc_against_KType itctx) $ unInner ts
      in
        (add_stack (TPreTuple (ts, N0, INat (length ts))) ctx, T0)
      end
    | MACRO_tuple_assign =>
      let
        val (t0, t1, sctx) = assert_cons2 sctx
        val (ts, offset, lowest_inited) = assert_TPreTuple $ whnf itctx t1
        val () = check_prop ictx (IMod (offset, N32) %= N0 /\ offset %/ N32 %+ N1 %= lowest_inited)
        val n = assert_INat $ simp_i lowest_inited
        val () = is_eq_ty itctx (t0, List.nth (ts, n-1))
      in
        ((itctx, rctx, TPreTuple (ts, offset, lowest_inited %- N1) :: sctx), T0)
      end
    | MARK_PreTuple2TuplePtr =>
      let
        val (t0, sctx) = assert_cons sctx
        val (t, offset, lowest_inited) = assert_TPreTuple $ whnf itctx t0
        val () = check_prop ictx (lowest_inited %= N0)
      in
        ((itctx, rctx, TTuplePtr (t, offset) :: sctx), T0)
      end
    | MACRO_inj t_other =>
      let
        val t_other = kc_against_kind itctx (unInner t_other, KType)
        val (t0, t1, sctx) = assert_cons2 sctx
        val b = assert_IBool $ simp_i $ assert_TiBool $ whnf itctx t0
        val inj = if b then InjInr else InjInl
        val ts = choose_pair_inj (t1, t_other) inj
      in
        ((itctx, rctx, TSum ts :: sctx), T0)
      end
    | _ => raise Impossible $ "unknown case in tc_inst(): " ^ (EVM1ExportPP.pp_inst_to_string $ EVM1ExportPP.export_inst NONE (itctx_names itctx) inst)
  end
      
fun tc_insts (params as (hctx, num_regs)) (ctx as (itctx as (ictx, tctx), rctx, sctx)) insts =
  let
    val tc_insts = tc_insts params
    fun itctxn () = itctx_names itctx
    val str_t = fn t => ExportPP.pp_t_to_string NONE $ ExportPP.export_t NONE (itctxn ()) t
    fun main () =
  case insts of
      JUMP =>
      let
        val (t0, sctx) = assert_cons sctx
        val t0 = whnf itctx t0
        val (rctx', sctx', i) = assert_TArrowEVM t0
        val () = is_sub_rctx itctx (rctx, rctx')
        val () = is_eq_tys itctx (sctx, sctx')
      in
        T_JUMP %+ i
      end
    (* | ISHalt t => *)
    (*   let *)
    (*     val t = kc_against_kind itctx (t, KType) *)
    (*     val () = tc_v_against_ty ctx (VReg 1, t) *)
    (*   in *)
    (*     T1 *)
    (*   end *)
    | MACRO_halt t =>
      let
        val t = kc_against_KType itctx t
        val () = is_eq_tys itctx (sctx, [t])
      in
        T0
      end
    | ISDummy _ => T0
    | ISCons bind =>
      let
        val (inst, I) = unBind bind
      in
        case inst of
            JUMPI =>
            let
              val (t0, t1, sctx) = assert_cons2 sctx
            in
              case whnf itctx t1 of
                  TConst TCBool =>
                  let
                    val () = assert_TBool $ whnf itctx t1
                    val t0 = whnf itctx t0
                    val (rctx', sctx', i2) = assert_TArrowEVM t0
                    val () = is_sub_rctx itctx (rctx, rctx')
                    val () = is_eq_tys itctx (sctx, sctx')
                    val i1 = tc_insts ctx I
                  in
                    T_JUMPI %+ IMax (i1, i2)
                  end
                | TiBool i =>
                  let
                    val (t2, sctx) = assert_cons sctx
                    val () = assert_TUnit "tc()/JUMP_I" $ whnf itctx t2
                    val t0 = whnf itctx t0
                    val (rctx', sctx', i2) = assert_TArrowEVM t0
                    val () = is_sub_rctx itctx (rctx, rctx')
                    val make_exists = make_exists "__p"
                    val t1 = make_exists (Subset_from_prop dummy $ i %= Ifalse)
                    val t2 = make_exists (Subset_from_prop dummy $ i %= Itrue)
                    val () = is_eq_tys itctx (t1 :: sctx, sctx')
                    val i1 = tc_insts (add_stack t2 ctx) I
                  in
                    T0 %+ IMax (i1, i2)
                  end
                | t1 => raise Impossible $ "tc()/JUMPI wrong type of t1: " ^ str_t t1
            end
          | MACRO_br_sum =>
            let
              val (t0, t1, sctx) = assert_cons2 sctx
              val (tl, tr) = assert_TSum $ whnf itctx t1
              val t0 = whnf itctx t0
              val (rctx', sctx', i2) = assert_TArrowEVM t0
              val () = is_sub_rctx itctx (rctx, rctx')
              val () = is_eq_tys itctx (TProd (TBool, tr) :: sctx, sctx')
              val i1 = tc_insts (add_stack (TProd (TBool, tl)) ctx) I
            in
              T0 %+ IMax (i1, i2)
            end
          | ASCTIME i =>
            let
              val i = sc_against_sort ictx (unInner i, STime)
              val i' = tc_insts ctx I
              val () = check_prop ictx (i' %<= i)
            in
              i
            end
          | _ =>
            let
              val (ctx, i1) = tc_inst params ctx inst 
              val i2 = tc_insts ctx I
            in
              i1 %+ i2
            end
      end
    | _ => raise Impossible $ "unknown case in tc_insts(): " ^ (EVM1ExportPP.pp_insts_to_string $ EVM1ExportPP.export_insts (NONE, NONE) (itctx_names itctx) insts)
    fun extra_msg () = "\nwhen typechecking\n" ^ (EVM1ExportPP.pp_insts_to_string $ EVM1ExportPP.export_insts (SOME 2, SOME 5) (itctx_names itctx) insts)
    val ret = main ()
              handle
              Impossible m => raise Impossible (m ^ extra_msg ())
              | MUnifyError (r, m) => raise MTCError ("Unification error:\n" ^ join_lines m ^ extra_msg ())
              (* | ForgetError (r, m) => raise MTCError ("Forgetting error: " ^ m ^ extra_msg ()) *)
              (* | MSCError (r, m) => raise MTCError ("Sortcheck error:\n" ^ join_lines m ^ extra_msg ()) *)
              (* | MTCError m => raise MTCError (m ^ extra_msg ()) *)
  in
    ret
  end

fun tc_hval (params as (hctx, num_regs)) h =
  let
    val () = println "tc_hval() started"
    val (itbinds, ((rctx, sctx, i), insts)) = unBind h
    val itbinds = unTeles itbinds
    val () = println "before getting itctx"
    val itctx as (ictx, tctx) =
        foldl
          (fn (bind, (ictx, tctx)) =>
              case bind of
                  inl (name, s) => ((binder2str name, is_wf_sort ictx $ unOuter s) :: ictx, tctx)
                | inr (name, k) => (ictx, (binder2str name, k) :: tctx)
          ) ([], []) itbinds
    val () = println "before checking rctx"
    (* val itctxn = itctx_names itctx *)
    val rctx = Rctx.mapi
                 (fn (r, t) =>
                     let
                       (* val () = println $ sprintf "checking r$: $" [str_int r, ExportPP.pp_t_to_string NONE $ ExportPP.export_t NONE itctxn t] *)
                       val ret = kc_against_kind itctx (t, KType)
                       (* val () = println "done" *)
                     in
                       ret
                     end) rctx
    val () = println "before checking sctx"
    val sctx = map (kc_against_KType itctx) sctx
    val () = println "before checking i"
    val i = sc_against_sort ictx (i, STime)
    val () = println "before checking insts"
    val i' = tc_insts params (itctx, rctx, sctx) insts
    val () = println "after checking insts"
    val () = check_prop ictx (i' %<= i)
    val () = println "tc_hval() finished"
  in
    ()
  end

fun tc_prog num_regs (H, I) =
  let
    fun get_hval_type h =
      let
        val (itbinds, ((rctx, sctx, i), _)) = unBind h
        val itbinds = unTeles itbinds
        val itbinds = map (map_inl_inr (mapPair' unBinderName unOuter) (mapFst unBinderName)) itbinds
        val t = TForallITs (itbinds, TArrowEVM (rctx, sctx, i))
      in
        t
      end
    fun get_hctx H = RctxUtil.fromList $ map (mapPair' fst get_hval_type) H
    val hctx = get_hctx H
    val () = app (fn ((l, name), h) => (println $ sprintf "tc_hval() on: $ <$>" [str_int l, name]; tc_hval (hctx, num_regs) h)) H
    val i = tc_insts (hctx, num_regs) (([], []), Rctx.empty, []) I
  in
    i
  end
    
fun evm1_typecheck num_regs P =
  let
    val ret = runWriter (fn () => tc_prog num_regs P) ()
  in
    ret
  end

end
