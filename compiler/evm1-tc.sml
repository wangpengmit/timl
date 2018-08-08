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
infix 8 %**
infix 7 %*
infix 6 %+ 
infix 4 %<
infix 4 %>
infix 4 %<=
infix 4 %>=
infix 4 %=
infix 4 <?
infix 4 >?
infix 4 <=?
infix 4 >=?
infix 4 =?
infix 4 <>?
infixr 3 /\
infixr 3 /\?
infixr 2 \/
infixr 2 \/?
infixr 1 -->
infix 1 <->

infix 7 %/
infix 6 %-
        
infix 6 %%-
infix 6 %%%-

fun a %/ b =
  case simp_i b of
      IConst (ICNat b, r) => IDiv (a, (b, r))
    | _ => raise Impossible "a %/ b: b must be IConst"

infixr 5 @::
infixr 5 @@
infix  6 @+
infix  9 @!

infix  9 @!!
infix  9 @%!!
infix  6 @%+
         
val T0 = T0 dummy
val T1 = T1 dummy
val N0 = INat 0
val N1 = INat 1

val STime = STime dummy
val SNat = SNat dummy
val SBool = SBool dummy
val SUnit = SUnit dummy

fun add_sorting_full new ((ictx, tctx), rctx, sctx, st) = ((new :: ictx, tctx), Rctx.map (* lazy_ *)shift01_i_t rctx, map shift01_i_t sctx, (* lazy_ *)shift01_i_i st)
fun add_kinding_full new ((ictx, tctx), rctx, sctx, st) = ((ictx, new :: tctx), Rctx.map (* lazy_ *)shift01_t_t rctx, map shift01_t_t sctx, st)
fun add_r p (itctx, rctx, sctx, st) = (itctx, rctx @+ p, sctx, st)
fun add_stack t (itctx, rctx, sctx, st) = (itctx, rctx, t :: sctx, st)

fun assert_TCell t =
  let
    fun err () = raise Impossible "assert_TCell"
  in
    case t of
        TTuplePtr (ts, offset, true) =>
        (case nth_error ts offset of
             SOME t => t
           | NONE => err ()
        )
      | _ => err ()
  end

fun get_word_const_type (hctx, st_int2name, st_name2ty) c =
  case c of
      WCTT () => TUnit
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
    | WCState n =>
      let
        val x = IMapU.must_find st_int2name n
        val st_t = st_name2ty @!! x
      in
        case st_t of
            TMap _ => TCell st_t
          | TSCell t => TCell t
          | _ => TState x
      end

fun tc_w (hctx, st_int2name, st_name2ty) (ctx as (itctx as (ictx, tctx))) w =
  case w of
      WConst c => get_word_const_type (hctx, st_int2name, st_name2ty) c
    | WUninit t => kc_against_kind itctx (t, KType ())
    | WBuiltin (name, t) => kc_against_kind itctx (t, KType ())
    | WNever t => (check_prop (PFalse dummy); kc_against_kind itctx (t, KType ()))

fun is_mult32 n =
  if n mod 32 = 0 then SOME $ n div 32
  else NONE
         
(* fun is_reg_addr num_regs n = *)
(*   case is_mult32 n of *)
(*       SOME n => *)
(*       (* r0 (n=1) is for scratch space of builtin macros and can't be explicitly accessed as a register *) *)
(*       if (* 1 *)2 <= n andalso n <= num_regs then SOME $ n-1 *)
(*       else NONE *)
(*     | NONE => NONE *)
         
fun is_reg_addr num_regs n =
  case is_mult32 n of
      SOME n =>
      (* r_m (m<FIRST_GENERAL_REG) is for scratch space of builtin macros and can't be explicitly accessed as a register *)
      if FIRST_GENERAL_REG + 1 <= n andalso n <= num_regs then SOME $ n-1
      else NONE
    | NONE => NONE
         
fun is_tuple_offset num_fields n =
  case is_mult32 n of
      SOME n =>
      if 0 <= n andalso n < num_fields then SOME n
      else NONE
    | NONE => NONE

fun C_inst b =
  case b of
      POP () => C_POP
    | ORIGIN () => C_ORIGIN
    | ADDRESS () => C_ADDRESS
    | BALANCE () => C_BALANCE
    | CALLER () => C_CALLER
    | CALLVALUE () => C_CALLVALUE
    | CALLDATASIZE () => C_CALLDATASIZE
         | CALLDATALOAD () => C_CALLDATALOAD
    | CODESIZE () => C_CODESIZE
    | GASPRICE () => C_GASPRICE
    | COINBASE () => C_COINBASE
    | TIMESTAMP () => C_TIMESTAMP
    | NUMBER () => C_NUMBER
    | DIFFICULTY () => C_DIFFICULTY
    | GASLIMIT () => C_GASLIMIT
                  
    | ADD () => C_ADD
    | SUB () => C_SUB
    | LT () => C_LT
    | GT () => C_GT
    | SLT () => C_SLT
    | SGT () => C_SGT
    | EQ () => C_EQ
    | ISZERO () => C_ISZERO
    | AND () => C_AND
    | OR () => C_OR
    | XOR () => C_XOR
    | NOT () => C_NOT
    | BYTE () => C_BYTE
    | MLOAD () => C_MLOAD
    | MSTORE () => C_MSTORE
    | MSTORE8 () => C_MSTORE8
    | PUSH _ => C_PUSH
    | DUP _ => C_DUP
    | SWAP _ => C_SWAP
                  
    | MUL () => C_MUL
    | DIV () => C_DIV
    | SDIV () => C_SDIV
    | MOD () => C_MOD
    | SMOD () => C_SMOD
                  
    (* | EXP () => C_EXP *)
    | EXP () => 0 (* will depend on operands *)
                  
    | JUMPI () => C_JUMPI
                    
    | SHA3 () => C_SHA3
    | SLOAD () => C_SLOAD
    (* | SSTORE () => C_SSTORE *)
    | SSTORE () => 0 (* will depend on operands *)
    | JUMPDEST () => C_JUMPDEST
    (* extensions (noops) *)
    | VALUE_AppT _ => C_VALUE_AppT
    | VALUE_AppI _ => C_VALUE_AppI
    | VALUE_Pack _ => C_VALUE_Pack
    | VALUE_PackI _ => C_VALUE_PackI
    | VALUE_Fold _ => C_VALUE_Fold
    | VALUE_AscType _ => C_VALUE_AscType
    | UNPACK _ => C_UNPACK
    | UNPACKI _ => C_UNPACKI
    | UNFOLD _ => C_UNFOLD
    | NAT2INT _ => C_NAT2INT
    | INT2NAT _ => C_INT2NAT
    | BYTE2INT _ => C_BYTE2INT
    (* | PRINTC _ => C_PRINTC *)
    (* | PACK_SUM _ => C_PACK_SUM *)
    | ASCTIME _ => C_ASCTIME
    | ASCSPACE _ => C_ASCSPACE
    | MARK_PreArray2ArrayPtr _ => C_MARK_PreArray2ArrayPtr
    | MARK_PreTuple2TuplePtr _ => C_MARK_PreTuple2TuplePtr
    | InstRestrictPtr _ => 0
    (* | MARK_inj _ => C_MARK_inj *)
                                    
    | LOG n => C_LOG n
                           
    | Dispatch _ => C_PUSH
                      
    | MACRO_init_free_ptr _ => raise Impossible $ "C_inst() on MACRO_init_free_ptr"
    | MACRO_tuple_malloc _ => raise Impossible $ "C_inst() on MACRO_tuple_malloc"
    | MACRO_tuple_assign _ => raise Impossible $ "C_inst() on MACRO_tuple_assign"
    | MACRO_printc _ => raise Impossible $ "C_inst() on MACRO_printc"
    | MACRO_array_malloc _ => raise Impossible $ "C_inst() on MACRO_array_malloc"
    | MACRO_array_init_assign _ => raise Impossible $ "C_inst() on MACRO_array_init_assign"
    | MACRO_array_init_len _ => raise Impossible $ "C_inst() on MACRO_array_init_len"
    | MACRO_int2byte _ => raise Impossible $ "C_inst() on MACRO_int2byte"
    | MACRO_inj _ => raise Impossible $ "C_inst() on MACRO_inj"
    | MACRO_br_sum _ => raise Impossible $ "C_inst() on MACRO_br_sum"
    | MACRO_map_ptr _ => raise Impossible $ "C_inst() on MACRO_map_ptr"
    | MACRO_vector_ptr _ => raise Impossible $ "C_inst() on MACRO_vector_ptr"
    | MACRO_vector_push_back _ => raise Impossible $ "C_inst() on MACRO_vector_push_back"

         | InstJUMP () => raise Impossible $ "C_inst() on InstJUMP"
         | InstRETURN () => raise Impossible $ "C_inst() on InstRETURN"
         | InstREVERT () => raise Impossible $ "C_inst() on InstREVERT"
         | CALLDATACOPY () => raise Impossible $ "C_inst() on CALLDATACOPY"
                                        
fun C_insts insts =
  case insts of
      ISCons bind =>
      let
        val (i, is) = unBind bind
      in
        C_inst i + C_insts is
      end
    | JUMP () => C_JUMP
    | RETURN () => C_RETURN
         | REVERT () => C_REVERT
    (* only for debug/printing purpose *)
    | ISDummy _ => C_ISDummy
    | MACRO_halt _ => raise Impossible $ "C_insts() on MACRO_halt"
                           
local
  fun dummy_inline_macro_inst b = inline_macro_inst (fn _ => PUSH1nat 0, fn _ => PUSH1nat 0, 0, fn _ => 0, TUnit, fn _ => [PUSH1nat 0]) b
in
val C_inst = fn b => sum $ map C_inst $ dummy_inline_macro_inst b
val C_insts = fn b => C_insts $ inline_macro_insts (dummy_inline_macro_inst, fn _ => PUSH1nat 0, 0) b
end

fun tc_inst (hctx, num_regs, st_name2ty, st_int2name) (ctx as (itctx as (ictx, tctx), rctx, sctx, st : idx)) inst =
  let
    fun itctxn () = itctx_names itctx
    val str_t = fn t => ExportPP.pp_t_to_string NONE $ ExportPP.export_t NONE (itctxn ()) t
    fun str_ts ts = surround "[" "]" $ join ",\n" $ map (trim o str_t) ts
    (* val () = println "tc() start: " *)
    (* val () = println $ str_ts sctx *)
    (* val inst_input_str = EVM1ExportPP.pp_inst_to_string $ EVM1ExportPP.export_inst NONE (itctxn ()) inst *)
    (* val () = print $ inst_input_str *)
    (* fun arith int_result nat_result name f = *)
    (*   let *)
    (*     val (t0, t1, sctx) = assert_cons2 sctx *)
    (*     val t = *)
    (*         case (t0, t1) of *)
    (*             (TConst (TCTiML (BTInt ())), TConst (TCTiML (BTInt ()))) => int_result *)
    (*           | (TNat i0, TNat i1) => nat_result $ f (i0, i1) *)
    (*           | _ => raise Impossible $ sprintf "$: can't operate on operands of types ($) and ($)" [name, str_t t0, str_t t1] *)
    (*   in *)
    (*     ((itctx, rctx, t :: sctx, st)) *)
    (*   end *)
    fun div_mod name f =
      let
        val (t0, t1, sctx) = assert_cons2 sctx
        val t =
            case (t0, t1) of
                (TNat i0, TNat i1) => TNat $ f (i0, i1)
              (* | (TConst (TCTiML (BTInt ())), TConst (TCTiML (BTInt ()))) => TInt *)
              | _ => raise Impossible $ sprintf "$: can't operate on operands of types ($) and ($)" [name, str_t t0, str_t t1]
      in
        ((itctx, rctx, t :: sctx, st))
      end
      (* arith TInt TNat a *)
    fun sdiv_smod name f =
      let
        val (t0, t1, sctx) = assert_cons2 sctx
        val t =
            case (t0, t1) of
                (TConst (TCTiML (BTInt ())), TConst (TCTiML (BTInt ()))) => TInt
              | _ => raise Impossible $ sprintf "$: can't operate on operands of types ($) and ($)" [name, str_t t0, str_t t1]
      in
        ((itctx, rctx, t :: sctx, st))
      end
    fun cmp name f =
      let
        val (t0, t1, sctx) = assert_cons2 sctx
        val t =
            case (t0, t1) of
                (TNat i0, TNat i1) => TiBool $ f (i0, i1)
              (* | (TConst (TCTiML (BTInt ())), TConst (TCTiML (BTInt ()))) => TBool *)
              | _ => raise Impossible $ sprintf "$: can't operate on operands of types ($) and ($)" [name, str_t t0, str_t t1]
      in
        ((itctx, rctx, t :: sctx, st))
      end
      (* arith TBool TiBool a *)
    fun scmp name f =
      let
        val (t0, t1, sctx) = assert_cons2 sctx
        val t =
            case (t0, t1) of
                (TConst (TCTiML (BTInt ())), TConst (TCTiML (BTInt ()))) => TBool
              | _ => raise Impossible $ sprintf "$: can't operate on operands of types ($) and ($)" [name, str_t t0, str_t t1]
      in
        ((itctx, rctx, t :: sctx, st))
      end
    fun and_or name f =
      let
        val (t0, t1, sctx) = assert_cons2 sctx
        val t =
            case (whnf itctx t0, whnf itctx t1) of
                (TConst (TCTiML (BTBool ())), TConst (TCTiML (BTBool ()))) => TBool
              | (TiBool i0, TiBool i1) => TiBool $ f (i0, i1)
              | (TConst (TCTiML (BTInt ())), TConst (TCTiML (BTInt ()))) => TInt
              | _ => raise Impossible $ sprintf "$: can't operate on operands of types ($) and ($)" [name, str_t t0, str_t t1]
      in
        ((itctx, rctx, t :: sctx, st))
      end
    fun err () = raise Impossible $ "unknown case in tc_inst(): " ^ (EVM1ExportPP.pp_inst_to_string $ EVM1ExportPP.export_inst NONE (itctx_names itctx) inst)
    val time_ref = ref $ to_real $ C_inst inst
    val space_ref = ref N0
    val ishift_ref = ref 0
    (* val () = println $ "before time_ref = " ^ (ExportPP.str_i $ ExportPP.export_i [] $ !time_ref) *)
    fun add_time_idx n = unop_ref (fn i => ((* println $ "add_time: " ^ str_int n;  *)i %+ n)) time_ref
    fun add_time n =  add_time_idx $ to_real n
    fun add_space j = unop_ref (fn i => i %+ j) space_ref
    fun add_ishift n = unop_ref (fn m => m + n) ishift_ref
    fun open_with pair = (add_ishift 1; open_sorting pair)
    fun assert_INat_simp i = assert_INat_m (Simp.simp_i i) (fn msg => raise Impossible $ "tc_inst/assert_INat: " ^ msg)
    val ctx = 
  case inst of
      ADD () =>
      let
        val (t0, t1, sctx) = assert_cons2 sctx
        val t =
            case (t0, t1) of
                (TConst (TCTiML (BTInt ())), TConst (TCTiML (BTInt ()))) => TInt
              | (TNat i0, TNat i1) => TNat $ i1 %+ i0
              | (TNat i, TTuplePtr (ts, offset, b)) => TTuplePtr (ts, offset + assert_INat_simp i, b)
              | (TTuplePtr (ts, offset, b), TNat i) => TTuplePtr (ts, offset + assert_INat_simp i, b)
              | (TNat i, TPreTuple (ts, offset, inited)) => TPreTuple (ts, offset + assert_INat_simp i, inited)
              | (TPreTuple (ts, offset, inited), TNat i) => TPreTuple (ts, offset + assert_INat_simp i, inited)
              | (TNat i, TArrayPtr (w, t, len, offset)) => TArrayPtr (w, t, len, offset %+ i)
              | (TArrayPtr (w, t, len, offset), TNat i) => TArrayPtr (w, t, len, offset %+ i)
              | (TVectorPtr (x, offset), TNat i) => TVectorPtr (x, offset %+ i)
              | _ => raise Impossible $ sprintf "ADD: can't add operands of types ($) and ($)" [str_t t0, str_t t1]
      in
        ((itctx, rctx, t :: sctx, st))
      end
    | SUB () =>
      let
        val (t0, t1, sctx) = assert_cons2 sctx
        fun a %%- b = (check_prop (a %>= b); a %- b)
        fun a %%%- b = (assert_b "tc_inst/a>=b" (a >= b); a - b)
        val t =
            case (t0, t1) of
                (TConst (TCTiML (BTInt ())), TConst (TCTiML (BTInt ()))) => TInt
              | (TNat i0, TNat i1) => TNat $ i0 %%- i1
              | (TTuplePtr (ts, offset, b), TNat i) => TTuplePtr (ts, offset %%%- assert_INat_simp i, b)
              | (TPreTuple (ts, offset, inited), TNat i) => TPreTuple (ts, offset %%%- assert_INat_simp i, inited)
              | (TArrayPtr (w, t, len, offset), TNat i) => TArrayPtr (w, t, len, offset %%- i)
              | (TVectorPtr (x, offset), TNat i) => TVectorPtr (x, offset %%- i)
              | _ => raise Impossible $ sprintf "SUB: can't subtract operands of types ($) and ($)" [str_t t0, str_t t1]
      in
        (itctx, rctx, t :: sctx, st)
      end
    | ORIGIN () => add_stack TInt ctx
    | ADDRESS () => add_stack TInt ctx
    | BALANCE () => add_stack TInt ctx
    | CALLER () => add_stack TInt ctx
    | CALLVALUE () => add_stack TInt ctx
    | CALLDATASIZE () => add_stack TInt ctx
    | CODESIZE () => add_stack TInt ctx
    | GASPRICE () => add_stack TInt ctx
    | COINBASE () => add_stack TInt ctx
    | TIMESTAMP () => add_stack TInt ctx
    | NUMBER () => add_stack TInt ctx
    | DIFFICULTY () => add_stack TInt ctx
    | GASLIMIT () => add_stack TInt ctx
    | MUL () =>
      let
        val (t0, t1, sctx) = assert_cons2 sctx
        val t =
            case (t0, t1) of
                (TNat i0, TNat i1) => TNat $ i0 %* i1
              | (TConst (TCTiML (BTInt ())), TConst (TCTiML (BTInt ()))) => TInt
              | _ => raise Impossible $ sprintf "MUL: can't operate on operands of types ($) and ($)" [str_t t0, str_t t1]
      in
        ((itctx, rctx, t :: sctx, st))
      end
      (* mul_div "MUL" op%* *)
    | DIV () => div_mod "DIV" op%/
    | SDIV () => sdiv_smod "SDIV" op%/
    | MOD () => div_mod "MOD" IMod
    | SMOD () => sdiv_smod "SMOD" IMod
    | EXP () =>
      let
        val (t0, t1, sctx) = assert_cons2 sctx
        val t =
            case (t0, t1) of
                (TConst (TCTiML (BTInt ())), TConst (TCTiML (BTInt ()))) =>
                (add_time C_EXP_max;
                 TInt)
              | (TNat i0, TNat i1) =>
                (add_time_idx $ nat_exp_cost i1;
                 TNat $ i0 %** i1)
              | (TConst (TCTiML (BTInt ())), TNat i1) =>
                (add_time_idx $ nat_exp_cost i1;
                 TInt)
              | _ => raise Impossible $ sprintf "EXP: can't exponent operands of types ($) and ($)" [str_t t0, str_t t1]
      in
        ((itctx, rctx, t :: sctx, st))
      end
    (* | SELFDESTRUCT () => *)
    (*   let *)
    (*     val (t0, sctx) = assert_cons sctx *)
    (*     val i = assert_TNat t0 *)
    (*     val () = add_time_idx $ self_destruct_cost i *)
    (*   in *)
    (*     ((itctx, rctx, sctx, st)) *)
    (*   end *)
    | LT () => cmp "LT" op<?
    | GT () => cmp "GT" op>?
    | SLT () => scmp "SLT" op<=?
    | SGT () => scmp "SGT" op>=?
    | EQ () =>
      let
        val (t0, t1, sctx) = assert_cons2 sctx
        val t =
            case (t0, t1) of
                (TConst (TCTiML (BTInt ())), TConst (TCTiML (BTInt ()))) => TBool
              | (TConst (TCTiML (BTByte ())), TConst (TCTiML (BTByte ()))) => TBool
              | (TConst (TCTiML (BTBool ())), TConst (TCTiML (BTBool ()))) => TBool
              | (TConst (TCUnit ()), TConst (TCUnit ())) => TBool
              | (TNat i0, TNat i1) => TiBool $ i0 =? i1
              | (TiBool i0, TiBool i1) => TiBool $ i0 =? i1
              | _ => raise Impossible $ sprintf "EQ: can't operate on operands of types ($) and ($)" [str_t t0, str_t t1]
      in
        ((itctx, rctx, t :: sctx, st))
      end
      (* cmp "EQ" op=? *)
    | ISZERO () =>
      let
        val (t0, sctx) = assert_cons sctx
        val t =
            case t0 of
                TConst (TCTiML (BTBool ())) => TBool
              | TConst (TCTiML (BTInt ())) => TBool
              | TiBool i => TiBool $ INeg (i, dummy)
              | TNat i => TiBool $ i =? N0
              | _ => raise Impossible $ sprintf "ISZERO: can't operate on operand of type ($)" [str_t t0]
      in
        ((itctx, rctx, t :: sctx, st))
      end
    | NOT () =>
      let
        val (t0, sctx) = assert_cons sctx
        val t =
            case t0 of
                TConst (TCTiML (BTInt ())) => TBool
              | _ => raise Impossible $ sprintf "NOT: can't operate on operand of type ($)" [str_t t0]
      in
        ((itctx, rctx, t :: sctx, st))
      end
    | AND () => and_or "AND" op/\?
    | OR () => and_or "OR" op\/?
    | XOR () => and_or "XOR" IXor
    | POP () =>
      let
        val (t0, sctx) = assert_cons sctx
      in
        ((itctx, rctx, sctx, st))
      end
    | MLOAD () => 
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
              | TTuplePtr (ts, n, false) =>
                (case is_tuple_offset (length ts) n of
                     SOME n => List.nth (ts, n)
                   | NONE => raise Impossible $ sprintf "MLOAD: bad offset in type ($)" [str_t t0]
                )
              | TArrayPtr (w, t, len, offset) =>
                let
                  fun read () =
                    if w = 32 then
                      (check_prop (IMod (offset, N32) %= N0 /\ N1 %<= offset %/ N32 /\ offset %/ N32 %<= len);
                       t)
                    else if w = 1 then
                      (check_prop (offset %<= len); (* it's safe to read [offset, offset+32) because there is the length data *)
                       TInt)
                    else raise Impossible "evm/tc/MLoad: can't read TArrayPtr with width not 32 or 1"
                in
                  case simp_i offset of
                     IConst (ICNat n, _) =>
                     if n = 0 then TNat len
                     else read ()
                   | _ => read ()
                end
              | _ => def ()
      in
        ((itctx, rctx, t :: sctx, st))
      end
    | MSTORE () => 
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
              | TArrayPtr (32, t, len, offset) =>
                (is_eq_ty itctx (t1, t); check_prop (IMod (offset, N32) %= N0 /\ N1 %<= offset %/ N32 /\ offset %/ N32 %<= len); rctx)
              | _ => def ()
      in
        ((itctx, rctx, sctx, st))
      end
    | MSTORE8 () => 
      let
        val (t0, t1, sctx) = assert_cons2 sctx
        fun def () = raise Impossible $ sprintf "MSTORE8: can't write to address of type ($)" [str_t t0]
        val rctx =
            case t0 of
                TArrayPtr (1, t, len, offset) =>
                (is_eq_ty itctx (t1, t); check_prop (N32 %<= offset /\ offset %< N32 %+ len); rctx)
              | _ => def ()
      in
        ((itctx, rctx, sctx, st))
      end
    | JUMPDEST () => ctx
    | PUSH (n, w) =>
      (assert_b "tc/PUSH/n" (1 <= n andalso n <= 32);
       (itctx, rctx, tc_w (hctx, st_int2name, st_name2ty) itctx (unInner w) :: sctx, st))
    | Dispatch ls =>
      let
        val () = app (fn (name, t1, t2, n) =>
                         (kc_against_KType itctx $ unInner t1;
                          kc_against_KType itctx $ unInner t2; ())) ls
      in
        add_stack TUnit ctx
      end
    | DUP n => 
      let
        val () = assert_b "tc/DUP/n" (1 <= n andalso n <= 16)
        val () = assert_b "tc/DUP/stack-length" (length sctx >= n)
      in
        ((itctx, rctx, List.nth (sctx, n-1) :: sctx, st))
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
        ((itctx, rctx, swap n sctx, st))
      end
    | VALUE_AppT t =>
      let
        val (t0, sctx) = assert_cons sctx
        val t0 = whnf itctx t0
        val (_, k, _, t2) = assert_TForall t0
        val t = kc_against_kind itctx (unInner t, k)
        val t = subst0_t_t t t2
      in
        ((itctx, rctx, t :: sctx, st))
      end
    | VALUE_AppI i =>
      let
        val (t0, sctx) = assert_cons sctx
        val t0 = whnf itctx t0
        val (_, s, _, t2) = assert_TForallI t0
        val i = sc_against_sort ictx (unInner i, s)
        val t = subst0_i_t i t2
      in
        ((itctx, rctx, t :: sctx, st))
      end
    | VALUE_Pack (t_pack, t) =>
      let
        val t_pack = kc_against_kind itctx (unInner t_pack, KType ())
        val t_pack = whnf itctx t_pack
        val (_, k, t') = assert_TExists t_pack
        val t = kc_against_kind itctx (unInner t, k)
        val t_v = subst0_t_t t t'
        val (t0, sctx) = assert_cons sctx
        val () = is_eq_ty itctx (t0, t_v)
      in
        ((itctx, rctx, t_pack :: sctx, st))
      end
    | VALUE_PackI (t_pack, i) =>
      let
        val t_pack = kc_against_kind itctx (unInner t_pack, KType ())
        val t_pack = whnf itctx t_pack
        val (_, s, t') = assert_TExistsI t_pack
        val i = sc_against_sort ictx (unInner i, s)
        val t_v = subst0_i_t i t'
        val (t0, sctx) = assert_cons sctx
        val () = is_eq_ty itctx (t0, t_v)
      in
        ((itctx, rctx, t_pack :: sctx, st))
      end
    | VALUE_Fold t_fold =>
      let
        val t_fold = kc_against_kind itctx (unInner t_fold, KType ())
        val t_fold = whnf itctx t_fold
        val (t, args) = collect_TAppIT t_fold
        val ((_, k), t1) = assert_TRec t
        val t = TAppITs (subst0_t_t t t1) args
        val (t0, sctx) = assert_cons sctx
        val () = is_eq_ty itctx (t0, t)
      in
        ((itctx, rctx, t_fold :: sctx, st))
      end
    | UNFOLD () =>
      let
        val (t0, sctx) = assert_cons sctx
        val t0 = whnf itctx t0
        val (t, args) = collect_TAppIT t0
        val ((_, k), t1) = assert_TRec t
        val t = TAppITs (subst0_t_t t t1) args
      in
        ((itctx, rctx, t :: sctx, st))
      end
    | VALUE_AscType t =>
      let
        val t = kc_against_kind itctx (unInner t, KType ())
        val (t0, sctx) = assert_cons sctx
        val () = is_eq_ty itctx (t0, t)
      in
        ((itctx, rctx, t :: sctx, st))
      end
    | UNPACK name =>
      let
        val (t0, sctx) = assert_cons sctx
        val t0 = whnf itctx t0
        val (_, k, t) = assert_TExists t0
      in
        (add_stack t $ add_kinding_full (binder2str name, k) (itctx, rctx, sctx, st))
      end
    | UNPACKI name =>
      let
        val (t0, sctx) = assert_cons sctx
        val t0 = whnf itctx t0
        val (_, s, t) = assert_TExistsI t0
        val new = (binder2str name, s)
        val () = open_with new
      in
        (add_stack t $ add_sorting_full new (itctx, rctx, sctx, st))
      end
    | NAT2INT () =>
      let
        val (t0, sctx) = assert_cons sctx
        val _ = assert_TNat $ whnf itctx t0
      in
        ((itctx, rctx, TInt :: sctx, st))
      end
    | INT2NAT () =>
      let
        val (t0, sctx) = assert_cons sctx
        val _ = assert_TInt $ whnf itctx t0
      in
        ((itctx, rctx, TSomeNat () :: sctx, st))
      end
    | BYTE2INT () =>
      let
        val (t0, sctx) = assert_cons sctx
        val _ = assert_TByte $ whnf itctx t0
      in
        ((itctx, rctx, TInt :: sctx, st))
      end
    | MACRO_printc () =>
      let
        val (t0, sctx) = assert_cons sctx
        val _ = assert_TByte $ whnf itctx t0
      in
        ((itctx, rctx, TUnit :: sctx, st))
      end
    | MACRO_int2byte () =>
      let
        val (t0, sctx) = assert_cons sctx
        val _ = assert_TInt $ whnf itctx t0
      in
        ((itctx, rctx, TByte :: sctx, st))
      end
    | MACRO_init_free_ptr _ => ctx
    | MACRO_array_malloc (width, t, is_upward) =>
      let
        val t = kc_against_kind itctx (unInner t, KType ())
        val () = good_width itctx width t
        val (t0, sctx) = assert_cons sctx
        val len = assert_TNat $ whnf itctx t0
        val lowest = if is_upward then N0 else len
        val () = add_space $ len %* N width %+ N 32
      in
        ((itctx, rctx, TPreArray (width, t, len, lowest, (false, is_upward)) :: sctx, st))
      end
    | MACRO_array_init_assign width =>
      let
        val (t0, t1, t2, sctx) = assert_cons3 sctx
        val offset = assert_TNat $ whnf itctx t0
        val (width', t, len, lowest, (len_inited, is_upward)) = assert_TPreArray $ whnf itctx t1
        val () = assert_b "evm-tc/array_init_assign: width' = width" $ width' = width
        val () = is_eq_ty itctx (t2, t)
        (* val () = println $ "is_upward = " ^ str_bool is_upward *)
        (* val () = println $ "offset = " ^ (ExportPP.str_i $ ExportPP.export_i (fst $ itctxn ()) offset) *)
        (* val () = println $ "lowest = " ^ (ExportPP.str_i $ ExportPP.export_i (fst $ itctxn ()) lowest) *)
      in
        (* todo: offset shouldn't be left on the result stack *)
        if is_upward then
          (check_prop (IMod (offset, N width) %= N0 /\ offset %/ N width %= lowest);
           ((itctx, rctx, TNat offset :: TPreArray (width, t, len, lowest %+ N1, (len_inited, is_upward)) :: t2 :: sctx, st)))
        else
          (check_prop (IMod (offset, N width) %= N0 /\ offset %/ N width %+ N1 %= lowest);
           ((itctx, rctx, TNat offset :: TPreArray (width, t, len, lowest %- N1, (len_inited, is_upward)) :: t2 :: sctx, st)))
      end
    | MACRO_array_init_len () =>
      let
        val (t0, t1, sctx) = assert_cons2 sctx
        val len' = assert_TNat $ whnf itctx t0
        val (w, t, len, lowest_inited, (_, dir)) = assert_TPreArray $ whnf itctx t1
        val () = check_prop (len' %= len)
      in
        ((itctx, rctx, TPreArray (w, t, len, lowest_inited, (true, dir)) :: sctx, st))
      end
    | MARK_PreArray2ArrayPtr () =>
      let
        val (t0, sctx) = assert_cons sctx
        val (w, t, len, lowest, (len_inited, is_upward)) = assert_TPreArray $ whnf itctx t0
        val () = assert_b "len_inited = true" (len_inited = true)
        val () =
            if is_upward then
              check_prop (lowest %= len)
            else
              check_prop (lowest %= N0)
      in
        (itctx, rctx, TArrayPtr (w, t, len, N32) :: sctx, st)
      end
    | MACRO_tuple_malloc ts =>
      let
        val ts = map (kc_against_KType itctx) $ unInner ts
        val len = length ts
        val () = add_space $ N $ 32*len
      in
        (add_stack (TPreTuple (ts, 0, len)) ctx)
      end
    | MACRO_tuple_assign () =>
      let
        val (t0, t1, sctx) = assert_cons2 sctx
        val (ts, offset, lowest_inited) = assert_TPreTuple $ whnf itctx t1
        val () = assert_b "tc_inst/MACRO_tuple_assign" (offset >= 0 andalso offset mod 32 = 0 andalso (offset div 32) + 1 = lowest_inited)
        (* val () = check_prop (IMod (offset, N32) %= N0 /\ offset %/ N32 %+ N1 %= lowest_inited) *)
        val () = is_eq_ty itctx (t0, List.nth (ts, lowest_inited - 1))
      in
        ((itctx, rctx, TPreTuple (ts, offset, lowest_inited - 1) :: sctx, st))
      end
    | MARK_PreTuple2TuplePtr () =>
      let
        val (t0, sctx) = assert_cons sctx
        val (t, offset, lowest_inited) = assert_TPreTuple $ whnf itctx t0
        val () = assert_b "tc_inst/MARK_PreTuple2TuplePtr" (lowest_inited = 0)
      in
        ((itctx, rctx, TTuplePtr (t, offset, false) :: sctx, st))
      end
    | MACRO_inj t_other =>
      let
        val t_other = kc_against_kind itctx (unInner t_other, KType ())
        val (t0, t1, sctx) = assert_cons2 sctx
        val b = assert_IBool $ simp_i $ assert_TiBool $ whnf itctx t0
        val inj = if b then InjInr () else InjInl ()
        val ts = choose_pair_inj (t1, t_other) inj
        val () = add_space $ N $ 32*2
      in
        ((itctx, rctx, TSum ts :: sctx, st))
      end
    | MACRO_vector_ptr () =>
      let
        val (t0, t1, sctx) = assert_cons2 sctx
        val vec = assert_TState t0
        val offset = assert_TNat t1
      in
        ((itctx, rctx, TVectorPtr (vec, offset) :: sctx, st))
      end
    | MACRO_vector_push_back () =>
      let
        val (t0, t1, sctx) = assert_cons2 sctx
        val vec = assert_TState t1
        val len = st @%!! vec
        val t = assert_TVector $ st_name2ty @!! vec
        val () = is_eq_ty itctx (t0, t)
      in
        ((itctx, rctx, sctx, st @%+ (vec, len %+ N1)))
      end
    | MACRO_map_ptr () =>
      let
        val (t0, t1, sctx) = assert_cons2 sctx
        val t1 = whnf itctx t1
        val ts = assert_TTuple $ assert_TMap $ assert_TCell t1
        val () = assert_TInt t0
      in
        ((itctx, rctx, TStorageTuplePtr (ts, 0) :: sctx, st))
      end
    | InstRestrictPtr len =>
      let
        val (t0, sctx) = assert_cons sctx
        val t0 = whnf itctx t0
        val (ts, offset) = assert_TStorageTuplePtr t0
        val () = assert_b "InstRestrictPtr/assert()" $ offset + len <= length ts
        val ts = take len $ drop offset ts
      in
        ((itctx, rctx, TStorageTuplePtr (ts, 0) :: sctx, st))
      end
    | SLOAD () => 
      let
        val (t0, sctx) = assert_cons sctx
        fun def () = raise Impossible $ sprintf "SLOAD: can't read from address of type ($)" [str_t t0]
        val t =
            case t0 of
                TVectorPtr (vec, offset) =>
                let
                  val len = st @%!! vec
                  val t = assert_TVector $ st_name2ty @!! vec
                  val () = check_prop (offset %< len)
                in
                  t
                end
              | TState x =>
                (case st_name2ty @!! x of
                     TVector _ =>
                     TNat $ st @%!! x
                   | TNatCell () =>
                     TNat $ st @%!! x
                   | _ => def ()
                )
              | TTuplePtr _ =>
                let
                  val t = assert_TCell t0
                  val () = assert_wordsize_ty t
                in
                  t
                end
              | _ => def ()
      in
        ((itctx, rctx, t :: sctx, st))
      end
    | SSTORE () => 
      let
        val (t0, t1, sctx) = assert_cons2 sctx
        fun def () = raise Impossible $ sprintf "SSTORE: can't read from address of type ($)" [str_t t0]
        val st =
            case t0 of
                TVectorPtr (vec, offset) =>
                let
                  val len = st @%!! vec
                  val t = assert_TVector $ st_name2ty @!! vec
                  val () = check_prop (offset %< len)
                  val () = is_eq_ty itctx (t1, t)
                  val () = add_time C_sset
                in
                  st
                end
              | TState x =>
                (case st_name2ty @!! x of
                     TVector _ =>
                     let
                       val new = assert_TNat t1
                       val () = check_prop (new %= N0)
                       val () = add_time C_sreset
                     in
                       st @%+ (x, N0)
                     end
                   | TNatCell () => 
                     let
                       val old = st @%!! x
                       val new = assert_TNat t1
                       (* todo: opportunity to collect reward *)
                       val award = IIte' (old <>? N0 /\? new =? N0, to_real R_sclear, T0)
                       val cost = IIte' (old =? N0 /\? new <>? N0, to_real C_sset, to_real C_sreset)
                       val () = add_time_idx cost
                     in
                       st @%+ (x, new)
                     end
                   | _ => def ()
                )
              | TTuplePtr _ =>
                let
                  val t = assert_TCell t0
                  val () = assert_wordsize_ty t
                  val () = is_eq_ty itctx (t1, t)
                  val () = add_time C_sset
                in
                  st
                end
              | _ => def ()
      in
        ((itctx, rctx, sctx, st))
      end
    | BYTE () => err ()
    | SHA3 () => err ()
    | JUMPI () => err ()
    | LOG _ => err ()
    | ASCTIME _ => err ()
    | ASCSPACE _ => err ()
    | MACRO_br_sum () => err ()
         | CALLDATALOAD () => err ()
         | CALLDATACOPY () => err ()
         | InstJUMP () => err ()
         | InstRETURN () => err ()
         | InstREVERT () => err ()
    (* val () = println $ "before time_ref = " ^ (ExportPP.str_i $ ExportPP.export_i [] $ !time_ref) *)
    val ret = (ctx, (!time_ref, !space_ref), !ishift_ref)
    (* val () = println "tc() finished:" *)
    (* val () = print $ inst_input_str *)
  in
    ret
  end
      
fun TProd (a, b) = TMemTuplePtr ([a, b], 0)

infix 6 %%+ 
infix 4 %%<=
        
fun shiftn_i_i n = shiftx_i_i 0 n
fun shiftn_i_2i n (a, b) = (shiftn_i_i n a, shiftn_i_i n b)
fun forget_i_2i x n = unop_pair $ forget_i_i x n
      
fun tc_insts (params as (hctx, num_regs, st_name2ty, st_int2name)) (ctx as (itctx as (ictx, tctx), rctx, sctx, st)) insts =
  let
    val tc_insts = tc_insts params
    fun itctxn () = itctx_names itctx
    val str_t = fn t => ExportPP.pp_t_to_string NONE $ ExportPP.export_t NONE (itctxn ()) t
    fun str_ts ts = surround "[" "]" $ join ",\n" $ map (trim o str_t) ts
    fun is_eq_stack itctx (sctx, sctx') =
      let
        fun itctxn () = itctx_names itctx
        val str_t = fn t => ExportPP.pp_t_to_string NONE $ ExportPP.export_t NONE (itctxn ()) t
        fun str_ts ts = surround "[" "]" $ join ",\n" $ map (trim o str_t) ts
        fun extra_msg () = sprintf "\nwhen comparing stack \n$\nagainst stack \n$\n" [str_ts sctx, str_ts sctx']
      in
        is_eq_tys itctx (sctx, sctx')
        handle Impossible msg => raise Impossible $ msg ^ extra_msg ()
             | MUnifyError (r, m) => raise MTCError $ "Unification error:\n" ^ join_lines m ^ extra_msg ()
             | MTCError m => raise MTCError $ m ^ extra_msg ()
      end
    fun is_eq_st ictx (i, i') =
      let
        (* val ictxn = map fst ictx *)
        (* val () = println $ sprintf "to compare states\n$\nand\n$" [ExportPP.str_i $ ExportPP.export_i ictxn i, ExportPP.str_i $ ExportPP.export_i ictxn i'] *)
        val (vars, _, m) = decompose_state i
        val (vars', _, m') = decompose_state i'
        (* val () = println $ "vars: " ^ ISetU.str_set str_int vars *)
        (* val () = println $ "vars': " ^ ISetU.str_set str_int vars' *)
        val () = assert_b "vars == vars'" $ (ISet.equal (vars, vars'))
        val () = assert_b "is_eq_st/is_same_domain" $ (StMapU.is_same_domain m m')
        val () = check_sub_map (m, m')
      in
        ()
      end
    fun err () = raise Impossible $ "unknown case in tc_insts(): " ^ (EVM1ExportPP.pp_insts_to_string $ EVM1ExportPP.export_insts (NONE, NONE) (itctx_names itctx) insts)
    fun main () =
  case insts of
      JUMP () =>
      let
        (* val () = println "JUMP" *)
        val (t0, sctx) = assert_cons sctx
        val t0 = whnf itctx t0
        val (st', rctx', sctx', i) = assert_TArrowEVM t0
        val () = is_sub_rctx itctx (rctx, rctx')
        val () = is_eq_stack itctx (sctx, sctx')
        val () = is_eq_st ictx (st, st')
      in
        (TN (C_insts insts) %%+ i, 0)
      end
    (* | ISHalt t => *)
    (*   let *)
    (*     val t = kc_against_kind itctx (t, KType ()) *)
    (*     val () = tc_v_against_ty ctx (VReg 1, t) *)
    (*   in *)
    (*     T1 *)
    (*   end *)
    | MACRO_halt (b, t) =>
      let
        val t = kc_against_KType itctx t
        val () = is_eq_stack itctx (sctx, [t])
      in
        (TN $ C_insts insts, 0)
      end
    | ISDummy _ => (TN $ C_insts insts, 0)
    | RETURN () => err ()
    | REVERT () => err ()
    | ISCons bind =>
      let
        val (inst, I) = unBind bind
      in
        case inst of
            JUMPI () =>
            let
              (* val () = println $ str_ts sctx *)
              (* val () = println "JUMPI" *)
              val (t0, t1, sctx) = assert_cons2 sctx
            in
              case whnf itctx t1 of
                  TConst TCBool =>
                  let
                    val () = assert_TBool $ whnf itctx t1
                    val t0 = whnf itctx t0
                    val (st', rctx', sctx', i2) = assert_TArrowEVM t0
                    val () = is_sub_rctx itctx (rctx, rctx')
                    val () = is_eq_stack itctx (sctx, sctx')
                    val () = is_eq_st ictx (st, st')
                    val (i1, ni) = tc_insts (itctx, rctx, sctx, st) I
                  in
                    (TN (C_inst inst) %%+ IMaxPair (i1, shiftn_i_2i ni i2), ni)
                  end
                | TiBool i =>
                  let
                    val (t2, sctx) = assert_cons sctx
                    val () = assert_TUnit "tc()/JUMP_I" $ whnf itctx t2
                    val t0 = whnf itctx t0
                    val (st', rctx', sctx', i2) = assert_TArrowEVM t0
                    val () = is_sub_rctx itctx (rctx, rctx')
                    val make_exists = make_exists "__p"
                    val t1 = make_exists (SSubset_from_prop dummy $ i %= Ifalse)
                    val t2 = make_exists (SSubset_from_prop dummy $ i %= Itrue)
                    val () = is_eq_stack itctx (t2 :: sctx, sctx')
                    val () = is_eq_st ictx (st, st')
                    val (i1, ni) = tc_insts (itctx, rctx, t1 :: sctx, st) I
                  in
                    (TN (C_inst inst) %%+ IMaxPair (i1, shiftn_i_2i ni i2), ni)
                  end
                | t1 => raise Impossible $ "tc()/JUMPI wrong type of t1: " ^ str_t t1
            end
          | MACRO_br_sum () =>
            let
              val (t0, t1, sctx) = assert_cons2 sctx
              val (tl, tr) = assert_TSum $ whnf itctx t1
              val t0 = whnf itctx t0
              val (st', rctx', sctx', i2) = assert_TArrowEVM t0
              val () = is_sub_rctx itctx (rctx, rctx')
              val () = is_eq_stack itctx (TProd (TiBoolConst true, tr) :: sctx, sctx')
              val () = is_eq_st ictx (st, st')
              val (i1, ni) = tc_insts (itctx, rctx, TProd (TiBoolConst false, tl) :: sctx, st) I
            in
              (TN (C_inst inst) %%+ IMaxPair (i1, shiftn_i_2i ni i2), ni)
            end
          | ASCTIME i =>
            let
              val i = sc_against_sort ictx (unInner i, STime)
              val ((i', j), ni) = tc_insts ctx I
              val () = close_n ni
              val (i', j) = forget_i_2i 0 ni (i', j)
              val () = check_prop (i' %<= i)
            in
              ((i, j), 0)
            end
          | ASCSPACE i =>
            let
              val i = sc_against_sort ictx (unInner i, SNat)
              val ((j, i'), ni) = tc_insts ctx I
              val () = close_n ni
              val (j, i') = forget_i_2i 0 ni (j, i')
              val () = check_prop (i' %<= i)
            in
              ((j, i), 0)
            end
          | _ =>
            let
              val (ctx, i1, ni1) = tc_inst params ctx inst 
              val (i2, ni2) = tc_insts ctx I
            in
              (shiftn_i_2i ni2 i1 %%+ i2, ni1 + ni2)
            end
      end
    fun extra_msg () = "\nwhen typechecking\n" ^ (EVM1ExportPP.pp_insts_to_string $ EVM1ExportPP.export_insts (SOME 3, SOME 5) (itctx_names itctx) insts)
    val ret = main ()
              handle
              Impossible m => raise Impossible (m ^ extra_msg ())
              | MUnifyError (r, m) => raise MTCError ("Unification error:\n" ^ join_lines m ^ extra_msg ())
              | ForgetError (r, m) => raise MTCError ("Forgetting error: " ^ m ^ extra_msg ())
              | MSCError (r, m) => raise MTCError ("Sortcheck error:\n" ^ join_lines m ^ extra_msg ())
              | MTCError m => raise MTCError (m ^ extra_msg ())
  in
    ret
  end

fun tc_hval (params as (hctx, num_regs, st_name2ty, st_int2name)) h =
  let
    (* val () = println "tc_hval() started" *)
    val (itbinds, ((st, rctx, sctx, (time, space)), insts)) = unBind h
    val itbinds = unTeles itbinds
    (* val () = println "before getting itctx" *)
    val itctx as (ictx, tctx) =
        foldl
          (fn (bind, (ictx, tctx)) =>
              case bind of
                  inl (name, s) =>
                  let
                    val new = (binder2str name, is_wf_sort ictx $ unOuter s)
                    val () = open_sorting new
                  in
                    (new :: ictx, tctx)
                  end
                | inr (name, k) =>
                  (ictx, (binder2str name, unOuter k) :: tctx)
          ) ([], []) itbinds
    (* val () = println "before checking rctx" *)
    (* val itctxn = itctx_names itctx *)
    val rctx = Rctx.mapi
                 (fn (r, t) =>
                     let
                       (* val () = println $ sprintf "checking r$: $" [str_int r, ExportPP.pp_t_to_string NONE $ ExportPP.export_t NONE itctxn t] *)
                       val ret = kc_against_kind itctx (t, KType ())
                       (* val () = println "done" *)
                     in
                       ret
                     end) rctx
    (* val () = println "before checking sctx" *)
    val sctx = map (kc_against_KType itctx) sctx
    (* val () = println "before checking i" *)
    val time = sc_against_sort ictx (time, STime)
    val space = sc_against_sort ictx (space, SNat)
    val st = sc_against_sort ictx (st, SState)
    (* val () = println "before checking insts" *)
    val (i', ni) = tc_insts params (itctx, rctx, sctx, st) insts
    (* val () = println "after checking insts" *)
    val () = close_n ni
    val i' = forget_i_2i 0 ni i'
    val () = check_prop (i' %%<= (time, space))
    val () = close_n $ length ictx
    (* val () = println "tc_hval() finished" *)
  in
    ()
  end

fun tc_prog (num_regs, st_name2ty, st_int2name, init_st) (H, I) =
  let
    fun get_hval_type h =
      let
        val (itbinds, ((st, rctx, sctx, i), _)) = unBind h
        val itbinds = unTeles itbinds
        val itbinds = map (map_inl_inr (mapPair' unBinderName unOuter) (mapPair' unBinderName unOuter)) itbinds
        val t = TForallITs (itbinds, TArrowEVM (st, rctx, sctx, i))
      in
        t
      end
    fun get_hctx H = RctxUtil.fromList $ map (mapPair' fst get_hval_type) H
    val hctx = get_hctx H
    val () = app (fn ((l, name), h) =>
                     (
                       (* println $ sprintf "tc_hval() on: $ <$>" [str_int l, name]; *)
                       tc_hval (hctx, num_regs, st_name2ty, st_int2name) h)) H
    val (i, ni) = tc_insts (hctx, num_regs, st_name2ty, st_int2name) (([], []), Rctx.empty, [], init_st) I
    val () = close_n ni
    val i = forget_i_2i 0 ni i
  in
    i
  end
    
fun evm1_typecheck params P =
  let
    val ret = runWriter (fn () => tc_prog params P) ()
  in
    ret
  end

end
