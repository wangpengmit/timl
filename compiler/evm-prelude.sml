structure EVMPrelude = struct

open Util
open BaseTypes
open MicroTiML
open EVM1Util
open EVM1
open EVM1OtherNames
open MicroTiMLUtil

infixr 0 $

infixr 5 @@
         
fun keccak256 s =
  let
    (* val filename = "keccak256.in.tmp" *)
    (* val () = write_bin_file (filename, s) *)
    val out_filename = "keccak256.out.tmp"
    val cmd = "keccak-256sum -l"
    val cmd = sprintf "echo -n '' | $ > $" [s, cmd, out_filename]
    val () = println $ "Running cmd: " ^ cmd
    val _ = OS.Process.system cmd
    val r = read_file out_filename
    val () = println $ "keccak256 result: " ^ r
  in
    r
  end
    
fun get_func_sig (name, t) =
  let
    fun str_t t =
      case t of
          TConst (TCTiML (BTInt ())) => "int256"
        | TConst (TCTiML (BTByte ())) => "uint8"
        | TConst (TCUnit ()) => "uint8"
        | TTuple ts => surround "(" ")" $ join "," $ map str_t ts
        | TArray (1, t, _) => "bytes" (* or "string"? *)
        | TArray (32, t, _) => str_t t ^ "[]"
        | _ => raise Impossible "get_func_sig: unknown type"
    fun str_arg t =
      case t of
          TConst (TCUnit ()) => "()"
        | TTuple _ => str_t t
        | _ => surround "(" ")" $ str_t t
    val sg = name ^ str_arg t
    val sg = keccak256 sg
    val sg = String.substring (sg, 0, 8)
    val sg = assert_some_m (fn () => raise Impossible "get_func_sig/str2int") $ str2int $ "0x" ^ sg
    val () = println $ "fun sig: " ^ hex 4 sg
  in
    sg
  end
    
fun is_Int_Byte_Unit t =
  case t of
      TConst (TCTiML (BTInt ())) => true
    | TConst (TCTiML (BTByte ())) => true
    | TConst (TCUnit ()) => true
    | _ => false

fun assert_Int_Byte_Unit t = assert_b "assert_Int_Byte_Unit" $ is_Int_Byte_Unit t = true

fun make_tuple n =
  (* [v_(n-1), ..., v_0] *)
  [TupleMalloc (repeat n $ TUnit)] @
  int_concatMap_rev
    (fn i => [
       (* [ptr, v_i, v_(i-1)] *)
       Swap1, (* [v_i, ptr, v_(i-1)] *)
       Dup2, (* [ptr, v_i, ptr, v_(i-1)] *)
       Push $ i*32,
       Add, (* [ptr+32*i, v_i, ptr, v_(i-1)] *)
       MStore (* [ptr, v_(i-1)] *)
    ]) n
(* [ptr] *)
    
fun untuple_save n =
  (* [ptr_to_tuple] *)
  int_concatMap (fn i => [Dup1, Push $ i*32, Add, MLoad, Swap1]) n
(* [ptr_to_tuple, v_(n-1), ..., v_0] *)
                
fun untuple n = untuple_save n @ [Pop]

fun decode pos t =
  case t of
      TTuple ts =>
      concatMapi (fn (i, t) => decode (pos + i * 32) t) ts @
      make_tuple (length ts)
    | TArray (w, t, len) =>
      let
        val () = assert_Int_Byte_Unit t
      in
        [
          Push pos,
          CallDataLoad,
          Push 4,
          Add, (* [ptr_to_input_array_len] *)
          Dup1,
          CallDataLoad, (* [array_len, ptr_to_input_array_len] *)
          Dup1, (* [array_len, array_len, ptr_to_input_array_len] *)
          ArrayMalloc (w, t, true), (* [ptr_to_array, array_len, ptr_to_input_array_len] *)
          Dup2,
          ArrayInitLen, (* [ptr_to_array, array_len, ptr_to_input_array_len] *)
          Swap1, (* [array_len, ptr_to_array, ptr_to_input_array_len] *)
          Push w,
          Mul, (* [array_len*w, ptr_to_array, ptr_to_input_array_len] *)
          Dup2, (* [ptr_to_array, array_len*w, ptr_to_array, ptr_to_input_array_len] *)
          Swap3, (* [ptr_to_input_array_len, array_len*w, ptr_to_array, ptr_to_array] *)
          Push 32,
          Add, (* [ptr_to_input_array, array_len*w, ptr_to_array, ptr_to_array] *)
          Swap1, (* [array_len*w, ptr_to_input_array, ptr_to_array, ptr_to_array] *)
          Swap2, (* [ptr_to_array, ptr_to_input_array, array_len*w, ptr_to_array] *)
          CallDataCopy (* [ptr_to_array] *)
        ]
      end
    | TConst (TCUnit ()) =>
      [ Push 0 ]
    | _ =>
      if is_Int_Byte_Unit t then
        [
          Push pos,
          CallDataLoad
        ]
      else
        raise Impossible "Can't decode type"

(* both tuple_len and pos_in_tuple are in bytes *)                  
fun encode_array w tuple_len pos_in_tuple =
  let
    (* the encoded data reuses the array's buffer, appending the tuple before the array *)
    (* there should be at least 'tuple_len' words before the array, such as the free pointer and scratch space *)
    val () = assert_b "encode_array: tuple_len <= ..." $ tuple_len <= FIRST_GENERAL_REG + 1
    val n = 32 * tuple_len
    val p = 32 * pos_in_tuple
  in
    [ (* [ptr_to_array] *)
      Push 32,
      Swap1,
      Sub, (* [ptr_to_array_len] *)
      Dup1, (* [ptr_to_array_len, ptr_to_array_len] *)
      MLoad, (* [array_len, ptr_to_array_len] *)
      Swap1, (* [ptr_to_array_len, array_len] *)
      Push n,
      Swap1,
      Sub, (* [ptr_to_array_len-n, array_len] *) 
      Push n,
      Dup2, (* [ptr_to_array_len-n, n, ptr_to_array_len-n, array_len] *)
      Push p,
      Add, (* [ptr_to_array_len-n+p, n, ptr_to_array_len-n, array_len] *)
      MStore, (* [ptr_to_array_len-n, array_len] *)
      Swap1, (* [array_len, ptr_to_array_len-n] *)
      Push w,
      Mul,
      Push $ 32+n,
      Add, (* [array_len*w+32+n, ptr_to_array_len-n] *)
      Swap1 (* [ptr_to_array_len-n, array_len*w+32+n] *)
    ] @
    (if w <> 32 then
       (* if w <> 32, we write an empty word after the array in order to meet the right-padding requirement *)
       [
         Dup2, (* [array_len*w+32+n, ptr_to_array_len-n, array_len*w+32+n] *)
         Dup2, (* [ptr_to_array_len-n, array_len*w+32+n, ptr_to_array_len-n, array_len*w+32+n] *)
         Add, (* [ptr_to_array_len+array_len*w+32=ptr_to_array_end, ptr_to_array_len-n, array_len*w+32+n] *)
         Push 0,
         Swap1,
         MStore (* [ptr_to_array_len-n, array_len*w+32+n] *)
       ]
     else
       []
    )
  end

fun is_TArray t =
  case t of
      TArray a => SOME a
    | _ => NONE
             
fun at_most_one_Array_other_Int_Byte_Unit ts =
  at_most_one_some_other_true is_TArray is_Int_Byte_Unit ts
                              
fun encode t =
  case t of
      TTuple ts =>
        (case at_most_one_Array_other_Int_Byte_Unit ts of
             inl (p, (w, t, _)) =>
             let
               val () = assert_Int_Byte_Unit t
               val len = length ts
             in
               (* [ptr_to_tuple] *)
               untuple_save (length ts) @
               [ (* [ptr_to_tuple, v_(len-1), ..., v_0] *)
                 Push $ 32*p,
                 Add,
                 MLoad (* [ptr_to_array, vs] *)
               ] @
               encode_array w len p @
               (* [ptr_to_array_len-n, array_len*w+32+n, vs] *)
               concatMapi
                 (fn (i, _) =>
                     let
                       val i = len-1-i
                     in
                       (* [ptr_to_array_len-n, array_len*w+32+n, v_i, v_(i-1)] *)
                       [Swap2] @ (* [v_i, array_len*w+32+n, ptr_to_array_len-n, v_(i-1)] *)
                       (if i = p then
                          [Pop]
                        else
                          [
                            Dup3, (* [ptr_to_array_len-n, v_i, array_len*w+32+n, ptr_to_array_len-n, v_(i-1)] *)
                            Push $ i*32,
                            Add, (* [ptr_to_array_len-n+i*32, v_i, array_len*w+32+n, ptr_to_array_len-n, v_(i-1)] *)
                            MStore (* [array_len*w+32+n, ptr_to_array_len-n, v_(i-1)] *)
                          ]
                       ) @
                       [Swap1] (* [ptr_to_array_len-n, array_len*w+32+n, v_(i-1)] *)
                     end
                 ) ts
                 (* [ptr_to_array_len-n, array_len*w+32+n] *)
             end
           | inr true =>
             [
               Push $ 32 * length ts,
               Swap1
             ]
           | inr false => raise Impossible "Can't encode tuple"
        )
    | TArray (w, t, len) =>
      let
        val () = assert_Int_Byte_Unit t
      in
        encode_array w 1 0
      end
    | _ =>
      if is_Int_Byte_Unit t then
        [
          Push 0,
          MStore,
          Push 32,
          Push 0
        ]
      else
        raise Impossible "Can't encode type"

fun large_exp (b, n) =
  if n <= 0 then LargeInt.fromInt 1
  else LargeInt.* (b, large_exp (b, n-1))
                     
fun rshift n =
  [
    Push_large $ large_exp (LargeInt.fromInt 2, n),
    Swap1,
    DIV ()
  ]
    
fun rshift_byte n = 
  [
    Push_large $ large_exp (LargeInt.fromInt 256, n),
    Swap1,
    DIV ()
  ]
    
fun try_fun (fresh_label, output_heap) (sg, t_arg, t_ret, func) =
  let
    val l_decode = fresh_label ()
    val code_try_sig =
        [
          Push 0,
          CallDataLoad
        ] @
        rshift_byte (32 - 4) @
        [
          Push sg,
          Eq,
          Push_l l_decode,
          Jumpi
        ]
          
    val l_k = fresh_label ()
                          
    val code_k =
      get_reg ARG_REG @
      untuple 2 @
      [Swap1, Pop] @ (* discard closure environment *)
      encode t_ret @
      [Return]
    val () = output_heap ((l_k, "prelude_k"), code_k)
                         
    fun k_closure t =
      [
        Push_l l_k,
        Push 0
      ] @
      make_tuple 2

    fun call_func r =
      (* [reg] *)
      get_reg r @ (* [f_closure] *)
      untuple 2 @ (* [env, l, arg] *)
      [Swap1, Swap2] @ (* [arg, env, l] *)
      make_tuple 2 @
      set_reg ARG_REG @
      [Jump]
      
    val code_decode =
        decode 4 t_arg @
        k_closure t_ret @
        make_tuple 2 @
        call_func func
    val () = output_heap ((l_decode, "prelude_decode"), code_decode)
                  
  in
    code_try_sig
  end

fun prelude (params as (fresh_label, output_heap)) funs =
  let
    fun revert_with error_code =
        [
          Push error_code,
          Push 0,
          MStore,
          Push 32,
          Push 0,
          Revert
        ]
    val l_no_sig_exit = fresh_label ()
    val () = output_heap ((l_no_sig_exit, "prelude_no_fun_sig"), revert_with ErrorCode.NO_FUN_SIG)
  in
    [
      Push 4,
      CallDataSize,
      Lt, (* 1 if size < 4 *)
      Push_l l_no_sig_exit,
      Jumpi
    ] @
    concatMap (try_fun params) funs @
    revert_with ErrorCode.NO_MATCH
  end

val add_prelude_flag = ref false
                           
fun add_prelude_inst params inst =
  case inst of
      Dispatch funs =>
      if !add_prelude_flag then
        prelude params $ map (fn (name, t1, t2, n) => (name, unInner t1, unInner t2, n)) funs
      else
        PUSH_value $ VConst $ WCTT ()
    | _ => [inst]

fun add_prelude_insts params insts =
  let
    val add_prelude_insts = add_prelude_insts params
    val add_prelude_inst = add_prelude_inst params
  in
    case insts of
        ISCons bind =>
        let
          val (inst, I) = unBind bind
        in
          add_prelude_inst inst @@ add_prelude_insts I
        end
      | _ => insts
  end

fun is_block_end inst =
  case inst of
      InstJUMP () => SOME $ JUMP ()
    | InstRETURN () => SOME $ RETURN ()
    | InstREVERT () => SOME $ REVERT ()
    | _ => NONE

fun early_end I =
  case I of
      ISCons bind => 
      let
        val (inst, I) = unBind bind
      in
        case is_block_end inst of
            SOME a => a
          | NONE => [inst] @@ early_end I
      end
    | _ => I

fun list2insts ls =
  let
    exception Done of ('idx, 'ty) insts
    fun f (inst, acc) =
      case is_block_end inst of
          SOME last => raise Done $ rev acc @@ last
        | NONE => inst :: acc
  in
    (foldl f [] ls; raise Impossible "list2insts: didn't find block ender") handle Done I => I
  end
             
fun add_prelude_hval params code =
  let
    val (binds, (spec, I)) = unBind code
    val I = add_prelude_insts params I
  in
    Bind (binds, (spec, early_end I))
  end

fun add_prelude_prog fresh_label (H, I) =
  let
    val r = ref []
    fun output_heap a = push_ref r a
    val params = (fresh_label, output_heap)
    val (H, I) = (map (mapSnd $ add_prelude_hval params) H, add_prelude_insts params I)
    fun insts2hval I = Bind (TeleNil, ((IEmptyState, Rctx.empty, [], TN0 dummy), list2insts I))
    val H' = map (mapSnd insts2hval) $ !r
  in
    (H @ H', I)
  end

end
