structure EVMPrelude = struct

open Util

infixr 0 $
       
fun is_Int_Byte_Unit t =
  case whnf ([], []) t of
      TConst (TCTiML (TCInt ())) => true
    | TConst (TCTiML (TCByte ())) => true
    | TConst (TCUnit ()) => true
    | _ => false

fun assert_Int_Byte_Unit t = assert_b "assert_Int_Byte_Unit" $ is_Int_Byte_Unit t = true

fun try_fun (sg, t_arg, t_ret, func) =
  let
    val () = assert_b "try_fun: len sg = 4" $ length sg = 4
    fun cmp_and (i, c) =
      [
        
      ]
    val l_decode = fresh_label ()
    val code_cmp_sig =
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
    fun decode pos t =
      case t of
          TTuple ts =>
          concatMapi (fn (i, t) => decode (pos + i * 32) t) ts @
          make_tuple (length ts)
        | TArrayPtr (w, t, len, offset) =>
          let
            val () = assert_b "encode: offset = 32" $ (assert_INat $ simp_i offset) = 32
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
              ArrayMalloc w t true, (* [ptr_to_array, array_len, ptr_to_input_array_len] *)
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
        | _ =>
          if is_Int_Byte_Unit t then
          [
            Push pos,
            CallDataLoad
          ]
          else
            raise Impossible "Can't decode type"

    (* (* both tuple_len and pos_in_tuple are in bytes *)                   *)
    (* fun encode_array32 tuple_len pos_in_tuple = *)
    (*   let *)
    (*     (* the encoded data reuses the array's buffer, appending the tuple before the array *) *)
    (*     val () = assert_b "" $ tuple_len <= 32 * (FIRST_GENERAL_REG + 1) *)
    (*   in *)
    (*       [ *)
    (*         Push 32, *)
    (*         Swap1, *)
    (*         Sub, (* [ptr_to_array_len] *) *)
    (*         Dup1, (* [ptr_to_array_len, ptr_to_array_len] *) *)
    (*         MLoad, (* [array_len, ptr_to_array_len] *) *)
    (*         Swap1, (* [ptr_to_array_len, array_len] *) *)
    (*         Push tuple_len, *)
    (*         Swap1, *)
    (*         Sub, (* [ptr_to_array_len-n, array_len] *) (* there should be at least 32 bytes before ptr_to_array_len, such as the free pointer and scratch space *) *)
    (*         Push tuple_len, *)
    (*         Dup2, (* [ptr_to_array_len-n, n, ptr_to_array_len-n, array_len] *) *)
    (*         Push pos_in_tuple, *)
    (*         Add, (* [ptr_to_array_len-n+p, n, ptr_to_array_len-n, array_len] *) *)
    (*         MStore, (* [ptr_to_array_len-n, array_len] *) *)
    (*         Swap1, (* [array_len, ptr_to_array_len-n] *) *)
    (*         Push 32, *)
    (*         Mul, *)
    (*         Push 32+tuple_len, *)
    (*         Add, (* [array_len*32+32+n, ptr_to_array_len-n] *) *)
    (*         Swap1 (* [ptr_to_array_len-n, array_len*32+32+n] *) *)
    (*       ] *)
    (*   end *)
        
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
          Push 32+n,
          Add, (* [array_len*w+32+n, ptr_to_array_len-n] *)
          Swap1 (* [ptr_to_array_len-n, array_len*w+32+n] *)
        ] @
        (if w <> 32 then
           (* if w <> 32, we write an empty word after the array in order to meet the right-padding requirement *)
           [
             Dup2, (* [array_len*w+32+n, ptr_to_array_len-n, array_len*w+32+n] *)
             Dup2, (* [ptr_to_array_len-n, array_len*w+32+n, ptr_to_array_len-n, array_len*w+32+n] *),
             Add, (* [ptr_to_array_len+array_len*w+32=ptr_to_array_end, ptr_to_array_len-n, array_len*w+32+n] *),
             Push 0,
             Swap1,
             MStore (* [ptr_to_array_len-n, array_len*w+32+n] *),
           ]
         else
           []
        )
      end

    fun untuple_save n =
      (* [ptr_to_tuple] *)
      int_concatMap (fn i => [Dup1, Push i*32, Add, MLoad, Swap1]) n @
    (* [ptr_to_tuple, v_(n-1), ..., v_0] *)
    fun untuple n = untuple_save n @ [Pop]

    fun make_tuple n =
      (* [v_(n-1), ..., v_0] *)
      [TupleMalloc (repeat n $ TUint)] @
      int_concatMap_rev
        (fn i => [
           (* [ptr, v_i, v_(i-1)] *)
           Swap1, (* [v_i, ptr, v_(i-1)] *)
           Dup2, (* [ptr, v_i, ptr, v_(i-1)] *)
           Push i*32,
           Add, (* [ptr+32*i, v_i, ptr, v_(i-1)] *)
           MStore, (* [ptr, v_(i-1)] *)
        ]) n
    (* [ptr] *)
      
    fun encode t =
      case t of
          TTuple ts =>
          if List.all is_Int_Byte_Unit ts then
            [
              Push 32 * length ts,
              Swap1
            ]
          else
            (case one_Array_other_Int_Byte_Unit ts of
                 SOME (p, (w, t, _, offset)) =>
                 let
                   val () = assert_b "encode: offset = 32" $ (assert_INat $ simp_i offset) = 32
                   val () = assert_Int_Byte_Unit t
                   val len = length ts
                 in
                   (* [ptr_to_tuple] *)
                   untuple_save (length ts) @
                   [ (* [ptr_to_tuple, v_(len-1), ..., v_0] *)
                     Push 32*p,
                     Add,
                     MLoad, (* [ptr_to_array, vs] *)
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
                              Push i*32,
                              Add, (* [ptr_to_array_len-n+i*32, v_i, array_len*w+32+n, ptr_to_array_len-n, v_(i-1)] *)
                              MStore, (* [array_len*w+32+n, ptr_to_array_len-n, v_(i-1)] *)
                            ]
                         ) @
                         [Swap1] (* [ptr_to_array_len-n, array_len*w+32+n, v_(i-1)] *)
                     ) ts
                   (* [ptr_to_array_len-n, array_len*w+32+n] *)
                 end
               | NONE => raise Impossible "Can't encode tuple"
            )
        | TArrayPtr (w, t, len, offset) =>
          let
            val () = assert_b "" $ (assert_INat $ simp_i offset) = 32
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

    fun code_k t =
      get_reg ARG_REG @
      untuple 2 @
      [Swap1, Pop] @ (* discard closure environment *)
      encode t @
      [Return]

    val l_k = fresh_label ()
                          
    fun k_closure t =
      [
        Push_l l_k,
        Push 0,
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
  in

    concatMapi cmp_and sg
  end

fun get_func_sig (name, t) =
  let
    fun str_t t =
      case t of
          TConst (TCTiML (TCInt ())) => "int256"
        | TConst (TCTiML (TCByte ())) => "uint8"
        | TConst (TCUnit ()) => "uint8"
                              | TTuple 
  in
  end
    
fun prelude funs =
    [
      Push 4,
      CallDataSize,
      Lt, (* 1 if size < 4 *)
      Push_l l_no_sig_exit,
      Jumpi
    ]
    @ concatMap try_fun funs
    @ no_match

fun add_prelude_inst (params as (PUSH_reg, PUSH_tuple_offset, scratch, reg_addr, TUnit)) (inst : ('a, 'b) inst) =
  let
    val add_prelude_inst = add_prelude_inst params
  in
    case inst of
        Dispatch funs =>
        if !add_prelude_flag then
          prelude funs
        else
          PUSH_value $ VConst WCUnit
      | _ => [inst]
  end

fun add_prelude_insts (params as (add_prelude_inst, PUSH_reg, scratch)) insts =
  let
    val add_prelude_insts = add_prelude_insts params
  in
    case insts of
        ISCons bind =>
        let
          val (inst, I) = unBind bind
        in
          add_prelude_inst inst @@ add_prelude_insts I
        end
      | MACRO_halt t => [PUSH_reg scratch, SWAP1, DUP2, MSTORE (), PUSH1nat 32, SWAP1] @@ RETURN ()(* t *)
      | _ => insts
  end
                                                                     
fun add_prelude_hval code =
  let
    val (binds, (spec, I)) = unBind code
    val I = add_prelude_insts I
  in
    Bind (binds, (spec, I))
  end

fun add_prelude_prog (H, I) =
  (map (mapSnd add_prelude_hval) H, add_prelude_insts I)

end
