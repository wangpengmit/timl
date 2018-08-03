structure EVMPrelude = struct

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
        ] @ rshift_byte (32 - 4)
        @ [
          Push sg,
          Eq,
          Push_l l_decode,
          Jumpi
        ]
    fun decode pos t =
      case t of
          TConst (TCInt ()) => 
          [
            Push pos,
            CallDataLoad
          ]
        | TConst (TCByte ()) => 
          [
            Push pos,
            CallDataLoad
          ]
        | TTuple ts =>
          concatMapi (fn (i, t) => decode (pos + i * 32) t) ts @
          make_tuple (length ts)
        | TArrayPtr (32, t, len, offset) =>
          let
            val () = assert_b "" $ (assert_INat $ simp_i offset) = 32
            val () = TInt_or_TByte t
          in
            [
              Push pos,
              CallDataLoad,
              Push 4,
              Add, (* [ptr_to_input_array_len] *)
              Dup1,
              CallDataLoad, (* [array_len, ptr_to_input_array_len] *)
              Dup1, (* [array_len, array_len, ptr_to_input_array_len] *)
              ArrayMalloc 32 t true, (* [ptr_to_array, array_len, ptr_to_input_array_len] *)
              Dup2,
              ArrayInitLen, (* [ptr_to_array, array_len, ptr_to_input_array_len] *)
              Swap1, (* [array_len, ptr_to_array, ptr_to_input_array_len] *)
              Push 32,
              Mul, (* [array_len*32, ptr_to_array, ptr_to_input_array_len] *)
              Dup2, (* [ptr_to_array, array_len*32, ptr_to_array, ptr_to_input_array_len] *)
              Swap3, (* [ptr_to_input_array_len, array_len*32, ptr_to_array, ptr_to_array] *)
              Push 32,
              Add, (* [ptr_to_input_array, array_len*32, ptr_to_array, ptr_to_array] *)
              Swap1, (* [array_len*32, ptr_to_input_array, ptr_to_array, ptr_to_array] *)
              Swap2, (* [ptr_to_array, ptr_to_input_array, array_len*32, ptr_to_array] *)
              CallDataCopy (* [ptr_to_array] *)
            ]
          end
        | TArrayPtr (1, t, len, offset) =>
          let
            val () = assert_b "" $ (assert_INat $ simp_i offset) = 32
            val () = assert_TByte t
          in
            [
              Push pos,
              CallDataLoad,
              Push 4,
              Add, (* [ptr_to_input_array_len] *)
              Dup1,
              CallDataLoad, (* [array_len, ptr_to_input_array_len] *)
              Dup1, (* [array_len, array_len, ptr_to_input_array_len] *)
              ArrayMalloc 1 t true, (* [ptr_to_array, array_len, ptr_to_input_array_len] *)
              Dup2,
              ArrayInitLen, (* [ptr_to_array, array_len, ptr_to_input_array_len] *)
              Swap1, (* [array_len, ptr_to_array, ptr_to_input_array_len] *)
              Dup2, (* [ptr_to_array, array_len, ptr_to_array, ptr_to_input_array_len] *)
              Swap3, (* [ptr_to_input_array_len, array_len, ptr_to_array, ptr_to_array] *)
              Push 32,
              Add, (* [ptr_to_input_array, array_len, ptr_to_array, ptr_to_array] *)
              Swap1, (* [array_len, ptr_to_input_array, ptr_to_array, ptr_to_array] *)
              Swap2, (* [ptr_to_array, ptr_to_input_array, array_len, ptr_to_array] *)
              CallDataCopy (* [ptr_to_array] *)
            ]
          end
          
    val code_decode =
        decode 4 t_arg @
        k_closure t_ret @
        make_tuple 2 @
        (* [set_reg ARG_REG, Push_l l_fun, Jump] *)
        call_func func
  in

    concatMapi cmp_and sg
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

end
