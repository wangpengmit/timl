structure EVMDebugLog = struct

open EVMPrelude
       
infixr 0 $

fun debug_log t =
  case t of
      TTuple ts =>
      [
        Push $ 32 * length ts,
        Swap1
      ]
    | TArray (w, t, len) =>
      [ (* [ptr_to_array] *)
        Push 32,
        Swap1,
        Sub, (* [ptr_to_array_len] *)
        Dup1, (* [ptr_to_array_len, ptr_to_array_len] *)
        MLoad, (* [array_len, ptr_to_array_len] *)
        Push w,
        Mul,
        Push 32,
        Add, (* [array_len*w+32, ptr_to_array_len] *)
        Swap1 (* [ptr_to_array_len, array_len*w+32] *)
      ]
    | _ => debug_log $ TTuple [t]

val add_debug_log_flag = ref false
                           
fun add_debug_log_inst () inst =
  case inst of
      DebugLog t =>
      if !add_debug_log_flag then
        debug_log (unInner t) @
        [Log0, PUSH1 WTT]
      else
        [PUSH1 WTT]
    | _ => [inst]

infixr 5 @@

fun add_debug_log_insts params insts =
  let
    val add_debug_log_insts = add_debug_log_insts params
    val add_debug_log_inst = add_debug_log_inst params
  in
    case insts of
        ISCons bind =>
        let
          val (inst, I) = unBind bind
        in
          add_debug_log_inst inst @@ add_debug_log_insts I
        end
      | _ => insts
  end

fun add_debug_log_hval params code =
  let
    val (binds, (spec, I)) = unBind code
    val I = add_debug_log_insts params I
  in
    Bind (binds, (spec, early_end I))
  end

fun add_debug_log_prog (H, I) =
  let
    val params = ()
    val (H, I) = (map (mapSnd $ add_debug_log_hval params) H, add_debug_log_insts params I)
  in
    (H, I)
  end

end
