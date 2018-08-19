structure EVMDebugLog = struct

open MicroTiMLUtilTiML
open EVMPrelude
       
infixr 0 $

fun is_TApp_TRec t =
  let
    val (t, args) = collect_TAppIT t
  in
    case t of
        TRec data => SOME (unBindAnnoName data, args)
      | _ => NONE
  end

fun try_unfold t =
  case is_TApp_TRec t of
      SOME ((k, (_, t1)), args) => whnf ([], []) $ TAppITs (subst0_t_t t t1) args
    | NONE => t

fun debug_log t =
  case whnf ([], []) $ snd $ collect_TExistsIT $ try_unfold t of
      TTuplePtr (ts, _, _) =>
      [
        Push $ 32 * length ts,
        Swap1
      ]
    | TArrayPtr (w, _, _, _) =>
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
    | _ =>
      [
        PUSH_reg scratch, MSTORE (), PUSH1nat 32, PUSH_reg scratch
      ]
      (* debug_log $ TTuple [t] *)

(* val add_debug_log_flag = ref false *)
                           
fun add_debug_log_inst () inst =
  case inst of
      DebugLog t =>
      (* if !add_debug_log_flag then *)
        debug_log (unInner t) @
        [Log0, PUSH1 WTT]
      (* else *)
      (*   [PUSH1 WTT] *)
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
