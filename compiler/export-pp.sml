structure ExportPP = struct

open LongId
open Util
open MicroTiMLUtil
open MicroTiMLVisitor
open MicroTiMLLongId
open MicroTiML
       
infixr 0 $
infixr 0 !!
         
fun short_to_long_id x = ID (x, dummy)
fun export_var sel ctx id =
  let
    fun unbound s = "__unbound_" ^ s
    (* fun unbound s = raise Impossible $ "Unbound identifier: " ^ s *)
    fun unbound_free s = s
  in
    case id of
        ID (x, _) =>
        short_to_long_id $ nth_error (sel ctx) x !! (fn () => unbound $ str_int x)
      | QID _ => short_to_long_id $ unbound_free $ CanToString.str_raw_var id
  end
(* val export_i = return2 *)
fun export_i a = ToString.export_i Gctx.empty a
val export_bs = ToString.export_bs
fun export_k k = map_kind export_bs k
fun export_s a = ToString.export_s Gctx.empty a
fun export_t a = export_t_fn (TVar (ID ("...", dummy), []), export_var snd, export_bs, export_i, export_s) a
fun export (depth_t, depth_e) a = export_e_fn (EVar $ ID ("...", dummy), export_var #4, export_var #3, export_k, export_i, export_s, export_t depth_t) depth_e a
val str = PP.string
fun str_var x = LongId.str_raw_long_id id(*str_int*) x
fun str_i a =
  (* ToStringRaw.str_raw_i a *)
  ToString.SN.strn_i a
(* const_fun "<idx>" a *)
fun str_bs a =
  (* ToStringRaw.str_raw_bs a *)
  ToString.SN.strn_bs a
fun str_s a =
  (* ToStringRaw.str_raw_s a *)
  ToString.SN.strn_s a
  (* const_fun "<sort>" a *)
fun pp_t_to s b =
  MicroTiMLPP.pp_t_to_fn (str_var, str_bs, str_i, str_s) s b
(* str s "<ty>" *)
fun pp_t b = MicroTiMLPP.pp_t_fn (str_var, str_bs, str_i, str_s) b
fun pp_t_to_string b = MicroTiMLPP.pp_t_to_string_fn (str_var, str_bs, str_i, str_s) b
fun pp_e_to_string a = MicroTiMLPP.pp_e_to_string_fn (
    str_var,
    str_i,
    str_s,
    str_bs,
    pp_t_to
  ) a
fun pp_e a = MicroTiMLPP.pp_e_fn (
    str_var,
    str_i,
    str_s,
    str_bs,
    pp_t_to
  ) a

(* val uniquefy_i = return2 *)
(* val uniquefy_s = return2 *)
val uniquefy_i = UniquefyIdx.uniquefy_i
val uniquefy_s = UniquefyIdx.uniquefy_s
fun uniquefy_t a = uniquefy_t_fn (uniquefy_i, uniquefy_s) a
fun uniquefy_e a = uniquefy_e_fn (uniquefy_i, uniquefy_s, uniquefy_t) a

end

