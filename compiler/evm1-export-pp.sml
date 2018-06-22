structure EVM1ExportPP = struct

open EVM1Visitor
open ExportPP
       
infixr 0 $
infixr 0 !!

fun params depth_t = (ISDummy ("..."), export_k, export_i, export_s, export_t depth_t)
fun export_inst depth_t a = export_inst_fn (params depth_t) a
fun export_insts (depth_t, depth_insts) a = export_insts_fn (params depth_t) depth_insts a
fun export_hval (depth_t, depth_insts) a = export_hval_fn (params depth_t) depth_insts a
fun export_prog (depth_t, depth_insts, depth_heap) a = export_prog_fn (params depth_t) depth_insts depth_heap a
fun pp_t_to_NONE s = pp_t_to s NONE
                             
fun pp_inst_to_string a = EVM1PP.pp_inst_to_string_fn (
    str_i,
    pp_t_to_NONE
  ) a
fun pp_inst a = EVM1PP.pp_inst_fn (
    str_i,
    pp_t_to_NONE
  ) a

fun pp_insts_to_string a = EVM1PP.pp_insts_to_string_fn (
    str_i,
    pp_t_to_NONE
  ) a
fun pp_insts a = EVM1PP.pp_insts_fn (
    str_i,
    pp_t_to_NONE
  ) a

fun pp_prog_to_string a = EVM1PP.pp_prog_to_string_fn (
    str_i,
    str_s,
    str_bs,
    pp_t_to_NONE
  ) a
fun pp_prog a = EVM1PP.pp_prog_fn (
    str_i,
    str_s,
    str_bs,
    pp_t_to_NONE
  ) a

end
