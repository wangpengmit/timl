structure TiTALExportPP = struct

open TiTALVisitor
open ExportPP
       
infixr 0 $
infixr 0 !!

fun params depth_t = (ISDummy ("..."), export_i, export_t depth_t)
fun export_insts (depth_t, depth_insts) a = export_insts_fn (params depth_t) depth_insts a
fun export_hval (depth_t, depth_insts) a = export_hval_fn export_s (params depth_t) depth_insts a
fun export_prog (depth_t, depth_insts, depth_heap) (H, I) =
  let
    val H = case depth_heap of
                SOME n => take n H
              | NONE => H
    val H = map (mapSnd $ export_hval (depth_t, depth_insts)) H
    val I = export_insts (depth_t, depth_insts) ([], []) I
  in
    (H, I)
  end
fun pp_insts_to_string a = TiTALPP.pp_insts_to_string_fn (
    str_i,
    (fn s => pp_t_to s NONE)
  ) a
fun pp_insts a = TiTALPP.pp_insts_fn (
    str_i,
    (fn s => pp_t_to s NONE)
  ) a

end
