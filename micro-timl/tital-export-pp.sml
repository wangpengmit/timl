structure TiTALExportPP = struct

open TiTALVisitor
open ExportPP
       
infixr 0 $
infixr 0 !!

fun params depth_t = (ISDummy ("..."), export_i, export_t depth_t)
fun export_insts (depth_t, depth_e) a = export_insts_fn (params depth_t) depth_e a
fun export_hval (depth_t, depth_e) a = export_hval_fn export_s (params depth_t) depth_e a
fun export_prog (depth_t, depth_e, depth_h) (H, I) =
  let
    val H = case depth_h of
                SOME n => take n H
              | NONE => H
    val H = map (mapSnd $ export_hval (depth_t, depth_e)) H
    val I = export_insts (depth_t, depth_e) ([], []) I
  in
    (H, I)
  end

end
