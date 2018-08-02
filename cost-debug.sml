structure CostDebug = struct

val debug_cost_flag = ref false
fun is_debug_cost () = !debug_cost_flag

end
