structure EVM1Simp = struct

open MicroTiMLSimp
open EVM1Visitor
       
fun simp_evm1_visitor_vtable cast () =
  default_evm1_visitor_vtable
    cast
    extend_noop
    extend_noop
    (ignore_this_env simp_i)
    (ignore_this_env simp_s)
    (ignore_this_env simp_t)
    visit_noop

fun new_simp_evm1_visitor params = new_evm1_visitor simp_evm1_visitor_vtable params
    
fun simp_prog b =
  let
    val visitor as (EVM1Visitor vtable) = new_simp_evm1_visitor ()
  in
    #visit_prog vtable visitor () b
  end

end
