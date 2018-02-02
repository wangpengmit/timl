structure MicroTiMLExLocallyNameless = struct

open MicroTiMLEx
       
(***************** the "open_e_e" visitor  **********************)    
    
fun open_e_expr_visitor_vtable cast (open_var, n) : ('this, int, 'var, 'idx, 'sort, 'kind, 'ty, 'var, 'idx, 'sort, 'kind, 'ty) expr_visitor_vtable =
  let
    fun extend_e this env _ = env + 1
    fun visit_var this env data = open_var env n data
  in
    default_expr_visitor_vtable
      cast
      extend_noop
      extend_noop
      extend_noop
      extend_e
      visit_var
      visit_noop
      visit_noop
      visit_noop
      visit_noop
  end

fun new_open_e_expr_visitor params = new_expr_visitor open_e_expr_visitor_vtable params
    
fun open_e_e_fn open_var x n b =
  let
    val visitor as (ExprVisitor vtable) = new_open_e_expr_visitor (open_var, n)
  in
    #visit_expr vtable visitor x b
  end

(* locally nameless variable *)
datatype ('bound, 'free) lnl_var =
         Bound of 'bound
         | Free of 'free
                     
fun open_var x free var = 
  case var of
      Bound y => 
      if y = x then
        Free free
      else
        var
    | Free _ => var

fun close_var x free var = 
  case var of
      Free id => 
      if id = free then
        Bound x
      else
        var
    | Bound _ => var

fun open_e_e a = shift_e_e_fn open_var a
fun open0_e_e a = open_e_e 0 a

fun close_e_e a = shift_e_e_fn close_var a
fun close0_e_e a = close_e_e 0 a

end
