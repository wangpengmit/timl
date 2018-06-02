structure MicroTiMLSimp = struct

open Simp
open MicroTiMLVisitor
       
fun simp_ty_visitor_vtable cast () =
    default_ty_visitor_vtable
      cast
      extend_noop
      extend_noop
      visit_noop
      visit_noop
      (ignore_this_env simp_i)
      (ignore_this_env simp_s)

fun new_simp_ty_visitor a = new_ty_visitor simp_ty_visitor_vtable a
    
fun simp_t b =
  let
    val visitor as (TyVisitor vtable) = new_simp_ty_visitor ()
  in
    #visit_ty vtable visitor () b
  end
    
fun simp_expr_visitor_vtable cast () =
    default_expr_visitor_vtable
      cast
      extend_noop
      extend_noop
      extend_noop
      extend_noop
      visit_noop
      visit_noop
      (ignore_this_env simp_i)
      (ignore_this_env simp_s)
      (ignore_this_env simp_t)

fun new_simp_expr_visitor params = new_expr_visitor simp_expr_visitor_vtable params
    
fun simp_e b =
  let
    val visitor as (ExprVisitor vtable) = new_simp_expr_visitor ()
  in
    #visit_expr vtable visitor () b
  end
    
end
