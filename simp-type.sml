functor SimpTypeFn (structure Type : TYPE
                    val simp_i : Type.idx -> Type.idx
                    val simp_s : Type.sort -> Type.sort
                    val subst_i_mt : Type.idx -> Type.mtype -> Type.mtype
                   ) = struct

structure Visitor = TypeVisitorFn (structure S = Type
                                   structure T = Type)
open Visitor
       
open Type
open SimpUtil

infixr 0 $
         
fun simp_type_visitor_vtable cast () =
  let
    fun extend_i this env name = (env + 1, name)
  in
    default_type_visitor_vtable
      cast
      extend_noop
      extend_noop
      visit_noop
      visit_noop
      (ignore_this_env simp_i)
      (ignore_this_env simp_s)
      visit_noop
      visit_noop
  end

fun new_simp_type_visitor a = new_type_visitor simp_type_visitor_vtable a
    
fun simp_mt b =
  let
    val visitor as (TypeVisitor vtable) = new_simp_type_visitor ()
  in
    #visit_mtype vtable visitor 0 b
  end
    
fun simp_t b =
  let
    val visitor as (TypeVisitor vtable) = new_simp_type_visitor ()
  in
    #visit_ty vtable visitor 0 b
  end
    
end
