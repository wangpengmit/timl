functor UniquefyIdxFn (
  structure Idx : IDX where type name = string * Region.region
  val map_uvar_bs : ('basic_sort -> 'basic_sort2) -> 'basic_sort Idx.uvar_bs -> 'basic_sort2 Idx.uvar_bs
  val map_uvar_i : ('basic_sort -> 'basic_sort2) * ('idx -> 'idx2) -> ('basic_sort, 'idx) Idx.uvar_i -> ('basic_sort2, 'idx2) Idx.uvar_i
  val map_uvar_s : ('basic_sort -> 'basic_sort2) * ('sort -> 'sort2) -> ('basic_sort, 'sort) Idx.uvar_s -> ('basic_sort2, 'sort2) Idx.uvar_s
) = struct

open Gctx
open List
open Util
open VisitorUtil
open Operators
       
structure IdxVisitor = IdxVisitorFn (struct
                                      structure S = Idx
                                      structure T = Idx
                                      end)
(* open IdxVisitor *)
structure IV = IdxVisitor
                           
(********* the "uniquefy" visitor: makes variable names unique to remove shadowing *********)
fun uniquefy_idx_visitor_vtable cast () =
  let
    fun extend this names name =
      let
        val (name, r) = name
        val name = find_unique names name
        val names = name :: names
        val name = (name, r)
      in
        (names, name)
      end
    fun visit_uvar_bs this ctx u =
      let
        val vtable = cast this
      in
        map_uvar_bs (#visit_basic_sort vtable this []) u
      end
    fun visit_uvar_i this ctx (u, r) =
      let
        val vtable = cast this
        val u = map_uvar_i (#visit_basic_sort vtable this [], #visit_idx vtable this []) u
      in
        (u, r)
      end
    fun visit_uvar_s this ctx (u, r) =
      let
        val vtable = cast this
        val u = map_uvar_s (#visit_basic_sort vtable this [], #visit_sort vtable this []) u
      in
        (u, r)
      end
  in
    IV.default_idx_visitor_vtable
      cast
      extend
      visit_noop
      (* visit_noop *)
      (* visit_noop *)
      (* visit_noop *)
      visit_uvar_bs
      visit_uvar_i
      visit_uvar_s
      visit_noop
  end

fun new_uniquefy_idx_visitor a = IV.new_idx_visitor uniquefy_idx_visitor_vtable a
    
fun uniquefy_i ctx b =
  let
    val visitor as (IV.IdxVisitor vtable) = new_uniquefy_idx_visitor ()
  in
    #visit_idx vtable visitor ctx b
  end

fun uniquefy_p ctx b =
  let
    val visitor as (IV.IdxVisitor vtable) = new_uniquefy_idx_visitor ()
  in
    #visit_prop vtable visitor ctx b
  end

fun uniquefy_s ctx b =
  let
    val visitor as (IV.IdxVisitor vtable) = new_uniquefy_idx_visitor ()
  in
    #visit_sort vtable visitor ctx b
  end
    
end
