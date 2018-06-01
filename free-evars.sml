structure StringIntOrdKey = PairOrdKeyFn (structure Fst = StringOrdKey
                                          structure Snd = IntOrdKey)
structure EVarOrdKey = SumOrdKeyFn (structure L = IntOrdKey
                                  structure R = StringIntOrdKey)
structure EVarSet = BinarySetFn (EVarOrdKey)
structure EVarSetU = SetUtilFn (EVarSet)

structure FreeEVars = struct

structure Visitor = ExprVisitorFn (structure S = Expr
                                   structure T = Expr)
open Visitor
open VisitorUtil
open Util
open LongId

infixr 0 $
                             
fun free_evars_expr_visitor_vtable cast output =
  let
    fun extend_e this env name = (env + 1, name)
    fun visit_var this env data =
      ((case data of
            ID (n, _) => if n >= env then output $ inl $ n - env
                         else ()
          | QID ((m, _), (n, _)) => output $ inr (m, n)
       );
       data)
    val vtable = 
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
          visit_noop
          visit_noop
          visit_noop
          visit_noop
    fun visit_DOpen this env (data as (m, scp)) =
      let
        val r = #visit_DOpen vtable this env data (*call super*)
        val (m, _) = unInner m
        (* 'open' touches all evars in the module, so all of them should be counted as free evars *)
        val () = Option.app (appi (fn (i, _) => output $ inr (m, i)) o #4) scp
      in
        r
      end
    val vtable = override_visit_DOpen vtable visit_DOpen
  in
    vtable
  end
fun new_free_evars_expr_visitor params = new_expr_visitor free_evars_expr_visitor_vtable params
fun free_evars b =
  let
    val r = ref []
    fun output n = push_ref r n
    val visitor as (ExprVisitor vtable) = new_free_evars_expr_visitor output
    val _ = #visit_expr vtable visitor 0 b
    val fvars = !r
  in
    EVarSetU.to_set fvars
  end

end
