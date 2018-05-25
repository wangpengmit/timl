structure EvalConstr = struct

open Util
open MicroTiMLLongId
       
infixr 0 $

fun eval_constr_expr_visitor_vtable cast () =
  let
    val vtable = 
        default_expr_visitor_vtable
          cast
          extend_noop
          extend_noop
          extend_noop
          extend_noop
          visit_noop
          visit_noop
          visit_noop
          visit_noop
          visit_noop
    fun visit_EAppConstr this env (e1, ts, is, e2) =
      let
        val vtable = cast this
        val e1 = #visit_expr vtable this env e1
        val ts = map (#visit_ty vtable this env) ts
        val is = map (#visit_idx vtable this env) is
        val e2 = #visit_expr vtable this env e2
      in
        case e1 of
            EAbsConstr data =>
            let
              val ((tnames, inames, ename), e) = unBind data
              val di = length is
              val e = fst $ foldl (fn (v, (b, dt)) => (subst_t_e (IDepth di, TDepth dt) dt v b, dt - 1)) (e, length ts - 1) ts
              val e = fst $ foldl (fn (v, (b, di)) => (subst_i_e di di v b, di - 1)) (e, di - 1) is
              val e = subst0_e_e e2 e
            in
              #visit_expr vtable this env e
            end
          | _ => EAppConstr (e1, ts, is, e2)
      end
    val vtable = override_visit_EAppConstr vtable visit_EAppConstr
  in
    vtable
  end

fun new_eval_constr_expr_visitor params = new_expr_visitor eval_constr_expr_visitor_vtable params
    
fun eval_constr b =
  let
    val visitor as (ExprVisitor vtable) = new_eval_constr_expr_visitor ()
  in
    #visit_expr vtable visitor () b
  end

end
