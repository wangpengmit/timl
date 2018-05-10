(* substitute uvar with var *)

structure SubstUVar = struct

open UVar
open Expr
open Util
open Subst
open ExprShift

infixr 0 $

fun visit_TUVar x v env (data as (y, _)) =
  let
    fun TV r n = TVar (ID (n, r))
  in
    if y = x then
      case !y of
          Fresh (_, (sctx, kctx)) => TAbsI_Many (rev sctx, TAbs_Many (rev kctx, TV dummy (v + env + length kctx), dummy), dummy)
        | Refined _ => raise Impossible "substu()/TUVar: shouldn't be Refined"
    else 
      TUVar data
  end

open TypeShiftVisitor
                 
fun new_on_t_type_visitor' visit_TUVar =
  let
    (* don't need to consult type variable's definition *)
    fun visit_var _ x = x
    val (TypeVisitor vtable) = new_on_t_type_visitor visit_var
    val vtable = override_visit_TUVar vtable $ ignore_this visit_TUVar
    val visitor = TypeVisitor vtable
  in
    visitor
  end

fun on_t_mt' params b =
  let
    val visitor as (TypeVisitor vtable) = new_on_t_type_visitor' params
  in
    #visit_mtype vtable visitor 0 b
  end

fun on_t_t' params b =
  let
    val visitor as (TypeVisitor vtable) = new_on_t_type_visitor' params
  in
    #visit_ty vtable visitor 0 b
  end

val params = visit_TUVar
               
fun substu_t_mt x v = on_t_mt' $ params x v
fun substu_t_t x v = on_t_t' $ params x v

fun adapt f x env = f (x + env)

fun substu_t_e x v = ExprShiftVisitor.on_t_e (adapt (substu_t_mt x) v, adapt (substu_t_t x) v)
                             
(* fun substu_ibind f x v (Bind (name, b) : ('a * 'b) ibind) = Bind (name, f x v b) *)
(* fun substu_tbind f x v (Bind (name, b) : ('a * 'b) tbind) = Bind (name, f x (v + 1) b) *)
(* fun substu x v (b : mtype) : mtype = *)
(*   case b of *)
(*       TUVar (y, _) => *)
(*       if y = x then *)
(*         case !y of *)
(*             Fresh (_, (sctx, kctx)) => TAbsIMany (sctx, TAbsMany (kctx, TV dummy (v + length kctx), dummy), dummy) *)
(*           | Refined _ => raise Impossible "substu()/TUVar: shouldn't be Refined" *)
(*       else  *)
(*         b *)
(*     | Unit r => Unit r *)
(*     | Arrow (t1, d, t2) => Arrow (substu x v t1, d, substu x v t2) *)
(*     | TyNat (i, r) => TyNat (i, r) *)
(*     | TyArray (t, i) => TyArray (substu x v t, i) *)
(*     | Prod (t1, t2) => Prod (substu x v t1, substu x v t2) *)
(*     | UniI (s, bind, r) => UniI (s, substu_ibind substu x v bind, r) *)
(*     (* don't need to consult type variable's definition *) *)
(*     | TVar x => TVar x *)
(*     | TAbs (k, bind, r) => TAbs (k, substu_tbind substu x v bind, r) *)
(*     | TApp (t1, t2) => TApp (substu x v t1, substu x v t2) *)
(*     | TAbsI (k, bind, r) => TAbsI (k, substu_ibind substu x v bind, r) *)
(*     | TAppI (t, i) => TAppI (substu x v t, i) *)
(*     | BaseType a => BaseType a *)
(*     | TDatatype _ => raise Unimpl "check_decl()/substu()/TDatatype" *)

end
