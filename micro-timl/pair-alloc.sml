(* Explicit pair allocation and assignments *)

structure PairAlloc = struct

fun pa_ty_visitor_vtable cast () =
  let
    val vtable =
        default_ty_visitor_vtable
          cast
          extend_noop
          extend_noop
          visit_noop
          visit_noop
          visit_noop
          visit_noop
    fun visit_TBinOp this env (data as (opr, t1, t2)) =
      case opr of
          TBinOp =>
          let
            val pa_t = #visit_ty (cast this) this env
            val t1 = pa_t t1
            val t2 = pa_t t2
          in
            TProdEx ((t1, true), (t2, true))
          end
        | _ => #visit_TBinOp vtable this env data (* call super *)
    val vtable = override_visit_TBinOp vtable visit_TBinOp
  in
    vtable
  end

fun new_pa_ty_visitor a = new_ty_visitor pa_ty_visitor_vtable a
    
fun pa_t t =
  let
    val visitor as (TyVisitor vtable) = new_pa_ty_visitor ()
  in
    #visit_ty vtable visitor () t
  end
    
fun pa_expr_visitor_vtable cast () =
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
    fun visit_EUnOp this env (data as (opr, e)) =
      case opr of
          EUProj proj => EProjProtected (proj, #visit_expr (cast this) this env e)
        | _ => #visit_EUnOp vtable this env data (* call super *)
    fun visit_EBinOp this env (data as (opr, e1, e2)) =
      case opr of
        | EBPair =>
          let
            val pa = #visit_expr (cast this) this env
            val (e1, t_e1) = assert_EAscType e1
            val (e2, t_e2) = assert_EAscType e2
            val e1 = pa e1
            val e2 = pa e2
            val t_e1 = pa_t t_e1
            val t_e2 = pa_t t_e2
            val x1 = fresh_evar ()
            val x2 = fresh_evar ()
            val y0 = fresh_evar ()
            val y1 = fresh_evar ()
            val y2 = fresh_evar ()
            val e = ELetManyClose (
                  [(x1, "x1", e1),
                   (x2, "x2", e2),
                   (y0, "y0", EMallocPair (t_e1, t_e2)),
                   (y1, "y1", EPairAssign (EV y0, ProjFst, EV x1)),
                   (y2, "y2", EPairAssign (EV y1, ProjSnd, EV x2)),
                  ], EV y2)                  
          in
            e
          end
        | _ => #visit_EBinOp vtable this env data (* call super *)
    val vtable = override_visit_EUnOp vtable visit_EUnOp
    val vtable = override_visit_EBinOp vtable visit_EBinOp
  in
    vtable
  end

fun new_pa_expr_visitor params = new_expr_visitor pa_expr_visitor_vtable params

fun pa b =
  let
    val visitor as (ExprVisitor vtable) = new_pa_expr_visitor ()
  in
    #visit_expr vtable visitor () b
  end

datatype 'expr decl =
         DLet of free_e * string * 'expr
         | DUnpack of (free_t * string) * (free_e * string) * 'expr
         | DUnpackI of (free_i * string) * (free_e * string) * 'expr
                                                                 
fun anf_decls output e =
  let
    val loop = anf_d output
  in
  case e of
      EBinOp (opr, e1, e2) =>
      let
        val e1 = loop e1
        val e2 = loop e2
        val x = fresh_evar ()
        val () = output $ DLet (x, "x", EBinOp (opr, e1, e2))
      in
        EV x
      end
    | EUnOp (opr, e) =>
      let
        val e = loop e
        val x = fresh_evar ()
        val () = output $ DLet (x, "x", EUnOp (opr, e))
      in
        EV x
      end
    | EWrite (e1, e2, e3) =>
      let
        val e1 = loop e1
        val e2 = loop e2
        val e3 = loop e3
        val x = fresh_evar ()
        val () = output $ DLet (x, "x", EWrite (e1, e2, e3))
      in
        EV x
      end
    | ELet (e1, bind) =>
      let
        val e1 = loop e1
        val (name_x, e2) = unBindSimpName bind
        val x = fresh_evar ()
        val e2 = open0_e_e x e2
        val () = output $ DLet (x, fst name_x, e1)
        val e2 = loop e2
      in
        e2
      end
    | EUnpack (e1, bind) =>
      let
        val e1 = loop e1
        val (name_a, bind) = unBindSimpName bind
        val (name_x, e2) = unBindSimpName bind
        val a = fresh_tvar ()
        val x = fresh_evar ()
        val e2 = open0_t_e a e2
        val e2 = open0_e_e x e2
        val () = output $ DUnpack ((a, fst name_a), (x, fst name_x), e1)
        val e2 = loop e2
      in
        e2
      end
    | EUnpackI (e1, bind) =>
      let
        val e1 = loop e1
        val (name_a, bind) = unBindSimpName bind
        val (name_x, e2) = unBindSimpName bind
        val a = fresh_ivar ()
        val x = fresh_evar ()
        val e2 = open0_i_e a e2
        val e2 = open0_e_e x e2
        val () = output $ DUnpackI ((a, fst name_a), (x, fst name_x), e1)
        val e2 = loop e2
      in
        e2
      end
    | ERec bind =>
      let
        val (t_x, (name_x, e)) = unBindAnnoName bind
        val x = fresh_evar ()
        val e = open0_e_e x e
        val (binds, e) = open_collect_EAbsIT e
        val (t_y, (name_y, e)) = assert_EAbs e
        val y = fresh_evar ()
        val e = open0_e_e y e
        val e = anf e
        val e = EAbs $ close0_e_e_anno ((y, fst name_y, t_y), e)
        val e = close_EAbsITs (binds, e)
        val e = ERec $ close0_e_e_anno ((x, fst name_x, t_x), e)
      in
        e
      end
    | EConst _ => e
    | EVar _ => e
  end

and anf e =
    let
      val decls = ref []
      fun output d = push_ref decls d
      val e = anf_decls output e
      val decls = !decls
      val e = EDecls (decls, e)
    in
      e
    end
      

(* fun flat e = () *)

(* fun check_anf e = () *)

      (* already implemented by post_process() *)
(* fun remove_noop_ELet_expr_visitor_vtable cast () = *)
(*   let *)
(*     val vtable =  *)
(*         default_expr_visitor_vtable *)
(*           cast *)
(*           extend_noop *)
(*           extend_noop *)
(*           extend_noop *)
(*           extend_noop *)
(*           visit_noop *)
(*           visit_noop *)
(*           visit_noop *)
(*           visit_noop *)
(*           visit_noop *)
(*     fun visit_ELet this env (data as (e1, bind)) = *)
(*       let *)
(*         val this_vtable = cast this *)
(*         val e1 = #visit_expr this_vtable this env e1 *)
(*       in *)
(*             case e1 of *)
(*                 EVar _ => #visit_expr this_vtable this env $ subst0_e_e e1 e2 *)
(*               | _ => *)
(*                 let *)
(*                   val (name, e2) = unBindSimpName bind *)
(*                   val e2 = #visit_expr this_vtable this env e2 *)
(*                 in *)
(*                   ELet (e1, EBind (name, e2)) *)
(*                 end *)
(*       end *)
(*     val vtable = override_visit_ELet vtable visit_ELet *)
(*   in *)
(*     vtable *)
(*   end *)

(* fun new_remove_noop_ELet_expr_visitor params = new_expr_visitor remove_noop_ELet_expr_visitor_vtable params *)

(* fun remove_noop_ELet b = *)
(*   let *)
(*     val visitor as (ExprVisitor vtable) = new_remove_noop_ELet_expr_visitor () *)
(*   in *)
(*     #visit_expr vtable visitor () b *)
(*   end *)

end
