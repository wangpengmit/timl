(* A-Normal-Form (let-normal-form) *)

structure ANF = struct

open MicroTiMLVisitor
open CompilerUtil
open MicroTiMLLocallyNameless
       
infixr 0 $
         
datatype 'expr decl =
         DLet of free_e * string * 'expr
         | DUnpack of (free_t * string) * (free_e * string) * 'expr
         | DUnpackI of (free_i * string) * (free_e * string) * 'expr

fun close_EDecl (d, e2) =
  case d of
      DLet d => ELetClose (d, e2)
    | DUnpack (a, x, e1) => EUnpackClose (e1, a, x, e2)
    | DUnpackI (a, x, e1) => EUnpackIClose (e1, a, x, e2)
      
fun close_EDecls (decls, e) = foldr close_EDecl e decls
                                                                 
fun anf_decls_expr_visitor_vtable cast output =
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
          visit_noop
    fun visit_expr this env e =
      case e of
          EAscSpace (e, i) => EAscSpace (anf e, i)
        | EPackI (t, i, e) => EPackI (t, i, #visit_expr (cast this) this env e)
        | _ =>
          let
            fun is_add_decl e =
              case e of
                  ELet _ => false
                | EUnpack _ => false
                | EUnpackI _ => false
                | ERec _ => false
                | ECase _ => false
                | EIfi _ => false
                | ETriOp (ETIte (), _, _, _) => false
                | EVar _ => false
                | EConst _ => false
                | EMsg _ => false
                | EState _ => false
                | EAscType _ => false
                | EAscTime _ => false
                | EAscSpace _ => false
                | EAscState _ => false
                | EBinOp (EBApp (), _, _) => false
                | EHalt _ => false
                | EUnOp (EUTiML (EUAnno _), _) => false
                | EUnOp _ => true
                | EBinOp _ => true
                | ETriOp _ => true
                | EAbs _ => true
                | EAbsT _ => true
                | EAppT _ => true
                | EAbsI _ => true
                | EAppI _ => true
                | EPack _ => true
                | EPackI _ => true
                | ENever _ => true
                | EBuiltin _ => true
                | ENewArrayValues _ => true
                | ETuple _ => true
                | ELetIdx _ => true
                | ELetType _ => true
                | ELetConstr _ => true
                | EAbsConstr _ => true
                | EAppConstr _ => true
                | EVarConstr _ => true
                | EPackIs _ => true
                | EMatchSum _ => true
                | EMatchPair _ => true
                | EMatchUnfold _ => true
                | EMallocPair _ => true
                | EPairAssign _ => true
                | EProjProtected _ => true
            val add_decl = is_add_decl e
            val e = #visit_expr vtable this env e (* call super *)
          in
            if add_decl then
              let
                val x = fresh_evar ()
                val () = output $ DLet (x, env, e)
              in
                EV x
              end
            else
              e
          end
    val vtable = override_visit_expr vtable visit_expr
    fun visit_ELet this env (data as (e1, bind)) =
      let
        val loop = #visit_expr (cast this) this
        val (name_x, e2) = unBindSimpName bind
        val e1 = loop (fst name_x) e1
        val x = fresh_evar ()
        val e2 = open0_e_e x e2
        val () = output $ DLet (x, fst name_x, e1)
        val e2 = loop env e2
      in
        e2
      end
    fun visit_EUnpack this env (data as (e1, bind)) =
      let
        val loop = #visit_expr (cast this) this
        val (name_a, bind) = unBindSimpName bind
        val (name_x, e2) = unBindSimpName bind
        val e1 = loop (fst name_x) e1
        val a = fresh_tvar ()
        val x = fresh_evar ()
        val e2 = open0_t_e a e2
        val e2 = open0_e_e x e2
        val () = output $ DUnpack ((a, fst name_a), (x, fst name_x), e1)
        val e2 = loop env e2
      in
        e2
      end
    fun visit_EUnpackI this env (data as (e1, bind)) =
      let
        val loop = #visit_expr (cast this) this
        val (name_a, bind) = unBindSimpName bind
        val (name_x, e2) = unBindSimpName bind
        val e1 = loop (fst name_x) e1
        val a = fresh_ivar ()
        val x = fresh_evar ()
        val e2 = open0_i_e a e2
        val e2 = open0_e_e x e2
        val () = output $ DUnpackI ((a, fst name_a), (x, fst name_x), e1)
        val e2 = loop env e2
      in
        e2
      end
    fun visit_ERec this env bind =
      let
        val (t_x, (name_x, e)) = unBindAnnoName bind
        val x = fresh_evar ()
        val e = open0_e_e x e
        val (binds, e) = open_collect_EAbsIT e
        val (st, (t_y, (name_y, e)), i_spec) = assert_EAbs e
        val y = fresh_evar ()
        val e = open0_e_e y e
        val e = anf e
        val e = EAbs (st, close0_e_e_anno ((y, fst name_y, t_y), e), i_spec)
        val e = close_EAbsITs (binds, e)
        val e = ERec $ close0_e_e_anno ((x, fst name_x, t_x), e)
      in
        e
      end
    fun visit_ECase this env (e, bind1, bind2) =
      let
        fun on_bind bind =
          let
            val (name_x, e) = unBindSimpName bind
            val x = fresh_evar ()
            val e = open0_e_e x e
            val e = anf e
            val bind = EBind (name_x, close0_e_e x e)
          in
            bind
          end
        val e = #visit_expr (cast this) this "xc" e
        val bind1 = on_bind bind1         
        val bind2 = on_bind bind2        
      in
        ECase (e, bind1, bind2)
      end
    fun visit_EIfi this env (e, bind1, bind2) =
      let
        fun on_bind bind =
          let
            val (name_x, e) = unBindSimpName bind
            val x = fresh_evar ()
            val e = open0_e_e x e
            val e = anf e
            val bind = EBind (name_x, close0_e_e x e)
          in
            bind
          end
        val e = #visit_expr (cast this) this "xc" e
        val bind1 = on_bind bind1         
        val bind2 = on_bind bind2        
      in
        EIfi (e, bind1, bind2)
      end
    fun visit_ETriOp this env (data as (opr, e, e1, e2)) =
      case opr of
          ETIte () =>
          let
            val e = #visit_expr (cast this) this "xc" e
            val e1 = anf e1         
            val e2 = anf e2        
          in
            ETriOp (ETIte (), e, e1, e2)
          end
        | _ => #visit_ETriOp vtable this env data (* call super *)
    (* this relies on form invariants after CPS *)
    fun visit_EAscTime this env (e, i) =
      let
        val e = anf e
      in
        EAscTime (e, i)
      end
    fun visit_EAppI this env (e, i) =
      let
        val (e, is) = collect_EAppI e
        val e = #visit_expr (cast this) this env e
        val e = EAppIs (e, is)
      in
        EAppI (e, i)
      end
    val vtable = override_visit_ELet vtable visit_ELet
    val vtable = override_visit_EUnpack vtable visit_EUnpack
    val vtable = override_visit_EUnpackI vtable visit_EUnpackI
    val vtable = override_visit_ERec vtable visit_ERec
    val vtable = override_visit_ECase vtable visit_ECase
    val vtable = override_visit_ETriOp vtable visit_ETriOp
    val vtable = override_visit_EIfi vtable visit_EIfi
    val vtable = override_visit_EAscTime vtable visit_EAscTime
    val vtable = override_visit_EAppI vtable visit_EAppI
  in
    vtable
  end

and new_anf_decls_expr_visitor params = new_expr_visitor anf_decls_expr_visitor_vtable params

and anf_decls output b =
  let
    val visitor as (ExprVisitor vtable) = new_anf_decls_expr_visitor output
  in
    #visit_expr vtable visitor "res" b
  end

and anf e =
    let
      val decls = ref []
      fun output d = push_ref decls d
      val e = anf_decls output e
      val decls = !decls
      val decls = rev decls
      val e = close_EDecls (decls, e)
    in
      e
    end

end
