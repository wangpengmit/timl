structure PatternVisitor = struct

open Pattern
       
infixr 0 $
       
type ('this, 'env, 'cvar, 'mtype, 'cvar2, 'mtype2) ptrn_visitor_vtable =
     {
       visit_ptrn : 'this -> 'env ctx -> ('cvar, 'mtype) ptrn -> ('cvar2, 'mtype2) ptrn,
       visit_PnVar : 'this -> 'env ctx -> ename binder -> ('cvar2, 'mtype2) ptrn,
       visit_PnTT : 'this -> 'env ctx -> region -> ('cvar2, 'mtype2) ptrn,
       (* visit_PnPair : 'this -> 'env ctx -> ('cvar, 'mtype) ptrn * ('cvar, 'mtype) ptrn -> ('cvar2, 'mtype2) ptrn, *)
       visit_PnAlias : 'this -> 'env ctx -> ename binder * ('cvar, 'mtype) ptrn * region -> ('cvar2, 'mtype2) ptrn,
       visit_PnConstr : 'this -> 'env ctx -> ('cvar * bool) outer * iname binder list * ('cvar, 'mtype) ptrn * region -> ('cvar2, 'mtype2) ptrn,
       visit_PnAnno : 'this -> 'env ctx -> ('cvar, 'mtype) ptrn * 'mtype outer -> ('cvar2, 'mtype2) ptrn,
       visit_cvar : 'this -> 'env -> 'cvar -> 'cvar2,
       visit_mtype : 'this -> 'env -> 'mtype -> 'mtype2,
       extend_i : 'this -> 'env -> iname -> 'env * iname,
       extend_e : 'this -> 'env -> ename -> 'env * ename
     }
       
type ('this, 'env, 'cvar, 'mtype, 'cvar2, 'mtype2) ptrn_visitor_interface =
     ('this, 'env, 'cvar, 'mtype, 'cvar2, 'mtype2) ptrn_visitor_vtable
                                       
(***************** the default visitor  **********************)    

open VisitorUtil
       
fun default_ptrn_visitor_vtable
      (cast : 'this -> ('this, 'env, 'cvar, 'mtype, 'cvar2, 'mtype2) ptrn_visitor_interface)
      extend_i
      extend_e
      visit_cvar
      visit_mtype
    : ('this, 'env, 'cvar, 'mtype, 'cvar2, 'mtype2) ptrn_visitor_vtable =
  let
    fun visit_ibinder this env name =
      let
        val vtable = cast this
        val name = visit_binder (#extend_i vtable this) env name
      in
        name
      end
    fun visit_ebinder this env name =
      let
        val vtable = cast this
        val name = visit_binder (#extend_e vtable this) env name
      in
        name
      end
    fun visit_ptrn this env data =
      let
        val vtable = cast this
      in
        case data of
            PnVar data => #visit_PnVar vtable this env data
          | PnTT data => #visit_PnTT vtable this env data
          (* | PnPair data => #visit_PnPair vtable this env data *)
          | PnAlias data => #visit_PnAlias vtable this env data
          | PnConstr data => #visit_PnConstr vtable this env data
          | PnAnno data => #visit_PnAnno vtable this env data
      end
    fun visit_PnVar this env data =
      let
        val vtable = cast this
      in
        PnVar $ visit_ebinder this env data
      end
    fun visit_PnTT this env data =
      PnTT data
    (* fun visit_PnPair this env data =  *)
    (*   let *)
    (*     val vtable = cast this *)
    (*     val (p1, p2) = data *)
    (*     val p1 = #visit_ptrn vtable this env p1 *)
    (*     val p2 = #visit_ptrn vtable this env p2 *)
    (*   in *)
    (*     PnPair (p1, p2) *)
    (*   end *)
    fun visit_PnAlias this env data =
      let
        val vtable = cast this
        val (name, p, r) = data
        val name = visit_ebinder this env name
        val p = #visit_ptrn vtable this env p
      in
        PnAlias (name, p, r)
      end
    fun visit_PnAnno this env data = 
      let
        val vtable = cast this
        val (p, t) = data
        val p = #visit_ptrn vtable this env p
        val t = visit_outer (#visit_mtype vtable this) env t
      in
        PnAnno (p, t)
      end
    fun visit_PnConstr this env data =
      let
        val vtable = cast this
        val (x, inames, p, r) = data
        val x = visit_outer (visit_pair (#visit_cvar vtable this) return2) env x
        val inames = map (visit_ibinder this env) inames
        val p = #visit_ptrn vtable this env p
      in
        PnConstr (x, inames, p, r)
      end
  in
    {
      visit_ptrn = visit_ptrn,
      visit_PnVar = visit_PnVar,
      visit_PnTT = visit_PnTT,
      (* visit_PnPair = visit_PnPair, *)
      visit_PnAlias = visit_PnAlias,
      visit_PnAnno = visit_PnAnno,
      visit_PnConstr = visit_PnConstr,
      visit_cvar = visit_cvar,
      visit_mtype = visit_mtype,
      extend_i = extend_i,
      extend_e = extend_e
    }
  end

datatype ('env, 'cvar, 'mtype, 'cvar2, 'mtype2) ptrn_visitor =
         PtrnVisitor of (('env, 'cvar, 'mtype, 'cvar2, 'mtype2) ptrn_visitor, 'env, 'cvar, 'mtype, 'cvar2, 'mtype2) ptrn_visitor_interface

fun ptrn_visitor_impls_interface (this : ('env, 'cvar, 'mtype, 'cvar2, 'mtype2) ptrn_visitor) :
    (('env, 'cvar, 'mtype, 'cvar2, 'mtype2) ptrn_visitor, 'env, 'cvar, 'mtype, 'cvar2, 'mtype2) ptrn_visitor_interface =
  let
    val PtrnVisitor vtable = this
  in
    vtable
  end

fun new_ptrn_visitor vtable params =
  let
    val vtable = vtable ptrn_visitor_impls_interface params
  in
    PtrnVisitor vtable
  end
    
(***************** the "subst_t_pn" visitor  **********************)    

fun subst_t_ptrn_visitor_vtable cast (subst_t_t, d, x, v) : ('this, idepth * tdepth, 'mtype, 'expr, 'mtype, 'expr2) ptrn_visitor_vtable =
  let
    fun extend_i this env name = (mapFst idepth_inc env, name)
    fun add_depth (di, dt) (di', dt') = (idepth_add (di, di'), tdepth_add (dt, dt'))
    fun visit_mtype this env b = subst_t_t (add_depth d env) (x + unTDepth (snd env)) v b
  in
    default_ptrn_visitor_vtable
      cast
      extend_i
      extend_noop
      visit_noop
      visit_mtype
  end

fun new_subst_t_ptrn_visitor params = new_ptrn_visitor subst_t_ptrn_visitor_vtable params
    
fun visit_subst_t_pn_fn substs env d x v b =
  let
    val visitor as (PtrnVisitor vtable) = new_subst_t_ptrn_visitor (substs, d, x, v)
  in
    #visit_ptrn vtable visitor env b
  end

fun subst_t_pn_fn substs = visit_subst_t_pn_fn substs (env2ctx (IDepth 0, TDepth 0))
fun substx_t_pn_fn substs = subst_t_pn_fn substs (IDepth 0, TDepth 0) 
fun subst0_t_pn_fn substs = substx_t_pn_fn substs 0

(***************** the "count_binder" visitor  **********************)    
    
fun count_binder_ptrn_visitor_vtable cast () =
  let
    fun extend_i this (ni, ne) name = ((ni + 1, ne), name)
    fun extend_e this (ni, ne) name = ((ni, ne + 1), name)
  in
    default_ptrn_visitor_vtable
      cast
      extend_i
      extend_e
      visit_noop
      visit_noop
  end

fun new_count_binder_ptrn_visitor params = new_ptrn_visitor count_binder_ptrn_visitor_vtable params
    
fun count_binder_pn b =
  let
    val visitor as (PtrnVisitor vtable) = new_count_binder_ptrn_visitor ()
    val ctx = env2ctx (0, 0)
    val _ = #visit_ptrn vtable visitor ctx b
  in
    !(#current ctx)
  end
    
(***************** the "collect_binder" visitor  **********************)    
    
fun collect_binder_ptrn_visitor_vtable cast () =
  let
    fun extend_i this (ni, ne) name = ((Name2str name :: ni, ne), name)
    fun extend_e this (ni, ne) name = ((ni, Name2str name :: ne), name)
  in
    default_ptrn_visitor_vtable
      cast
      extend_i
      extend_e
      visit_noop
      visit_noop
  end

fun new_collect_binder_ptrn_visitor params = new_ptrn_visitor collect_binder_ptrn_visitor_vtable params
    
fun collect_binder_pn b =
  let
    val visitor as (PtrnVisitor vtable) = new_collect_binder_ptrn_visitor ()
    val ctx = env2ctx ([], [])
    val _ = #visit_ptrn vtable visitor ctx b
  in
    !(#current ctx)
  end
    
end
