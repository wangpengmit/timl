signature TYPE_VISITOR_PARAMS = sig
  structure S : TYPE
  structure T : TYPE
  sharing type S.base_type = T.base_type
  sharing type S.name = T.name
  sharing type S.region = T.region
end

functor TypeVisitorFn (Params : TYPE_VISITOR_PARAMS) = struct

open Params
open Unbound
open Namespaces
open Binders
open Operators
open Region
open S

infixr 0 $
       
type ('this, 'env) type_visitor_vtable =
     {
       visit_mtype : 'this -> 'env -> mtype -> T.mtype,
       visit_TArrow : 'this -> 'env -> (idx StMap.map * mtype) * (idx * idx) * (idx StMap.map * mtype) -> T.mtype,
       visit_TNat : 'this -> 'env -> idx * region -> T.mtype,
       visit_TArray : 'this -> 'env -> mtype * idx -> T.mtype,
       visit_TBase : 'this -> 'env -> base_type * region -> T.mtype,
       visit_TUnit : 'this -> 'env -> region -> T.mtype,
       visit_TProd : 'this -> 'env -> mtype * mtype -> T.mtype,
       visit_TUniI : 'this -> 'env -> sort * (name * mtype) Bind.ibind * region -> T.mtype,
       visit_TVar : 'this -> 'env -> var -> T.mtype,
       visit_TAbs : 'this -> 'env -> kind * (name * mtype) Bind.tbind * region -> T.mtype,
       visit_TApp : 'this -> 'env -> mtype * mtype -> T.mtype,
       visit_TAbsI : 'this -> 'env -> basic_sort * (name * mtype) Bind.ibind  * region -> T.mtype,
       visit_TAppI : 'this -> 'env -> mtype * idx -> T.mtype,
       visit_TUVar : 'this -> 'env -> (basic_sort, kind, mtype) uvar_mt * region -> T.mtype,
       visit_TDatatype : 'this -> 'env -> mtype datatype_def * region -> T.mtype,
       visit_TSumbool : 'this -> 'env -> sort * sort -> T.mtype,
       visit_ty : 'this -> 'env -> ty -> T.ty,
       visit_PTMono : 'this -> 'env -> mtype -> T.ty,
       visit_PTUni : 'this -> 'env -> (name * ty) Bind.tbind * region -> T.ty,
       visit_datatype : 'this -> 'env -> mtype datatype_def -> T.mtype T.datatype_def,
       visit_constr_core : 'this -> 'env -> mtype constr_core -> T.mtype T.constr_core,
       visit_constr_info : 'this -> 'env -> mtype constr_info -> T.mtype T.constr_info,
       visit_var : 'this -> 'env -> var -> T.var,
       visit_basic_sort : 'this -> 'env -> basic_sort -> T.basic_sort,
       visit_idx : 'this -> 'env -> idx -> T.idx,
       visit_sort : 'this -> 'env -> sort -> T.sort,
       visit_kind : 'this -> 'env -> kind -> T.kind,
       visit_uvar : 'this -> 'env -> (basic_sort, kind, mtype) uvar_mt * region -> (T.basic_sort, T.kind, T.mtype) T.uvar_mt * region,
       extend_i : 'this -> 'env -> name -> 'env * name,
       extend_t_anno : 'this -> 'env -> name * T.kind -> 'env * name,
       extend_t : 'this -> 'env -> name -> 'env * name
     }
       
fun override_visit_mtype (record : ('this, 'env) type_visitor_vtable) new =
  {
    visit_mtype = new,
    visit_TArrow = #visit_TArrow record,
    visit_TNat = #visit_TNat record,
    visit_TArray = #visit_TArray record,
    visit_TBase = #visit_TBase record,
    visit_TUnit = #visit_TUnit record,
    visit_TProd = #visit_TProd record,
    visit_TUniI = #visit_TUniI record,
    visit_TVar = #visit_TVar record,
    visit_TAbs = #visit_TAbs record,
    visit_TApp = #visit_TApp record,
    visit_TAbsI = #visit_TAbsI record,
    visit_TAppI = #visit_TAppI record,
    visit_TUVar = #visit_TUVar record,
    visit_TDatatype = #visit_TDatatype record,
    visit_TSumbool = #visit_TSumbool record,
    visit_ty = #visit_ty record,
    visit_PTMono = #visit_PTMono record,
    visit_PTUni = #visit_PTUni record,
    visit_datatype = #visit_datatype record,
    visit_constr_core = #visit_constr_core record,
    visit_constr_info = #visit_constr_info record,
    visit_var = #visit_var record,
    visit_basic_sort = #visit_basic_sort record,
    visit_idx = #visit_idx record,
    visit_sort = #visit_sort record,
    visit_kind = #visit_kind record,
    visit_uvar = #visit_uvar record,
    extend_i = #extend_i record,
    extend_t_anno = #extend_t_anno record,
    extend_t = #extend_t record
  }

fun override_visit_TVar (record : ('this, 'env) type_visitor_vtable) new =
  {
    visit_mtype = #visit_mtype record,
    visit_TArrow = #visit_TArrow record,
    visit_TNat = #visit_TNat record,
    visit_TArray = #visit_TArray record,
    visit_TBase = #visit_TBase record,
    visit_TUnit = #visit_TUnit record,
    visit_TProd = #visit_TProd record,
    visit_TUniI = #visit_TUniI record,
    visit_TVar = new,
    visit_TAbs = #visit_TAbs record,
    visit_TApp = #visit_TApp record,
    visit_TAbsI = #visit_TAbsI record,
    visit_TAppI = #visit_TAppI record,
    visit_TUVar = #visit_TUVar record,
    visit_TDatatype = #visit_TDatatype record,
    visit_TSumbool = #visit_TSumbool record,
    visit_ty = #visit_ty record,
    visit_PTMono = #visit_PTMono record,
    visit_PTUni = #visit_PTUni record,
    visit_datatype = #visit_datatype record,
    visit_constr_core = #visit_constr_core record,
    visit_constr_info = #visit_constr_info record,
    visit_var = #visit_var record,
    visit_basic_sort = #visit_basic_sort record,
    visit_idx = #visit_idx record,
    visit_sort = #visit_sort record,
    visit_kind = #visit_kind record,
    visit_uvar = #visit_uvar record,
    extend_i = #extend_i record,
    extend_t_anno = #extend_t_anno record,
    extend_t = #extend_t record
  }

fun override_visit_TAppI (record : ('this, 'env) type_visitor_vtable) new =
  {
    visit_mtype = #visit_mtype record,
    visit_TArrow = #visit_TArrow record,
    visit_TNat = #visit_TNat record,
    visit_TArray = #visit_TArray record,
    visit_TBase = #visit_TBase record,
    visit_TUnit = #visit_TUnit record,
    visit_TProd = #visit_TProd record,
    visit_TUniI = #visit_TUniI record,
    visit_TVar = #visit_TVar record,
    visit_TAbs = #visit_TAbs record,
    visit_TApp = #visit_TApp record,
    visit_TAbsI = #visit_TAbsI record,
    visit_TAppI = new,
    visit_TUVar = #visit_TUVar record,
    visit_TDatatype = #visit_TDatatype record,
    visit_TSumbool = #visit_TSumbool record,
    visit_ty = #visit_ty record,
    visit_PTMono = #visit_PTMono record,
    visit_PTUni = #visit_PTUni record,
    visit_datatype = #visit_datatype record,
    visit_constr_core = #visit_constr_core record,
    visit_constr_info = #visit_constr_info record,
    visit_var = #visit_var record,
    visit_basic_sort = #visit_basic_sort record,
    visit_idx = #visit_idx record,
    visit_sort = #visit_sort record,
    visit_kind = #visit_kind record,
    visit_uvar = #visit_uvar record,
    extend_i = #extend_i record,
    extend_t_anno = #extend_t_anno record,
    extend_t = #extend_t record
  }

fun override_visit_TApp (record : ('this, 'env) type_visitor_vtable) new =
  {
    visit_mtype = #visit_mtype record,
    visit_TArrow = #visit_TArrow record,
    visit_TNat = #visit_TNat record,
    visit_TArray = #visit_TArray record,
    visit_TBase = #visit_TBase record,
    visit_TUnit = #visit_TUnit record,
    visit_TProd = #visit_TProd record,
    visit_TUniI = #visit_TUniI record,
    visit_TVar = #visit_TVar record,
    visit_TAbs = #visit_TAbs record,
    visit_TApp = new,
    visit_TAbsI = #visit_TAbsI record,
    visit_TAppI = #visit_TAppI record,
    visit_TUVar = #visit_TUVar record,
    visit_TDatatype = #visit_TDatatype record,
    visit_TSumbool = #visit_TSumbool record,
    visit_ty = #visit_ty record,
    visit_PTMono = #visit_PTMono record,
    visit_PTUni = #visit_PTUni record,
    visit_datatype = #visit_datatype record,
    visit_constr_core = #visit_constr_core record,
    visit_constr_info = #visit_constr_info record,
    visit_var = #visit_var record,
    visit_basic_sort = #visit_basic_sort record,
    visit_idx = #visit_idx record,
    visit_sort = #visit_sort record,
    visit_kind = #visit_kind record,
    visit_uvar = #visit_uvar record,
    extend_i = #extend_i record,
    extend_t_anno = #extend_t_anno record,
    extend_t = #extend_t record
  }

fun override_visit_TUVar (record : ('this, 'env) type_visitor_vtable) new =
  {
    visit_mtype = #visit_mtype record,
    visit_TArrow = #visit_TArrow record,
    visit_TNat = #visit_TNat record,
    visit_TArray = #visit_TArray record,
    visit_TBase = #visit_TBase record,
    visit_TUnit = #visit_TUnit record,
    visit_TProd = #visit_TProd record,
    visit_TUniI = #visit_TUniI record,
    visit_TVar = #visit_TVar record,
    visit_TAbs = #visit_TAbs record,
    visit_TApp = #visit_TApp record,
    visit_TAbsI = #visit_TAbsI record,
    visit_TAppI = #visit_TAppI record,
    visit_TUVar = new,
    visit_TDatatype = #visit_TDatatype record,
    visit_TSumbool = #visit_TSumbool record,
    visit_ty = #visit_ty record,
    visit_PTMono = #visit_PTMono record,
    visit_PTUni = #visit_PTUni record,
    visit_datatype = #visit_datatype record,
    visit_constr_core = #visit_constr_core record,
    visit_constr_info = #visit_constr_info record,
    visit_var = #visit_var record,
    visit_basic_sort = #visit_basic_sort record,
    visit_idx = #visit_idx record,
    visit_sort = #visit_sort record,
    visit_kind = #visit_kind record,
    visit_uvar = #visit_uvar record,
    extend_i = #extend_i record,
    extend_t_anno = #extend_t_anno record,
    extend_t = #extend_t record
  }

fun override_extend_t_anno (record : ('this, 'env) type_visitor_vtable) new =
  {
    visit_mtype = #visit_mtype record,
    visit_TArrow = #visit_TArrow record,
    visit_TNat = #visit_TNat record,
    visit_TArray = #visit_TArray record,
    visit_TBase = #visit_TBase record,
    visit_TUnit = #visit_TUnit record,
    visit_TProd = #visit_TProd record,
    visit_TUniI = #visit_TUniI record,
    visit_TVar = #visit_TVar record,
    visit_TAbs = #visit_TAbs record,
    visit_TApp = #visit_TApp record,
    visit_TAbsI = #visit_TAbsI record,
    visit_TAppI = #visit_TAppI record,
    visit_TUVar = #visit_TUVar record,
    visit_TDatatype = #visit_TDatatype record,
    visit_TSumbool = #visit_TSumbool record,
    visit_ty = #visit_ty record,
    visit_PTMono = #visit_PTMono record,
    visit_PTUni = #visit_PTUni record,
    visit_datatype = #visit_datatype record,
    visit_constr_core = #visit_constr_core record,
    visit_constr_info = #visit_constr_info record,
    visit_var = #visit_var record,
    visit_basic_sort = #visit_basic_sort record,
    visit_idx = #visit_idx record,
    visit_sort = #visit_sort record,
    visit_kind = #visit_kind record,
    visit_uvar = #visit_uvar record,
    extend_i = #extend_i record,
    extend_t_anno = new,
    extend_t = #extend_t record
  }

type ('this, 'env) type_visitor_interface =
     ('this, 'env) type_visitor_vtable
                                       
datatype 'env type_visitor =
         TypeVisitor of ('env type_visitor, 'env) type_visitor_interface

fun type_visitor_impls_interface (this : 'env type_visitor) :
    ('env type_visitor, 'env) type_visitor_interface =
  let
    val TypeVisitor vtable = this
  in
    vtable
  end

fun new_type_visitor vtable params =
  let
    val vtable = vtable type_visitor_impls_interface params
  in
    TypeVisitor vtable
  end
    
(***************** the default visitor  **********************)    

open VisitorUtil
       
fun default_type_visitor_vtable
      (cast : 'this -> ('this, 'env) type_visitor_interface)
      extend_i
      extend_t
      visit_var
      visit_basic_sort
      visit_idx
      visit_sort
      visit_kind
      visit_uvar
    : ('this, 'env) type_visitor_vtable =
  let
    fun visit_mtype this env data =
      let
        val vtable = cast this
      in
        case data of
	    TArrow data => #visit_TArrow vtable this env data
          | TNat data => #visit_TNat vtable this env data
          | TiBool (i, r) => T.TiBool (#visit_idx vtable this env i, r)
          | TArray data => #visit_TArray vtable this env data
	  | TBase data => #visit_TBase vtable this env data
          | TUnit data => #visit_TUnit vtable this env data
	  | TProd data => #visit_TProd vtable this env data
	  | TUniI data => #visit_TUniI vtable this env data
          | TVar data => #visit_TVar vtable this env data
          | TAbs data => #visit_TAbs vtable this env data
          | TApp data => #visit_TApp vtable this env data
          | TAbsI data => #visit_TAbsI vtable this env data
          | TAppI data => #visit_TAppI vtable this env data
          | TUVar data => #visit_TUVar vtable this env data
          | TDatatype data => #visit_TDatatype vtable this env data
          | TSumbool data => #visit_TSumbool vtable this env data
          | TMap t => T.TMap $ #visit_mtype vtable this env t
          | TState data => T.TState data
          | TTuplePtr (ts, n, r) => T.TTuplePtr (visit_list (#visit_mtype vtable this) env ts, n, r)
      end
    fun visit_TArrow this env data =
      let
        val vtable = cast this
        val ((st1, t1), i, (st2, t2)) = data
        val st1 = StMap.map (#visit_idx vtable this env) st1
        val t1 = #visit_mtype vtable this env t1
        val i = visit_pair (#visit_idx vtable this) (#visit_idx vtable this) env i
        val st2 = StMap.map (#visit_idx vtable this env) st2
        val t2 = #visit_mtype vtable this env t2
      in
        T.TArrow ((st1, t1), i, (st2, t2))
      end
    fun visit_TNat this env data =
      let
        val vtable = cast this
        val (i, r) = data
        val i = #visit_idx vtable this env i
      in
        T.TNat (i, r)
      end
    fun visit_TArray this env data =
      let
        val vtable = cast this
        val (t, i) = data
        val t = #visit_mtype vtable this env t
        val i = #visit_idx vtable this env i
      in
        T.TArray (t, i)
      end
    fun visit_TBase this env data =
      T.TBase data
    fun visit_TUnit this env data =
      T.TUnit data
    fun visit_TProd this env data =
      let
        val vtable = cast this
        val (t1, t2) = data
        val t1 = #visit_mtype vtable this env t1
        val t2 = #visit_mtype vtable this env t2
      in
        T.TProd (t1, t2)
      end
    fun visit_ibind this =
      let
        val vtable = cast this
      in
        Bind.visit_bind (#extend_i vtable this)
      end
    fun visit_tbind this =
      let
        val vtable = cast this
      in
        Bind.visit_bind (#extend_t vtable this)
      end
    fun visit_binds visit_bind this f_anno f_term env (binds : ('namespace, 'classifier, 'name, 'inner) Bind.binds) : ('namespace, 'classifier2, 'name, 'inner2) Bind.binds=
      let
        val visit_ibinds = visit_binds visit_bind this f_anno f_term
        val vtable = cast this
      in
        case binds of
            Bind.BindNil t => Bind.BindNil $ f_term env t
          | Bind.BindCons (anno, bind) => Bind.BindCons (f_anno env anno, visit_bind this visit_ibinds env bind)
      end
    fun visit_ibinds a = visit_binds visit_ibind a
    fun visit_tbinds a = visit_binds visit_tbind a
    fun visit_TUniI this env data =
      let
        val vtable = cast this
        val (s, bind, r) = data
        val s = #visit_sort vtable this env s
        val bind = visit_ibind this (#visit_mtype vtable this) env bind
      in
        T.TUniI (s, bind, r)
      end
    fun visit_TVar this env data =
      let
        val vtable = cast this
        val data = #visit_var vtable this env data
      in
        T.TVar data
      end
    fun extend_t_anno this env (name, _) = 
      let
        val vtable = cast this
      in
        #extend_t vtable this env name
      end
    fun visit_tbind_anno this f env (anno, bind) = 
      let
        val vtable = cast this
        val Bind.Bind (name, t) = bind
        val (env, name) = #extend_t_anno vtable this env (name, anno)
        val t = f env t
        val bind = Bind.Bind (name, t)
      in
        (anno, bind)
      end
    fun visit_TAbs this env data =
      let
        val vtable = cast this
        val (k, bind, r) = data
        val k = #visit_kind vtable this env k
        val (k, bind) = visit_tbind_anno this (#visit_mtype vtable this) env (k, bind)
      in
        T.TAbs (k, bind, r)
      end
    fun visit_TApp this env data =
      let
        val vtable = cast this
        val (t1, t2) = data
        val t1 = #visit_mtype vtable this env t1
        val t2 = #visit_mtype vtable this env t2
      in
        T.TApp (t1, t2)
      end
    fun visit_TAbsI this env data =
      let
        val vtable = cast this
        val (b, bind, r) = data
        val b = #visit_basic_sort vtable this env b
        val bind = visit_ibind this (#visit_mtype vtable this) env bind
      in
        T.TAbsI (b, bind, r)
      end
    fun visit_TAppI this env data =
      let
        val vtable = cast this
        val (t, i) = data
        val t = #visit_mtype vtable this env t
        val i = #visit_idx vtable this env i
      in
        T.TAppI (t, i)
      end
    fun visit_TUVar this env data =
      let
        val vtable = cast this
        val data = #visit_uvar vtable this env data
      in
        T.TUVar data
      end
    fun visit_ty this env data =
      let
        val vtable = cast this
      in
        case data of
	    PTMono data => #visit_PTMono vtable this env data
	  | PTUni data => #visit_PTUni vtable this env data
      end
    fun visit_PTMono this env data =
      let
        val vtable = cast this
        val data = #visit_mtype vtable this env data
      in
        T.PTMono data
      end
    fun visit_PTUni this env data =
      let
        val vtable = cast this
        val (bind, r) = data
        val bind = visit_tbind this (#visit_ty vtable this) env bind
      in
        T.PTUni (bind, r)
      end
    fun visit_constr_core this env (data : mtype constr_core) : T.mtype T.constr_core =
      let
        val vtable = cast this
      in
        visit_ibinds this
                     (#visit_sort vtable this)
                     (visit_pair (#visit_mtype vtable this)
                                 (visit_list (#visit_idx vtable this))) env data
      end
    fun visit_constr_info this env (data : mtype constr_info) : T.mtype T.constr_info =
      let
        val vtable = cast this
      in
        visit_pair (#visit_var vtable this)
                   (visit_tbinds this
                                 return2
                                 (#visit_constr_core vtable this)) env data
      end
    fun visit_datatype this env data =
      let
        val vtable = cast this
        fun visit_constr_decl env (name, c, r) = (name, #visit_constr_core vtable this env c, r)
      in
        visit_tbind this
                    (visit_tbinds this
                                  return2
                                  (visit_pair (visit_list (#visit_basic_sort vtable this))
                                              (visit_list visit_constr_decl))) env data
      end
    fun visit_TDatatype this env data =
      let
        val vtable = cast this
        val (dt, r) = data
        fun visit_constr_decl env (name, c, r) = (name, visit_constr_core this env c, r)
        val dt = #visit_datatype vtable this env dt
      in
        T.TDatatype (dt, r)
      end
    fun visit_TSumbool this env (s1, s2) =
      let
        val vtable = cast this
        val s1 = #visit_sort vtable this env s1
        val s2 = #visit_sort vtable this env s2
      in
        T.TSumbool (s1, s2)
      end
  in
    {
      visit_mtype = visit_mtype,
      visit_TArrow = visit_TArrow,
      visit_TNat = visit_TNat,
      visit_TArray = visit_TArray,
      visit_TBase = visit_TBase,
      visit_TUnit = visit_TUnit,
      visit_TProd = visit_TProd,
      visit_TUniI = visit_TUniI,
      visit_TVar = visit_TVar,
      visit_TAbs = visit_TAbs,
      visit_TApp = visit_TApp,
      visit_TAbsI = visit_TAbsI,
      visit_TAppI = visit_TAppI,
      visit_TUVar = visit_TUVar,
      visit_TDatatype = visit_TDatatype,
      visit_TSumbool = visit_TSumbool,
      visit_ty = visit_ty,
      visit_PTMono = visit_PTMono,
      visit_PTUni = visit_PTUni,
      visit_datatype = visit_datatype,
      visit_constr_core = visit_constr_core,
      visit_constr_info = visit_constr_info,
      visit_var = visit_var,
      visit_basic_sort = visit_basic_sort,
      visit_idx = visit_idx,
      visit_sort = visit_sort,
      visit_kind = visit_kind,
      visit_uvar = visit_uvar,
      extend_i = extend_i,
      extend_t_anno = extend_t_anno,
      extend_t = extend_t
    }
  end

end

