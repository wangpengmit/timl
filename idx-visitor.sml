signature IDX_VISITOR_PARAMS = sig
  structure S : IDX
  structure T : IDX
  sharing type S.base_sort = T.base_sort
  sharing type S.name = T.name
  sharing type S.region = T.region
end

functor IdxVisitorFn (Params : IDX_VISITOR_PARAMS) = struct

open Params
open Unbound
open Namespaces
open Binders
open Operators
open Region
open S

infixr 0 $
       
type ('this, 'env) idx_visitor_vtable =
     {
       visit_basic_sort : 'this -> 'env -> basic_sort -> T.basic_sort,
       visit_BSBase : 'this -> 'env -> base_sort  -> T.basic_sort,
       visit_BSArrow : 'this -> 'env -> basic_sort * basic_sort -> T.basic_sort,
       visit_BSUVar : 'this -> 'env -> basic_sort uvar_bs -> T.basic_sort,
       visit_idx : 'this -> 'env -> idx -> T.idx,
       visit_IVar : 'this -> 'env -> var * sort list -> T.idx,
       visit_IConst : 'this -> 'env -> Operators.idx_const * region -> T.idx,
       visit_IUnOp : 'this -> 'env -> Operators.idx_un_op * idx * region -> T.idx,
       visit_IBinOp : 'this -> 'env -> Operators.idx_bin_op * idx * idx -> T.idx,
       visit_IIte : 'this -> 'env -> idx * idx * idx * region -> T.idx,
       visit_IAbs : 'this -> 'env -> basic_sort * (name * idx) Bind.ibind * region -> T.idx,
       visit_IUVar : 'this -> 'env -> (basic_sort, idx) uvar_i * region -> T.idx,
       visit_prop : 'this -> 'env -> prop -> T.prop,
       visit_PTrueFalse : 'this -> 'env -> bool * region -> T.prop,
       visit_PBinConn : 'this -> 'env -> Operators.bin_conn * prop * prop -> T.prop,
       visit_PNot : 'this -> 'env -> prop * region -> T.prop,
       visit_PBinPred : 'this -> 'env -> Operators.bin_pred * idx * idx -> T.prop,
       visit_PQuan : 'this -> 'env -> idx exists_anno Operators.quan * basic_sort * (name * prop) Bind.ibind * region -> T.prop,
       visit_sort : 'this -> 'env -> sort -> T.sort,
       visit_SBasic : 'this -> 'env -> basic_sort * region -> T.sort,
       visit_SSubset : 'this -> 'env -> (basic_sort * region) * (name * prop) Bind.ibind * region -> T.sort,
       visit_SUVar : 'this -> 'env -> (basic_sort, sort) uvar_s * region -> T.sort,
       visit_SAbs : 'this -> 'env -> basic_sort * (name * sort) Bind.ibind * region -> T.sort,
       visit_SApp : 'this -> 'env -> sort * idx -> T.sort,
       visit_var : 'this -> 'env -> var -> T.var,
       visit_uvar_bs : 'this -> 'env -> basic_sort uvar_bs -> T.basic_sort T.uvar_bs,
       visit_uvar_i : 'this -> 'env -> (basic_sort, idx) uvar_i * region -> (T.basic_sort, T.idx) T.uvar_i * region,
       visit_uvar_s : 'this -> 'env -> (basic_sort, sort) uvar_s * region -> (T.basic_sort, T.sort) T.uvar_s * region,
       visit_quan : 'this -> 'env -> idx exists_anno quan -> T.idx T.exists_anno quan,
       extend : 'this -> 'env -> name -> 'env * name
     }
       
type ('this, 'env) idx_visitor_interface =
     ('this, 'env) idx_visitor_vtable
                                       
datatype 'env idx_visitor =
         IdxVisitor of ('env idx_visitor, 'env) idx_visitor_interface

fun idx_visitor_impls_interface (this : 'env idx_visitor) :
    ('env idx_visitor, 'env) idx_visitor_interface =
  let
    val IdxVisitor vtable = this
  in
    vtable
  end

fun new_idx_visitor vtable params =
  let
    val vtable = vtable idx_visitor_impls_interface params
  in
    IdxVisitor vtable
  end
    
fun override_visit_idx (record : ('this, 'env) idx_visitor_vtable) new =
  {
    visit_basic_sort = #visit_basic_sort record,
    visit_BSBase = #visit_BSBase record,
    visit_BSArrow = #visit_BSArrow record,
    visit_BSUVar = #visit_BSUVar record,
    visit_idx = new,
    visit_IVar = #visit_IVar record,
    visit_IConst = #visit_IConst record,
    visit_IUnOp = #visit_IUnOp record,
    visit_IBinOp = #visit_IBinOp record,
    visit_IIte = #visit_IIte record,
    visit_IAbs = #visit_IAbs record,
    visit_IUVar = #visit_IUVar record,
    visit_prop = #visit_prop record,
    visit_PTrueFalse = #visit_PTrueFalse record,
    visit_PBinConn = #visit_PBinConn record,
    visit_PNot = #visit_PNot record,
    visit_PBinPred = #visit_PBinPred record,
    visit_PQuan = #visit_PQuan record,
    visit_sort = #visit_sort record,
    visit_SBasic = #visit_SBasic record,
    visit_SSubset = #visit_SSubset record,
    visit_SUVar = #visit_SUVar record,
    visit_SAbs = #visit_SAbs record,
    visit_SApp = #visit_SApp record,
    visit_var = #visit_var record,
    visit_uvar_bs = #visit_uvar_bs record,
    visit_uvar_i = #visit_uvar_i record,
    visit_uvar_s = #visit_uvar_s record,
    visit_quan = #visit_quan record,
    extend = #extend record
  }

fun override_visit_BSUVar (record : ('this, 'env) idx_visitor_vtable) new =
  {
    visit_basic_sort = #visit_basic_sort record,
    visit_BSBase = #visit_BSBase record,
    visit_BSArrow = #visit_BSArrow record,
    visit_BSUVar = new,
    visit_idx = #visit_idx record,
    visit_IVar = #visit_IVar record,
    visit_IConst = #visit_IConst record,
    visit_IUnOp = #visit_IUnOp record,
    visit_IBinOp = #visit_IBinOp record,
    visit_IIte = #visit_IIte record,
    visit_IAbs = #visit_IAbs record,
    visit_IUVar = #visit_IUVar record,
    visit_prop = #visit_prop record,
    visit_PTrueFalse = #visit_PTrueFalse record,
    visit_PBinConn = #visit_PBinConn record,
    visit_PNot = #visit_PNot record,
    visit_PBinPred = #visit_PBinPred record,
    visit_PQuan = #visit_PQuan record,
    visit_sort = #visit_sort record,
    visit_SBasic = #visit_SBasic record,
    visit_SSubset = #visit_SSubset record,
    visit_SUVar = #visit_SUVar record,
    visit_SAbs = #visit_SAbs record,
    visit_SApp = #visit_SApp record,
    visit_var = #visit_var record,
    visit_uvar_bs = #visit_uvar_bs record,
    visit_uvar_i = #visit_uvar_i record,
    visit_uvar_s = #visit_uvar_s record,
    visit_quan = #visit_quan record,
    extend = #extend record
  }

fun override_visit_IVar (record : ('this, 'env) idx_visitor_vtable) new =
  {
    visit_basic_sort = #visit_basic_sort record,
    visit_BSBase = #visit_BSBase record,
    visit_BSArrow = #visit_BSArrow record,
    visit_BSUVar = #visit_BSUVar record,
    visit_idx = #visit_idx record,
    visit_IVar = new,
    visit_IConst = #visit_IConst record,
    visit_IUnOp = #visit_IUnOp record,
    visit_IBinOp = #visit_IBinOp record,
    visit_IIte = #visit_IIte record,
    visit_IAbs = #visit_IAbs record,
    visit_IUVar = #visit_IUVar record,
    visit_prop = #visit_prop record,
    visit_PTrueFalse = #visit_PTrueFalse record,
    visit_PBinConn = #visit_PBinConn record,
    visit_PNot = #visit_PNot record,
    visit_PBinPred = #visit_PBinPred record,
    visit_PQuan = #visit_PQuan record,
    visit_sort = #visit_sort record,
    visit_SBasic = #visit_SBasic record,
    visit_SSubset = #visit_SSubset record,
    visit_SUVar = #visit_SUVar record,
    visit_SAbs = #visit_SAbs record,
    visit_SApp = #visit_SApp record,
    visit_var = #visit_var record,
    visit_uvar_bs = #visit_uvar_bs record,
    visit_uvar_i = #visit_uvar_i record,
    visit_uvar_s = #visit_uvar_s record,
    visit_quan = #visit_quan record,
    extend = #extend record
  }

fun override_visit_IBinOp (record : ('this, 'env) idx_visitor_vtable) new =
  {
    visit_basic_sort = #visit_basic_sort record,
    visit_BSBase = #visit_BSBase record,
    visit_BSArrow = #visit_BSArrow record,
    visit_BSUVar = #visit_BSUVar record,
    visit_idx = #visit_idx record,
    visit_IVar = #visit_IVar record,
    visit_IConst = #visit_IConst record,
    visit_IUnOp = #visit_IUnOp record,
    visit_IBinOp = new,
    visit_IIte = #visit_IIte record,
    visit_IAbs = #visit_IAbs record,
    visit_IUVar = #visit_IUVar record,
    visit_prop = #visit_prop record,
    visit_PTrueFalse = #visit_PTrueFalse record,
    visit_PBinConn = #visit_PBinConn record,
    visit_PNot = #visit_PNot record,
    visit_PBinPred = #visit_PBinPred record,
    visit_PQuan = #visit_PQuan record,
    visit_sort = #visit_sort record,
    visit_SBasic = #visit_SBasic record,
    visit_SSubset = #visit_SSubset record,
    visit_SUVar = #visit_SUVar record,
    visit_SAbs = #visit_SAbs record,
    visit_SApp = #visit_SApp record,
    visit_var = #visit_var record,
    visit_uvar_bs = #visit_uvar_bs record,
    visit_uvar_i = #visit_uvar_i record,
    visit_uvar_s = #visit_uvar_s record,
    visit_quan = #visit_quan record,
    extend = #extend record
  }

fun override_visit_IIte (record : ('this, 'env) idx_visitor_vtable) new =
  {
    visit_basic_sort = #visit_basic_sort record,
    visit_BSBase = #visit_BSBase record,
    visit_BSArrow = #visit_BSArrow record,
    visit_BSUVar = #visit_BSUVar record,
    visit_idx = #visit_idx record,
    visit_IVar = #visit_IVar record,
    visit_IConst = #visit_IConst record,
    visit_IUnOp = #visit_IUnOp record,
    visit_IBinOp = #visit_IBinOp record,
    visit_IIte = new,
    visit_IAbs = #visit_IAbs record,
    visit_IUVar = #visit_IUVar record,
    visit_prop = #visit_prop record,
    visit_PTrueFalse = #visit_PTrueFalse record,
    visit_PBinConn = #visit_PBinConn record,
    visit_PNot = #visit_PNot record,
    visit_PBinPred = #visit_PBinPred record,
    visit_PQuan = #visit_PQuan record,
    visit_sort = #visit_sort record,
    visit_SBasic = #visit_SBasic record,
    visit_SSubset = #visit_SSubset record,
    visit_SUVar = #visit_SUVar record,
    visit_SAbs = #visit_SAbs record,
    visit_SApp = #visit_SApp record,
    visit_var = #visit_var record,
    visit_uvar_bs = #visit_uvar_bs record,
    visit_uvar_i = #visit_uvar_i record,
    visit_uvar_s = #visit_uvar_s record,
    visit_quan = #visit_quan record,
    extend = #extend record
  }

fun override_visit_IUVar (record : ('this, 'env) idx_visitor_vtable) new =
  {
    visit_basic_sort = #visit_basic_sort record,
    visit_BSBase = #visit_BSBase record,
    visit_BSArrow = #visit_BSArrow record,
    visit_BSUVar = #visit_BSUVar record,
    visit_idx = #visit_idx record,
    visit_IVar = #visit_IVar record,
    visit_IConst = #visit_IConst record,
    visit_IUnOp = #visit_IUnOp record,
    visit_IBinOp = #visit_IBinOp record,
    visit_IIte = #visit_IIte record,
    visit_IAbs = #visit_IAbs record,
    visit_IUVar = new,
    visit_prop = #visit_prop record,
    visit_PTrueFalse = #visit_PTrueFalse record,
    visit_PBinConn = #visit_PBinConn record,
    visit_PNot = #visit_PNot record,
    visit_PBinPred = #visit_PBinPred record,
    visit_PQuan = #visit_PQuan record,
    visit_sort = #visit_sort record,
    visit_SBasic = #visit_SBasic record,
    visit_SSubset = #visit_SSubset record,
    visit_SUVar = #visit_SUVar record,
    visit_SAbs = #visit_SAbs record,
    visit_SApp = #visit_SApp record,
    visit_var = #visit_var record,
    visit_uvar_bs = #visit_uvar_bs record,
    visit_uvar_i = #visit_uvar_i record,
    visit_uvar_s = #visit_uvar_s record,
    visit_quan = #visit_quan record,
    extend = #extend record
  }

fun override_visit_SApp (record : ('this, 'env) idx_visitor_vtable) new =
  {
    visit_basic_sort = #visit_basic_sort record,
    visit_BSBase = #visit_BSBase record,
    visit_BSArrow = #visit_BSArrow record,
    visit_BSUVar = #visit_BSUVar record,
    visit_idx = #visit_idx record,
    visit_IVar = #visit_IVar record,
    visit_IConst = #visit_IConst record,
    visit_IUnOp = #visit_IUnOp record,
    visit_IBinOp = #visit_IBinOp record,
    visit_IIte = #visit_IIte record,
    visit_IAbs = #visit_IAbs record,
    visit_IUVar = #visit_IUVar record,
    visit_prop = #visit_prop record,
    visit_PTrueFalse = #visit_PTrueFalse record,
    visit_PBinConn = #visit_PBinConn record,
    visit_PNot = #visit_PNot record,
    visit_PBinPred = #visit_PBinPred record,
    visit_PQuan = #visit_PQuan record,
    visit_sort = #visit_sort record,
    visit_SBasic = #visit_SBasic record,
    visit_SSubset = #visit_SSubset record,
    visit_SUVar = #visit_SUVar record,
    visit_SAbs = #visit_SAbs record,
    visit_SApp = new,
    visit_var = #visit_var record,
    visit_uvar_bs = #visit_uvar_bs record,
    visit_uvar_i = #visit_uvar_i record,
    visit_uvar_s = #visit_uvar_s record,
    visit_quan = #visit_quan record,
    extend = #extend record
  }

fun override_visit_SUVar (record : ('this, 'env) idx_visitor_vtable) new =
  {
    visit_basic_sort = #visit_basic_sort record,
    visit_BSBase = #visit_BSBase record,
    visit_BSArrow = #visit_BSArrow record,
    visit_BSUVar = #visit_BSUVar record,
    visit_idx = #visit_idx record,
    visit_IVar = #visit_IVar record,
    visit_IConst = #visit_IConst record,
    visit_IUnOp = #visit_IUnOp record,
    visit_IBinOp = #visit_IBinOp record,
    visit_IIte = #visit_IIte record,
    visit_IAbs = #visit_IAbs record,
    visit_IUVar = #visit_IUVar record,
    visit_prop = #visit_prop record,
    visit_PTrueFalse = #visit_PTrueFalse record,
    visit_PBinConn = #visit_PBinConn record,
    visit_PNot = #visit_PNot record,
    visit_PBinPred = #visit_PBinPred record,
    visit_PQuan = #visit_PQuan record,
    visit_sort = #visit_sort record,
    visit_SBasic = #visit_SBasic record,
    visit_SSubset = #visit_SSubset record,
    visit_SUVar = new,
    visit_SAbs = #visit_SAbs record,
    visit_SApp = #visit_SApp record,
    visit_var = #visit_var record,
    visit_uvar_bs = #visit_uvar_bs record,
    visit_uvar_i = #visit_uvar_i record,
    visit_uvar_s = #visit_uvar_s record,
    visit_quan = #visit_quan record,
    extend = #extend record
  }

(***************** the default visitor  **********************)    

open VisitorUtil
       
fun default_idx_visitor_vtable
      (cast : 'this -> ('this, 'env) idx_visitor_interface)
      extend
      visit_var
      visit_uvar_bs
      visit_uvar_i
      visit_uvar_s
      visit_quan
    : ('this, 'env) idx_visitor_vtable =
  let
    fun visit_basic_sort this env data =
      let
        val vtable = cast this
      in
        case data of
            BSBase data => #visit_BSBase vtable this env data
          | BSArrow data => #visit_BSArrow vtable this env data
          | BSUVar data => #visit_BSUVar vtable this env data
      end
    fun visit_BSBase this env data =
      T.BSBase data
    fun visit_BSArrow this env data =
      let
        val vtable = cast this
        val (b1, b2) = data
        val b1 = #visit_basic_sort vtable this env b1
        val b2 = #visit_basic_sort vtable this env b2
      in
        T.BSArrow (b1, b2)
      end
    fun visit_BSUVar this env data =
      let
        val vtable = cast this
        val data = #visit_uvar_bs vtable this env data
      in
        T.BSUVar data
      end
    fun visit_idx this env data =
      let
        val vtable = cast this
      in
        case data of
	    IVar data => #visit_IVar vtable this env data
          | IConst data => #visit_IConst vtable this env data
          | IUnOp data => #visit_IUnOp vtable this env data
          | IBinOp data => #visit_IBinOp vtable this env data
          | IIte data => #visit_IIte vtable this env data
          | IAbs data => #visit_IAbs vtable this env data
          | IUVar data => #visit_IUVar vtable this env data
          | IState st => T.IState $ StMap.map (#visit_idx vtable this env) st
      end
    fun visit_IVar this env data =
      let
        val vtable = cast this
        val data = visit_pair (#visit_var vtable this) (visit_list (#visit_sort vtable this)) env data
      in
        T.IVar data
      end
    fun visit_IConst this env data =
      T.IConst data
    fun visit_IUnOp this env data =
      let
        val vtable = cast this
        val (opr, i, r) = data
        val i = #visit_idx vtable this env i
      in
        T.IUnOp (opr, i, r)
      end
    fun visit_IBinOp this env data =
      let
        val vtable = cast this
        val (opr, i1, i2) = data
        val i1 = #visit_idx vtable this env i1
        val i2 = #visit_idx vtable this env i2
      in
        T.IBinOp (opr, i1, i2)
      end
    fun visit_IIte this env data =
      let
        val vtable = cast this
        val (i1, i2, i3, r) = data
        val i1 = #visit_idx vtable this env i1
        val i2 = #visit_idx vtable this env i2
        val i3 = #visit_idx vtable this env i3
      in
        T.IIte (i1, i2, i3, r)
      end
    fun visit_ibind this =
      let
        val vtable = cast this
      in
        Bind.visit_bind (#extend vtable this)
      end
    fun visit_IAbs this env data =
      let
        val vtable = cast this
        val (b, bind, r) = data
        val b = #visit_basic_sort vtable this env b
        val bind = visit_ibind this (#visit_idx vtable this) env bind
      in
        T.IAbs (b, bind, r)
      end
    fun visit_IUVar this env data =
      let
        val vtable = cast this
        val data = #visit_uvar_i vtable this env data
      in
        T.IUVar data
      end
    fun visit_prop this env data =
      let
        val vtable = cast this
      in
        case data of
	    PTrueFalse data => #visit_PTrueFalse vtable this env data
          | PBinConn data => #visit_PBinConn vtable this env data
          | PNot data => #visit_PNot vtable this env data
	  | PBinPred data => #visit_PBinPred vtable this env data
          | PQuan data => #visit_PQuan vtable this env data
      end
    fun visit_PTrueFalse this env data =
      T.PTrueFalse data
    fun visit_PBinConn this env data =
      let
        val vtable = cast this
        val (opr, p1, p2) = data
        val p1 = #visit_prop vtable this env p1
        val p2 = #visit_prop vtable this env p2
      in
        T.PBinConn (opr, p1, p2)
      end
    fun visit_PNot this env data =
      let
        val vtable = cast this
        val (p, r) = data
        val p = #visit_prop vtable this env p
      in
        T.PNot (p, r)
      end
    fun visit_PBinPred this env data =
      let
        val vtable = cast this
        val (opr, i1, i2) = data
        val i1 = #visit_idx vtable this env i1
        val i2 = #visit_idx vtable this env i2
      in
        T.PBinPred (opr, i1, i2)
      end
    fun visit_PQuan this env data =
      let
        val vtable = cast this
        val (q, b, bind, r) = data
        val q = #visit_quan vtable this env q
        val b = #visit_basic_sort vtable this env b
        val bind = visit_ibind this (#visit_prop vtable this) env bind
      in
        T.PQuan (q, b, bind, r)
      end
    fun visit_sort this env data =
      let
        val vtable = cast this
      in
        case data of
	    SBasic data => #visit_SBasic vtable this env data
	  | SSubset data => #visit_SSubset vtable this env data
          | SUVar data => #visit_SUVar vtable this env data
          | SAbs data => #visit_SAbs vtable this env data
          | SApp data => #visit_SApp vtable this env data
      end
    fun visit_SBasic this env data =
      let
        val vtable = cast this
        val (b, r) = data
        val b = #visit_basic_sort vtable this env b
      in
        T.SBasic (b, r)
      end
    fun visit_SSubset this env data =
      let
        val vtable = cast this
        val ((b, r), bind, r2) = data
        val b = #visit_basic_sort vtable this env b
        val bind = visit_ibind this (#visit_prop vtable this) env bind
      in
        T.SSubset ((b, r), bind, r2)
      end
    fun visit_SUVar this env data =
      let
        val vtable = cast this
        val data = #visit_uvar_s vtable this env data
      in
        T.SUVar data
      end
    fun visit_SAbs this env data =
      let
        val vtable = cast this
        val (b, bind, r) = data
        val b = #visit_basic_sort vtable this env b
        val bind = visit_ibind this (#visit_sort vtable this) env bind
      in
        T.SAbs (b, bind, r)
      end
    fun visit_SApp this env data =
      let
        val vtable = cast this
        val (s, i) = data
        val s = #visit_sort vtable this env s
        val i = #visit_idx vtable this env i
      in
        T.SApp (s, i)
      end
  in
    {
      visit_basic_sort = visit_basic_sort,
      visit_BSBase = visit_BSBase,
      visit_BSArrow = visit_BSArrow,
      visit_BSUVar = visit_BSUVar,
      visit_idx = visit_idx,
      visit_IVar = visit_IVar,
      visit_IConst = visit_IConst,
      visit_IUnOp = visit_IUnOp,
      visit_IBinOp = visit_IBinOp,
      visit_IIte = visit_IIte,
      visit_IAbs = visit_IAbs,
      visit_IUVar = visit_IUVar,
      visit_prop = visit_prop,
      visit_PTrueFalse = visit_PTrueFalse,
      visit_PBinConn = visit_PBinConn,
      visit_PNot = visit_PNot,
      visit_PBinPred = visit_PBinPred,
      visit_PQuan = visit_PQuan,
      visit_sort = visit_sort,
      visit_SBasic = visit_SBasic,
      visit_SSubset = visit_SSubset,
      visit_SUVar = visit_SUVar,
      visit_SAbs = visit_SAbs,
      visit_SApp = visit_SApp,
      visit_var = visit_var,
      visit_uvar_bs = visit_uvar_bs,
      visit_uvar_i = visit_uvar_i,
      visit_uvar_s = visit_uvar_s,
      visit_quan = visit_quan,
      extend = extend
    }
  end

end
