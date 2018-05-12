structure MicroTiMLVisitor2 = struct

open Operators
open MicroTiML
open Unbound
open Util
       
infixr 0 $
infix 0 !!

(***************** type visitor2  **********************)    

type ('this, 'env, 'var, 'bsort, 'idx, 'sort, 'var2, 'bsort2, 'idx2, 'sort2, 'var3, 'bsort3, 'idx3, 'sort3) ty_visitor2_vtable =
     {
       visit2_kind : 'this -> 'env -> 'bsort kind -> 'bsort2 kind -> 'bsort3 kind,
       visit2_KType : 'this -> 'env -> unit -> 'bsort2 kind -> 'bsort3 kind,
       visit2_KArrow : 'this -> 'env -> 'bsort * 'bsort kind -> 'bsort2 kind -> 'bsort3 kind,
       visit2_KArrowT : 'this -> 'env -> 'bsort kind * 'bsort kind -> 'bsort2 kind -> 'bsort3 kind,
       visit2_ty : 'this -> 'env -> ('var, 'bsort, 'idx, 'sort) ty -> ('var2, 'bsort2, 'idx2, 'sort2) ty -> ('var3, 'bsort3, 'idx3, 'sort3) ty,
       visit2_TVar : 'this -> 'env -> 'var * 'bsort kind list -> ('var2, 'bsort2, 'idx2, 'sort2) ty -> ('var3, 'bsort3, 'idx3, 'sort3) ty,
       visit2_TConst : 'this -> 'env -> ty_const -> ('var2, 'bsort2, 'idx2, 'sort2) ty -> ('var3, 'bsort3, 'idx3, 'sort3) ty,
       visit2_TBinOp : 'this -> 'env -> ty_bin_op * ('var, 'bsort, 'idx, 'sort) ty * ('var, 'bsort, 'idx, 'sort) ty -> ('var2, 'bsort2, 'idx2, 'sort2) ty -> ('var3, 'bsort3, 'idx3, 'sort3) ty,
       visit2_TArrow : 'this -> 'env -> ('idx * ('var, 'bsort, 'idx, 'sort) ty) * 'idx * ('idx * ('var, 'bsort, 'idx, 'sort) ty) -> ('var2, 'bsort2, 'idx2, 'sort2) ty -> ('var3, 'bsort3, 'idx3, 'sort3) ty,
       visit2_TAbsI : 'this -> 'env -> ('bsort, ('var, 'bsort, 'idx, 'sort) ty) ibind_anno -> ('var2, 'bsort2, 'idx2, 'sort2) ty -> ('var3, 'bsort3, 'idx3, 'sort3) ty,
       visit2_TAppI : 'this -> 'env -> ('var, 'bsort, 'idx, 'sort) ty * 'idx -> ('var2, 'bsort2, 'idx2, 'sort2) ty -> ('var3, 'bsort3, 'idx3, 'sort3) ty,
       visit2_TQuan : 'this -> 'env -> unit quan * ('bsort kind, ('var, 'bsort, 'idx, 'sort) ty) tbind_anno -> ('var2, 'bsort2, 'idx2, 'sort2) ty -> ('var3, 'bsort3, 'idx3, 'sort3) ty,
       visit2_TQuanI : 'this -> 'env -> unit quan * ('sort, ('var, 'bsort, 'idx, 'sort) ty) ibind_anno -> ('var2, 'bsort2, 'idx2, 'sort2) ty -> ('var3, 'bsort3, 'idx3, 'sort3) ty,
       visit2_TRec : 'this -> 'env -> ('bsort kind, ('var, 'bsort, 'idx, 'sort) ty) tbind_anno -> ('var2, 'bsort2, 'idx2, 'sort2) ty -> ('var3, 'bsort3, 'idx3, 'sort3) ty,
       visit2_TNat : 'this -> 'env -> 'idx -> ('var2, 'bsort2, 'idx2, 'sort2) ty -> ('var3, 'bsort3, 'idx3, 'sort3) ty,
       visit2_TArr : 'this -> 'env -> ('var, 'bsort, 'idx, 'sort) ty * 'idx -> ('var2, 'bsort2, 'idx2, 'sort2) ty -> ('var3, 'bsort3, 'idx3, 'sort3) ty,
       visit2_TAbsT : 'this -> 'env -> ('bsort kind, ('var, 'bsort, 'idx, 'sort) ty) tbind_anno -> ('var2, 'bsort2, 'idx2, 'sort2) ty -> ('var3, 'bsort3, 'idx3, 'sort3) ty,
       visit2_TAppT : 'this -> 'env -> ('var, 'bsort, 'idx, 'sort) ty * ('var, 'bsort, 'idx, 'sort) ty -> ('var2, 'bsort2, 'idx2, 'sort2) ty -> ('var3, 'bsort3, 'idx3, 'sort3) ty,
       visit2_TProdEx : 'this -> 'env -> (('var, 'bsort, 'idx, 'sort) ty * bool) * (('var, 'bsort, 'idx, 'sort) ty * bool) -> ('var2, 'bsort2, 'idx2, 'sort2) ty -> ('var3, 'bsort3, 'idx3, 'sort3) ty,
       visit2_TArrowTAL : 'this -> 'env -> ('var, 'bsort, 'idx, 'sort) ty Rctx.map * 'idx -> ('var2, 'bsort2, 'idx2, 'sort2) ty -> ('var3, 'bsort3, 'idx3, 'sort3) ty,
       visit2_var : 'this -> 'env -> 'var -> 'var2 -> 'var3,
       visit2_bsort : 'this -> 'env -> 'bsort -> 'bsort2 -> 'bsort3,
       visit2_idx : 'this -> 'env -> 'idx -> 'idx2 -> 'idx3,
       visit2_sort : 'this -> 'env -> 'sort -> 'sort2 -> 'sort3,
       visit2_ty_const : 'this -> 'env -> ty_const -> ty_const -> ty_const,
       visit2_ty_bin_op : 'this -> 'env -> ty_bin_op -> ty_bin_op -> ty_bin_op,
       visit2_quan : 'this -> 'env -> unit quan -> unit quan -> unit quan,
       visit2_ibind_anno_bsort : 'this -> ('env -> 'bsort -> 'bsort2 -> 'bsort3) -> ('env -> ('var, 'bsort, 'idx, 'sort) ty -> ('var2, 'bsort2, 'idx2, 'sort2) ty -> ('var3, 'bsort3, 'idx3, 'sort3) ty) -> 'env -> ('bsort, ('var, 'bsort, 'idx, 'sort) ty) ibind_anno -> ('bsort2, ('var2, 'bsort2, 'idx2, 'sort2) ty) ibind_anno -> ('bsort3, ('var3, 'bsort3, 'idx3, 'sort3) ty) ibind_anno,
       visit2_ibind_anno_sort : 'this -> ('env -> 'sort -> 'sort2 -> 'sort3) -> ('env -> ('var, 'bsort, 'idx, 'sort) ty -> ('var2, 'bsort2, 'idx2, 'sort2) ty -> ('var3, 'bsort3, 'idx3, 'sort3) ty) -> 'env -> ('sort, ('var, 'bsort, 'idx, 'sort) ty) ibind_anno -> ('sort2, ('var2, 'bsort2, 'idx2, 'sort2) ty) ibind_anno -> ('sort3, ('var3, 'bsort3, 'idx3, 'sort3) ty) ibind_anno,
       visit2_tbind_anno : 'this -> ('env -> 'bsort kind -> 'bsort2 kind -> 'bsort3 kind) -> ('env -> ('var, 'bsort, 'idx, 'sort) ty -> ('var2, 'bsort2, 'idx2, 'sort2) ty -> ('var3, 'bsort3, 'idx3, 'sort3) ty) -> 'env -> ('bsort kind, ('var, 'bsort, 'idx, 'sort) ty) tbind_anno -> ('bsort2 kind, ('var2, 'bsort2, 'idx2, 'sort2) ty) tbind_anno -> ('bsort3 kind, ('var3, 'bsort3, 'idx3, 'sort3) ty) tbind_anno,
       extend_i : 'this -> 'env -> iname -> 'env * iname,
       extend_t : 'this -> 'env -> tname -> 'env * tname
     }
       
type ('this, 'env, 'var, 'bsort, 'idx, 'sort, 'var2, 'bsort2, 'idx2, 'sort2, 'var3, 'bsort3, 'idx3, 'sort3) ty_visitor2_interface =
     ('this, 'env, 'var, 'bsort, 'idx, 'sort, 'var2, 'bsort2, 'idx2, 'sort2, 'var3, 'bsort3, 'idx3, 'sort3) ty_visitor2_vtable
                                       
fun override_visit2_TVar (record : ('this, 'env, 'var, 'bsort, 'idx, 'sort, 'var2, 'bsort2, 'idx2, 'sort2, 'var3, 'bsort3, 'idx3, 'sort3) ty_visitor2_vtable) new : ('this, 'env, 'var, 'bsort, 'idx, 'sort, 'var2, 'bsort2, 'idx2, 'sort2, 'var3, 'bsort3, 'idx3, 'sort3) ty_visitor2_vtable =
  {
       visit2_kind = #visit2_kind record,
       visit2_KType = #visit2_KType record,
       visit2_KArrow = #visit2_KArrow record,
       visit2_KArrowT = #visit2_KArrowT record,
       visit2_ty = #visit2_ty record,
       visit2_TVar = new,
       visit2_TConst = #visit2_TConst record,
       visit2_TBinOp = #visit2_TBinOp record,
       visit2_TArrow = #visit2_TArrow record,
       visit2_TAbsI = #visit2_TAbsI record,
       visit2_TAppI = #visit2_TAppI record,
       visit2_TQuan = #visit2_TQuan record,
       visit2_TQuanI = #visit2_TQuanI record,
       visit2_TRec = #visit2_TRec record,
       visit2_TNat = #visit2_TNat record,
       visit2_TArr = #visit2_TArr record,
       visit2_TAbsT = #visit2_TAbsT record,
       visit2_TAppT = #visit2_TAppT record,
       visit2_TProdEx = #visit2_TProdEx record,
       visit2_TArrowTAL = #visit2_TArrowTAL record,
       visit2_var = #visit2_var record,
       visit2_bsort = #visit2_bsort record,
       visit2_idx = #visit2_idx record,
       visit2_sort = #visit2_sort record,
       visit2_ty_const = #visit2_ty_const record,
       visit2_ty_bin_op = #visit2_ty_bin_op record,
       visit2_quan = #visit2_quan record,
       visit2_ibind_anno_bsort = #visit2_ibind_anno_bsort record,
       visit2_ibind_anno_sort = #visit2_ibind_anno_sort record,
       visit2_tbind_anno = #visit2_tbind_anno record,
       extend_i = #extend_i record,
       extend_t = #extend_t record
  }

fun override_visit2_TAppT (record : ('this, 'env, 'var, 'bsort, 'idx, 'sort, 'var2, 'bsort2, 'idx2, 'sort2, 'var3, 'bsort3, 'idx3, 'sort3) ty_visitor2_vtable) new : ('this, 'env, 'var, 'bsort, 'idx, 'sort, 'var2, 'bsort2, 'idx2, 'sort2, 'var3, 'bsort3, 'idx3, 'sort3) ty_visitor2_vtable =
  {
       visit2_kind = #visit2_kind record,
       visit2_KType = #visit2_KType record,
       visit2_KArrow = #visit2_KArrow record,
       visit2_KArrowT = #visit2_KArrowT record,
       visit2_ty = #visit2_ty record,
       visit2_TVar = #visit2_TVar record,
       visit2_TConst = #visit2_TConst record,
       visit2_TBinOp = #visit2_TBinOp record,
       visit2_TArrow = #visit2_TArrow record,
       visit2_TAbsI = #visit2_TAbsI record,
       visit2_TAppI = #visit2_TAppI record,
       visit2_TQuan = #visit2_TQuan record,
       visit2_TQuanI = #visit2_TQuanI record,
       visit2_TRec = #visit2_TRec record,
       visit2_TNat = #visit2_TNat record,
       visit2_TArr = #visit2_TArr record,
       visit2_TAbsT = #visit2_TAbsT record,
       visit2_TAppT = new,
       visit2_TProdEx = #visit2_TProdEx record,
       visit2_TArrowTAL = #visit2_TArrowTAL record,
       visit2_var = #visit2_var record,
       visit2_bsort = #visit2_bsort record,
       visit2_idx = #visit2_idx record,
       visit2_sort = #visit2_sort record,
       visit2_ty_const = #visit2_ty_const record,
       visit2_ty_bin_op = #visit2_ty_bin_op record,
       visit2_quan = #visit2_quan record,
       visit2_ibind_anno_bsort = #visit2_ibind_anno_bsort record,
       visit2_ibind_anno_sort = #visit2_ibind_anno_sort record,
       visit2_tbind_anno = #visit2_tbind_anno record,
       extend_i = #extend_i record,
       extend_t = #extend_t record
  }

fun override_visit2_TAppI (record : ('this, 'env, 'var, 'bsort, 'idx, 'sort, 'var2, 'bsort2, 'idx2, 'sort2, 'var3, 'bsort3, 'idx3, 'sort3) ty_visitor2_vtable) new : ('this, 'env, 'var, 'bsort, 'idx, 'sort, 'var2, 'bsort2, 'idx2, 'sort2, 'var3, 'bsort3, 'idx3, 'sort3) ty_visitor2_vtable =
  {
       visit2_kind = #visit2_kind record,
       visit2_KType = #visit2_KType record,
       visit2_KArrow = #visit2_KArrow record,
       visit2_KArrowT = #visit2_KArrowT record,
       visit2_ty = #visit2_ty record,
       visit2_TVar = #visit2_TVar record,
       visit2_TConst = #visit2_TConst record,
       visit2_TBinOp = #visit2_TBinOp record,
       visit2_TArrow = #visit2_TArrow record,
       visit2_TAbsI = #visit2_TAbsI record,
       visit2_TAppI = new,
       visit2_TQuan = #visit2_TQuan record,
       visit2_TQuanI = #visit2_TQuanI record,
       visit2_TRec = #visit2_TRec record,
       visit2_TNat = #visit2_TNat record,
       visit2_TArr = #visit2_TArr record,
       visit2_TAbsT = #visit2_TAbsT record,
       visit2_TAppT = #visit2_TAppT record,
       visit2_TProdEx = #visit2_TProdEx record,
       visit2_TArrowTAL = #visit2_TArrowTAL record,
       visit2_var = #visit2_var record,
       visit2_bsort = #visit2_bsort record,
       visit2_idx = #visit2_idx record,
       visit2_sort = #visit2_sort record,
       visit2_ty_const = #visit2_ty_const record,
       visit2_ty_bin_op = #visit2_ty_bin_op record,
       visit2_quan = #visit2_quan record,
       visit2_ibind_anno_bsort = #visit2_ibind_anno_bsort record,
       visit2_ibind_anno_sort = #visit2_ibind_anno_sort record,
       visit2_tbind_anno = #visit2_tbind_anno record,
       extend_i = #extend_i record,
       extend_t = #extend_t record
  }

(***************** the default visitor2  **********************)    

open VisitorUtil
       
fun visit2_pair visit2_fst visit2_snd env (a, b) (a', b') = (visit2_fst env a a', visit2_snd env b b')
fun visit2_list visit env = map2 (visit env)
                                                  
fun visit2_abs visit2_'p env (Abs p1) (Abs p1') =
  Abs $ visit2_'p (env2ctx env) p1 p1'

fun visit2_binder extend (ctx : 'env ctx) (Binder x) (Binder x') =
  let
    val env = !(#current ctx)
    val (env, x) = extend env x
    val () = #current ctx := env
  in
    Binder x
  end
fun visit2_outer visit2_'t (ctx : 'env ctx) (Outer t1) (Outer t1') = Outer $ visit2_'t (#outer ctx) t1 t1'
fun visit2_rebind visit2_'p (ctx : 'env ctx) (Rebind p1) (Rebind p1') = Rebind $ visit2_'p {outer = !(#current ctx), current = #current ctx} p1 p1'
    
fun visit2_inner x = (visit2_rebind o visit2_outer) x
fun visit2_bind visit2_'p = visit2_abs o visit2_pair visit2_'p o visit2_inner
                                             
fun visit2_bind_simp extend = visit2_bind (visit2_binder extend)
fun visit2_bind_anno extend visit2_'anno = visit2_bind (visit2_pair (visit2_binder extend) (visit2_outer visit2_'anno))
                                                       
exception Visitor2Error of string
                             
fun error _ _ = raise Visitor2Error ""
fun error_k _ _ = raise Visitor2Error ""
    
fun eq_or_throw f b b' =
    if f b b' then b
    else raise Visitor2Error ""
               
fun visit2_eq eq a = (ignore_this_env $ eq_or_throw $ curry eq) a
               
fun default_ty_visitor2_vtable
      (cast : 'this -> ('this, 'env, 'var, 'bsort, 'idx, 'sort, 'var2, 'bsort2, 'idx2, 'sort2, 'var3, 'bsort3, 'idx3, 'sort3) ty_visitor2_interface)
      extend_i
      extend_t
      visit2_var
      visit2_bsort
      visit2_idx
      visit2_sort
    : ('this, 'env, 'var, 'bsort, 'idx, 'sort, 'var2, 'bsort2, 'idx2, 'sort2, 'var3, 'bsort3, 'idx3, 'sort3) ty_visitor2_vtable =
  let
    fun visit2_kind this env data other =
      let
        val vtable = cast this
      in
        case data of
            KType () => #visit2_KType vtable this env () other
          | KArrow data => #visit2_KArrow vtable this env data other
          | KArrowT data => #visit2_KArrowT vtable this env data other
      end
    fun visit2_KType this env () other =
        case other of
            KType () =>
            KType ()
          | _ => error_k KType other
    fun visit2_KArrow this env data other = 
      let
        val vtable = cast this
        val (b, k) = data
      in
        case other of
            KArrow (b', k') =>
            let
              val b = #visit2_bsort vtable this env b b'
              val k = #visit2_kind vtable this env k k'
            in
              KArrow (b, k)
            end
          | _ => error_k (KArrow data) other
      end
    fun visit2_KArrowT this env data other = 
      let
        val vtable = cast this
        val (k1, k2) = data
      in
        case other of
            KArrowT (k1', k2') =>
            let
              val k1 = #visit2_kind vtable this env k1 k1'
              val k2 = #visit2_kind vtable this env k2 k2'
            in
              KArrowT (k1, k2)
            end
          | _ => error_k (KArrowT data) other
      end
    fun visit_eq msg a a' = (assert_b msg (a = a'); a)
    fun visit2_ty this env data other =
      let
        val vtable = cast this
      in
        case data of
            TVar data => #visit2_TVar vtable this env data other
          | TConst data => #visit2_TConst vtable this env data other
          | TBinOp data => #visit2_TBinOp vtable this env data other
          | TArrow data => #visit2_TArrow vtable this env data other
          | TAbsI data => #visit2_TAbsI vtable this env data other
          | TAppI data => #visit2_TAppI vtable this env data other
          | TQuan data => #visit2_TQuan vtable this env data other
          | TQuanI data => #visit2_TQuanI vtable this env data other
          | TRec data => #visit2_TRec vtable this env data other
          | TNat data => #visit2_TNat vtable this env data other
          | TArr data => #visit2_TArr vtable this env data other
          | TAbsT data => #visit2_TAbsT vtable this env data other
          | TAppT data => #visit2_TAppT vtable this env data other
          | TProdEx data => #visit2_TProdEx vtable this env data other
          | TArrowTAL data => #visit2_TArrowTAL vtable this env data other
          | TArrowEVM (data as (i1, rctx, ts, i2)) =>
            (case other of
                 TArrowEVM (i1', rctx', ts', i2') =>
                 let
                   val i1 = #visit2_idx vtable this env i1 i1'
                   val () = if Rctx.numItems rctx = Rctx.numItems rctx' then ()
                            else error (TArrowEVM data) other
                   val rctx = Rctx.unionWith (fn (inl (inl t), inl (inr t')) => inr $ #visit2_ty vtable this env t t'
                                             | _ => raise Impossible "visit2_TArrowEVM") (Rctx.map (inl o inl) rctx, Rctx.map (inl o inr) rctx')
                   (* if size changes after union, there must be some mismatched keys *)
                   val () = if Rctx.numItems rctx = Rctx.numItems rctx' then ()
                            else error (TArrowEVM data) other
                   val rctx = Rctx.map (fn inr t => t
                                       | _ => error (TArrowEVM data) other) rctx
                   val ts = visit2_list (#visit2_ty vtable this) env ts ts'
                   val i2 = #visit2_idx vtable this env i2 i2'
                 in
                   TArrowEVM (i1, rctx, ts, i2)
                 end
               | _ => error (TArrowEVM data) other)
          | TiBool i =>
            (case other of
                 TiBool i' =>
                 TiBool $ #visit2_idx vtable this env i i'
               | _ => error (TiBool i) other)
          | TPreArray (t, i1, i2, b) =>
            (case other of
                 TPreArray (t', i1', i2', b') =>
                 TPreArray (#visit2_ty vtable this env t t', #visit2_idx vtable this env i1 i1', #visit2_idx vtable this env i2 i2', visit_eq "visit_TPreArray/b=b'" b b')
               | _ => error (TPreArray (t, i1, i2, b)) other)
          | TArrayPtr (t, i1, i2) =>
            (case other of
                 TArrayPtr (t', i1', i2') =>
                 TArrayPtr (#visit2_ty vtable this env t t', #visit2_idx vtable this env i1 i1', #visit2_idx vtable this env i2 i2')
               | _ => error (TArrayPtr (t, i1, i2)) other)
          | TTuplePtr (data as (ts, i, b)) =>
            (case other of
                 TTuplePtr (ts', i', b') =>
                 TTuplePtr (visit2_list (#visit2_ty vtable this) env ts ts', #visit2_idx vtable this env i i', visit2_eq op= this env b b')
               | _ => error (TTuplePtr data) other)
          | TPreTuple (ts, i, i2) =>
            (case other of
                 TPreTuple (ts', i', i2') =>
                 TPreTuple (visit2_list (#visit2_ty vtable this) env ts ts', #visit2_idx vtable this env i i', #visit2_idx vtable this env i2 i2')
               | _ => error (TPreTuple (ts, i, i2)) other)
          | TMap t =>
            (case other of
                 TMap t' =>
                 TMap (#visit2_ty vtable this env t t')
               | _ => error (TMap t) other)
          | TState x =>
            (case other of
                 TState x' =>
                 TState (visit2_eq op= this env x x')
               | _ => error (TState x) other)
          | TVectorPtr (data as (x, i)) =>
            (case other of
                 TVectorPtr (x', i') =>
                 TVectorPtr (visit2_eq op= this env x x', #visit2_idx vtable this env i i')
               | _ => error (TVectorPtr data) other)
      end
    fun visit2_TVar this env data other =
      let
        val vtable = cast this
      in
        case other of
            TVar data' =>
            TVar $ visit2_pair (#visit2_var vtable this) (visit2_list (#visit2_kind vtable this)) env data data'
          | _ => error (TVar data) other
      end
    fun visit2_TConst this env data other =
      let
        val vtable = cast this
      in
        case other of
            TConst data' =>
            TConst $ #visit2_ty_const vtable this env data data'
          | _ => error (TConst data) other
      end
    fun visit2_TBinOp this env data other = 
      let
        val vtable = cast this
        val (opr, t1, t2) = data
      in
        case other of
            TBinOp (opr', t1', t2') =>
            let
              val opr = #visit2_ty_bin_op vtable this env opr opr'
              val t1 = #visit2_ty vtable this env t1 t1'
              val t2 = #visit2_ty vtable this env t2 t2'
            in
              TBinOp (opr, t1, t2)
            end
          | _ => error (TBinOp data) other
      end
    fun visit2_TArrow this env data other = 
      let
        val vtable = cast this
        val ((i1, t1), i, (i2, t2)) = data
      in
        case other of
            TArrow ((i1', t1'), i', (i2', t2')) =>
            let
              val i1 = #visit2_idx vtable this env i1 i1'
              val t1 = #visit2_ty vtable this env t1 t1'
              val i = #visit2_idx vtable this env i i'
              val i2 = #visit2_idx vtable this env i2 i2'
              val t2 = #visit2_ty vtable this env t2 t2'
            in
              TArrow ((i1, t1), i, (i2, t2))
            end
          | _ => error (TArrow data) other
      end
    fun visit2_TAbsI this env data other =
      let
        val vtable = cast this
      in
        case other of
            TAbsI data' =>
            TAbsI $ #visit2_ibind_anno_bsort vtable this (#visit2_bsort vtable this) (#visit2_ty vtable this) env data data'
          | _ => error (TAbsI data) other
      end
    fun visit2_TAppI this env data other = 
      let
        val vtable = cast this
        val (t, i) = data
      in
        case other of
            TAppI (t', i') =>
            let
              val t = #visit2_ty vtable this env t t'
              val i = #visit2_idx vtable this env i i'
            in
              TAppI (t, i)
            end
          | _ => error (TAppI data) other
      end
    fun visit2_TQuan this env data other =
      let
        val vtable = cast this
        val (q, bind) = data
      in
        case other of
            TQuan (q', bind') =>
            let
              val q = #visit2_quan vtable this env q q'
              val bind = #visit2_tbind_anno vtable this (#visit2_kind vtable this) (#visit2_ty vtable this) env bind bind'
            in
              TQuan (q, bind)
            end
          | _ => error (TQuan data) other
      end
    fun visit2_TQuanI this env data other =
      let
        val vtable = cast this
        val (q, bind) = data
      in
        case other of
            TQuanI (q', bind') =>
            let
              val q = #visit2_quan vtable this env q q'
              val bind = #visit2_ibind_anno_sort vtable this (#visit2_sort vtable this) (#visit2_ty vtable this) env bind bind'
            in
              TQuanI (q, bind)
            end
          | _ => error (TQuanI data) other
      end
    fun visit2_TRec this env data other =
      let
        val vtable = cast this
      in
        case other of
            TRec data' =>
            TRec $ #visit2_tbind_anno vtable this (#visit2_kind vtable this) (#visit2_ty vtable this) env data data'
          | _ => error (TRec data) other
      end
    fun visit2_TNat this env data other = 
      let
        val vtable = cast this
      in
        case other of
            TNat data' =>
            TNat $ #visit2_idx vtable this env data data'
          | _ => error (TNat data) other
      end
    fun visit2_TArr this env data other = 
      let
        val vtable = cast this
        val (t, i) = data
      in
        case other of
            TArr (t', i') =>
            let
              val t = #visit2_ty vtable this env t t'
              val i = #visit2_idx vtable this env i i'
            in
              TArr (t, i)
            end
          | _ => error (TArr data) other
      end
    fun visit2_TAbsT this env data other =
      let
        val vtable = cast this
      in
        case other of
            TAbsT data' =>
            TAbsT $ #visit2_tbind_anno vtable this (#visit2_kind vtable this) (#visit2_ty vtable this) env data data'
          | _ => error (TAbsT data) other
      end
    fun visit2_TAppT this env data other = 
      let
        val vtable = cast this
        val (t1, t2) = data
      in
        case other of
            TAppT (t1', t2') =>
            let
              val t1 = #visit2_ty vtable this env t1 t1'
              val t2 = #visit2_ty vtable this env t2 t2'
            in
              TAppT (t1, t2)
            end
          | _ => error (TAppT data) other
      end
    fun visit2_TProdEx this env data other = 
      let
        val vtable = cast this
        val ((t1, b1), (t2, b2)) = data
      in
        case other of
            TProdEx ((t1', b1'), (t2', b2')) =>
            let
              val t1 = #visit2_ty vtable this env t1 t1'
              val t2 = #visit2_ty vtable this env t2 t2'
              val b1 = visit2_eq op= this env b1 b1'
              val b2 = visit2_eq op= this env b2 b2'
            in
              TProdEx ((t1, b1), (t2, b2))
            end
          | _ => error (TProdEx data) other
      end
    fun visit2_TArrowTAL this env data other = 
      let
        val vtable = cast this
        val (ts, i) = data
      in
        case other of
            TArrowTAL (ts', i') =>
            let
              val () = if Rctx.numItems ts = Rctx.numItems ts' then ()
                       else error (TArrowTAL data) other
              val ts = Rctx.unionWith (fn (inl (inl t), inl (inr t')) => inr $ #visit2_ty vtable this env t t'
                                      | _ => raise Impossible "visit2_TArrowTAL") (Rctx.map (inl o inl) ts, Rctx.map (inl o inr) ts')
              (* if size changes after union, there must be some mismatched keys *)
              val () = if Rctx.numItems ts = Rctx.numItems ts' then ()
                       else error (TArrowTAL data) other
              val ts = Rctx.map (fn inr t => t
                                | _ => error (TArrowTAL data) other) ts
              val i = #visit2_idx vtable this env i i'
            in
              TArrowTAL (ts, i)
            end
          | _ => error (TArrowTAL data) other
      end
    fun default_visit2_bind_anno extend this = visit2_bind_anno (extend this)
  in
    {visit2_kind = visit2_kind,
     visit2_KType = visit2_KType,
     visit2_KArrow = visit2_KArrow,
     visit2_KArrowT = visit2_KArrowT,
     visit2_ty = visit2_ty,
     visit2_TVar = visit2_TVar,
     visit2_TConst = visit2_TConst,
     visit2_TBinOp = visit2_TBinOp,
     visit2_TArrow = visit2_TArrow,
     visit2_TAbsI = visit2_TAbsI,
     visit2_TAppI = visit2_TAppI,
     visit2_TQuan = visit2_TQuan,
     visit2_TQuanI = visit2_TQuanI,
     visit2_TRec = visit2_TRec,
     visit2_TNat = visit2_TNat,
     visit2_TArr = visit2_TArr,
     visit2_TAbsT = visit2_TAbsT,
     visit2_TAppT = visit2_TAppT,
     visit2_TProdEx = visit2_TProdEx,
     visit2_TArrowTAL = visit2_TArrowTAL,
     visit2_var = visit2_var,
     visit2_bsort = visit2_bsort,
     visit2_idx = visit2_idx,
     visit2_sort = visit2_sort,
     visit2_ty_const = visit2_eq op=,
     visit2_ty_bin_op = visit2_eq op=,
     visit2_quan = visit2_eq op=,
     visit2_ibind_anno_bsort = default_visit2_bind_anno extend_i,
     visit2_ibind_anno_sort = default_visit2_bind_anno extend_i,
     visit2_tbind_anno = default_visit2_bind_anno extend_t,
     extend_i = extend_i,
     extend_t = extend_t
    }
  end

datatype ('env, 'var, 'bsort, 'idx, 'sort, 'var2, 'bsort2, 'idx2, 'sort2, 'var3, 'bsort3, 'idx3, 'sort3) ty_visitor2 =
         TyVisitor of (('env, 'var, 'bsort, 'idx, 'sort, 'var2, 'bsort2, 'idx2, 'sort2, 'var3, 'bsort3, 'idx3, 'sort3) ty_visitor2, 'env, 'var, 'bsort, 'idx, 'sort, 'var2, 'bsort2, 'idx2, 'sort2, 'var3, 'bsort3, 'idx3, 'sort3) ty_visitor2_interface

fun ty_visitor2_impls_interface (this : ('env, 'var, 'bsort, 'idx, 'sort, 'var2, 'bsort2, 'idx2, 'sort2, 'var3, 'bsort3, 'idx3, 'sort3) ty_visitor2) :
    (('env, 'var, 'bsort, 'idx, 'sort, 'var2, 'bsort2, 'idx2, 'sort2, 'var3, 'bsort3, 'idx3, 'sort3) ty_visitor2, 'env, 'var, 'bsort, 'idx, 'sort, 'var2, 'bsort2, 'idx2, 'sort2, 'var3, 'bsort3, 'idx3, 'sort3) ty_visitor2_interface =
  let
    val TyVisitor vtable = this
  in
    vtable
  end

fun new_ty_visitor2 vtable params =
  let
    val vtable = vtable ty_visitor2_impls_interface params
  in
    TyVisitor vtable
  end
    
(***************** the "eq_t" visitor  **********************)    
    
fun eq_t_visitor2_vtable cast (eq_var, eq_bsort, eq_i, eq_s) : ('this, unit, 'var, 'bsort, 'idx, 'sort, 'var2, 'bsort2, 'idx2, 'sort2, 'var, 'bsort, 'idx, 'sort) ty_visitor2_vtable =
  let
  in
    default_ty_visitor2_vtable
      cast
      extend_noop
      extend_noop
      (ignore_this_env $ eq_or_throw eq_var)
      (ignore_this_env $ eq_or_throw eq_bsort)
      (ignore_this_env $ eq_or_throw eq_i)
      (ignore_this_env $ eq_or_throw eq_s)
  end

fun new_eq_t_visitor2 a = new_ty_visitor2 eq_t_visitor2_vtable a
    
fun eq_t_fn params b b' =
  let
    val visitor2 as (TyVisitor vtable) = new_eq_t_visitor2 params
  in
    (#visit2_ty vtable visitor2 () b b'; true)
    handle Visitor2Error msg => false
  end

structure UnitTest = struct

fun TV x = TVar (x, [])
                
fun test1 dirname =
  let
    val () = println "MicroTiMLVisitor2.UnitTest started"
    fun eq_t a = eq_t_fn (curry op=, Equal.eq_bs, Equal.eq_i, Equal.eq_s) a
    val t1 = TBinOp (TBProd (), TV 0, TV 1)
    val t2 = TBinOp (TBProd (), TV 0, TV 2)
    val () = assert_b "" $ eq_t t1 t1
    val () = assert_b "" $ eq_t t2 t2
    val () = assert_b "" $ not $ eq_t t1 t2
    val () = println "MicroTiMLVisitor2.UnitTest passed"
  in
    ()
  end
    
val test_suites = [
  test1
]
                    
end
                       
end
