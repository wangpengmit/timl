structure TiTALVisitor = struct

open TiTAL

type ('this, 'env, 'idx, 'ty, 'idx2, 'ty2) tital_visitor_vtable =
     {
       visit_WLabel : 'this -> 'env -> label -> 'ty2 word,
       visit_WConst : 'this -> 'env -> Operators.expr_const -> 'ty2 word,
       visit_WUninit : 'this -> 'env -> 'ty -> 'ty2 word,
       visit_WBuiltin : 'this -> 'env -> 'ty -> 'ty2 word,
       visit_WNever : 'this -> 'env -> 'ty -> 'ty2 word,
       visit_VReg : 'this -> 'env -> reg -> ('idx2, 'ty2) value,
       visit_VWord : 'this -> 'env -> 'ty word -> ('idx2, 'ty2) value,
       visit_VAppT : 'this -> 'env -> ('idx, 'ty) value * 'ty -> ('idx2, 'ty2) value,
       visit_VAppI : 'this -> 'env -> ('idx, 'ty) value * 'idx -> ('idx2, 'ty2) value,
       visit_VPack : 'this -> 'env -> 'ty * 'ty * ('idx, 'ty) value -> ('idx2, 'ty2) value,
       visit_VPackI : 'this -> 'env -> 'ty * 'idx * ('idx, 'ty) value -> ('idx2, 'ty2) value,
       visit_VFold : 'this -> 'env -> 'ty * ('idx, 'ty) value -> ('idx2, 'ty2) value,
       visit_IBinOp : 'this -> 'env -> inst_bin_op * reg * reg * ('idx, 'ty) value inner -> ('idx2, 'ty2) inst,
       visit_IUnOp : 'this -> 'env -> inst_un_op * reg * ('idx, 'ty) value inner -> ('idx2, 'ty2) inst,
       visit_IMallocPair : 'this -> 'env -> reg * (('idx, 'ty) value inner * ('idx, 'ty) value inner) -> ('idx2, 'ty2) inst,
       visit_ILd : 'this -> 'env -> reg * (reg * projector) -> ('idx2, 'ty2) inst,
       visit_ISt : 'this -> 'env -> (reg * projector) * reg -> ('idx2, 'ty2) inst,
       visit_IUnpack : 'this -> 'env -> tbinder * reg * ('idx, 'ty) value outer -> ('idx2, 'ty2) inst,
       visit_IUnpackI : 'this -> 'env -> ibinder * reg * ('idx, 'ty) value outer -> ('idx2, 'ty2) inst,
       visit_IInj : 'this -> 'env -> reg * injector * ('idx, 'ty) value inner -> ('idx2, 'ty2) inst,
       visit_IAscTime : 'this -> 'env -> 'idx inner -> ('idx2, 'ty2) inst,
       visit_ISCons : 'this -> 'env -> (('idx, 'ty) inst, ('idx, 'ty) insts) bind -> ('idx2, 'ty2) insts,
       visit_ISJmp : 'this -> 'env -> ('idx, 'ty) value -> ('idx2, 'ty2) insts,
       visit_ISHalt : 'this -> 'env -> 'ty -> ('idx2, 'ty2) insts,
       visit_idx : 'this -> 'env -> 'idx -> 'idx2,
       visit_ty : 'this -> 'env -> 'ty -> 'ty2,
       extend_i : 'this -> 'env -> iname -> 'env,
       extend_t : 'this -> 'env -> tname -> 'env
     }
       
type ('this, 'env, 'idx, 'ty, 'idx2, 'ty2) tital_visitor_interface =
     ('this, 'env, 'idx, 'ty, 'idx2, 'ty2) tital_visitor_vtable
                                           
datatype ('env, 'idx, 'ty, 'idx2, 'ty2) tital_visitor =
         TiTALVisitor of (('env, 'idx, 'ty, 'idx2, 'ty2) tital_visitor, 'env, 'idx, 'ty, 'idx2, 'ty2) tital_visitor_interface

fun tital_visitor_impls_interface (this : ('env, 'idx, 'ty, 'idx2, 'ty2) tital_visitor) :
    (('env, 'idx, 'ty, 'idx2, 'ty2) tital_visitor, 'env, 'idx, 'ty, 'idx2, 'ty2) tital_visitor_interface =
  let
    val TiTALVisitor vtable = this
  in
    vtable
  end

fun new_tital_visitor vtable params =
  let
    val vtable = vtable tital_visitor_impls_interface params
  in
    TiTALVisitor vtable
  end

(***************** the default visitor  **********************)    

open VisitorUtil
       
fun default_tital_visitor_vtable
      (cast : 'this -> ('this, 'env, 'idx, 'ty, 'idx2, 'ty2) tital_visitor_interface)
      extend_i
      extend_t
      visit_idx
      visit_ty
    : ('this, 'env, 'idx, 'ty, 'idx2, 'ty2) tital_visitor_vtable =
  let
    fun visit_word this env data =
      let
        val vtable = cast this
      in
        case data of
            WLabel data => #visit_WLabel vtable this env data
          | WConst data => #visit_WConst vtable this env data
          | WUninit data => #visit_WUninit vtable this env data
          | WBuiltin data => #visit_WBuiltin vtable this env data
          | WNever data => #visit_WNever vtable this env data
      end
    fun visit_WLabel this env data = WLabel data
    fun visit_WConst this env data = WConst data
    fun visit_WUninit this env t = 
      let
        val vtable = cast this
        val t = #visit_ty vtable this env t
      in
        WUninit t
      end
    fun visit_WBuiltin this env t = 
      let
        val vtable = cast this
        val t = #visit_ty vtable this env t
      in
        WBuiltin t
      end
    fun visit_WNever this env t = 
      let
        val vtable = cast this
        val t = #visit_ty vtable this env t
      in
        WNever t
      end
    fun visit_value this env data =
      let
        val vtable = cast this
      in
        case data of
            VReg data => #visit_VReg vtable this env data
          | VWord data => #visit_VWord vtable this env data
          | VAppT data => #visit_VAppT vtable this env data
          | VAppI data => #visit_VAppI vtable this env data
          | VPack data => #visit_VPack vtable this env data
          | VPackI data => #visit_VPackI vtable this env data
          | VFold data => #visit_VFold vtable this env data
      end
    fun visit_VReg this env data = VReg data
    fun visit_VWord this env w = 
      let
        val vtable = cast this
        val w = #visit_word vtable this env w
      in
        VWord w
      end
    fun visit_VAppT this env (v, t) = 
      let
        val vtable = cast this
        val v = #visit_value vtable this env v
        val t = #visit_ty vtable this env t
      in
        VAppT (v, t)
      end
    fun visit_VAppI this env (v, i) = 
      let
        val vtable = cast this
        val v = #visit_value vtable this env v
        val i = #visit_idx vtable this env i
      in
        VAppI (v, i)
      end
    fun visit_VPack this env (t, t', v) = 
      let
        val vtable = cast this
        val t = #visit_ty vtable this env t
        val t' = #visit_ty vtable this env t'
        val v = #visit_value vtable this env v
      in
        VPack (t, t', v)
      end
    fun visit_VPackI this env (t, i, v) = 
      let
        val vtable = cast this
        val t = #visit_ty vtable this env t
        val i = #visit_idx vtable this env i
        val v = #visit_value vtable this env v
      in
        VPackI (t, i, v)
      end
    fun visit_VFold this env (t, v) = 
      let
        val vtable = cast this
        val t = #visit_ty vtable this env t
        val v = #visit_value vtable this env v
      in
        VFold (t, v)
      end
    fun visit_value this env data =
      let
        val vtable = cast this
      in
        case data of
            IBinOp data => #visit_IBinOp vtable this env data
          | IUnOp data => #visit_IUnOp vtable this env data
          | IMallocPair data => #visit_IMallocPair vtable this env data
          | ILd data => #visit_ILd vtable this env data
          | ISt data => #visit_ISt vtable this env data
          | IUnpack data => #visit_IUnpack vtable this env data
          | IUnpackI data => #visit_IUnpackI vtable this env data
          | IInj data => #visit_IInj vtable this env data
          | IAscTime data => #visit_IAscTime vtable this env data
      end
    fun visit_IUnOp this env (opr, r, v) = 
      let
        val vtable = cast this
        val v = visit_inner (#visit_value vtable this) env v
      in
        IUnOp (opr, r, v)
      end
    fun visit_IBinOp this env (opr, r, r', v) = 
      let
        val vtable = cast this
        val v = visit_inner (#visit_value vtable this) env v
      in
        IBinOp (opr, r, r', v)
      end
    fun visit_IMallocPair this env (r, (v, v')) = 
      let
        val vtable = cast this
        val v = visit_inner (#visit_value vtable this) env v
        val v' = visit_inner (#visit_value vtable this) env v'
      in
        IMallocPair (r, (v, v'))
      end
    fun visit_ILd this env data = ILd data
    fun visit_ISt this env data = ISt data
    fun visit_IUnpack this env (name, r, v) = 
      let
        val vtable = cast this
        val name = visit_tbinder this env name
        val v = visit_outer (#visit_value vtable this) env v
      in
        IUnpack (name, r, v)
      end
    fun visit_IUnpackI this env (name, r, v) = 
      let
        val vtable = cast this
        val name = visit_ibinder this env name
        val v = visit_outer (#visit_value vtable this) env v
      in
        IUnpackI (name, r, v)
      end
    fun visit_IInj this env (r, inj, v) = 
      let
        val vtable = cast this
        val v = visit_inner (#visit_value vtable this) env v
      in
        IInj (r, inj, v)
      end
    fun visit_IAscTime this env i = 
      let
        val vtable = cast this
        val i = visit_inner (#visit_idx vtable this) env i
      in
        IAscTime i
      end



        
    fun visit_un_op this env opr = 
      let
        val vtable = cast this
        fun on_t x = #visit_ty vtable this env x
      in
        case opr of
            EUProj opr => EUProj opr
          | EUInj (opr, t) => EUInj (opr, on_t t)
          | EUFold t => EUFold $ on_t t
          | EUUnfold => EUUnfold
      end
    fun visit_EUnOp this env data = 
      let
        val vtable = cast this
        val (opr, e) = data
        val opr = visit_un_op this env opr
        val e = #visit_expr vtable this env e
      in
        EUnOp (opr, e)
      end
    fun visit_EBinOp this env data = 
      let
        val vtable = cast this
        val (opr, e1, e2) = data
        val e1 = #visit_expr vtable this env e1
        val e2 = #visit_expr vtable this env e2
      in
        EBinOp (opr, e1, e2)
      end
    fun visit_EWrite this env data = 
      let
        val vtable = cast this
        val (e1, e2, e3) = data
        val e1 = #visit_expr vtable this env e1
        val e2 = #visit_expr vtable this env e2
        val e3 = #visit_expr vtable this env e3
      in
        EWrite (e1, e2, e3)
      end
    fun visit_ibind this = visit_bind_simp (#extend_i (cast this) this)
    fun visit_tbind this = visit_bind_simp (#extend_t (cast this) this)
    fun visit_ebind this = visit_bind_simp (#extend_e (cast this) this)
    fun visit_ibind_anno this = visit_bind_anno (#extend_i (cast this) this)
    fun visit_tbind_anno this = visit_bind_anno (#extend_t (cast this) this)
    fun visit_ebind_anno this = visit_bind_anno (#extend_e (cast this) this)
    fun visit_ECase this env data =
      let
        val vtable = cast this
        val (e, e1, e2) = data
        val e = #visit_expr vtable this env e
        val e1 = visit_ebind this (#visit_expr vtable this) env e1
        val e2 = visit_ebind this (#visit_expr vtable this) env e2
      in
        ECase (e, e1, e2)
      end
    fun visit_EAbs this env data =
      let
        val vtable = cast this
        val data = visit_ebind_anno this (#visit_ty vtable this) (#visit_expr vtable this) env data
      in
        EAbs data
      end
    fun visit_ERec this env data =
      let
        val vtable = cast this
        val data = visit_ebind_anno this (#visit_ty vtable this) (#visit_expr vtable this) env data
      in
        ERec data
      end
    fun visit_EAbsT this env data =
      let
        val vtable = cast this
        val data = visit_tbind_anno this (#visit_kind vtable this) (#visit_expr vtable this) env data
      in
        EAbsT data
      end
    fun visit_EAppT this env data = 
      let
        val vtable = cast this
        val (e, t) = data
        val e = #visit_expr vtable this env e
        val t = #visit_ty vtable this env t
      in
        EAppT (e, t)
      end
    fun visit_EAbsI this env data =
      let
        val vtable = cast this
        val data = visit_ibind_anno this (#visit_sort vtable this) (#visit_expr vtable this) env data
      in
        EAbsI data
      end
    fun visit_EAppI this env data = 
      let
        val vtable = cast this
        val (e, i) = data
        val e = #visit_expr vtable this env e
        val i = #visit_idx vtable this env i
      in
        EAppI (e, i)
      end
    fun visit_EPack this env data = 
      let
        val vtable = cast this
        val (t_all, t, e) = data
        val t_all = #visit_ty vtable this env t_all
        val t = #visit_ty vtable this env t
        val e = #visit_expr vtable this env e
      in
        EPack (t_all, t, e)
      end
    fun visit_EUnpack this env data =
      let
        val vtable = cast this
        val (e, bind) = data
        val e = #visit_expr vtable this env e
        val bind = (visit_tbind this o visit_ebind this) (#visit_expr vtable this) env bind
      in
        EUnpack (e, bind)
      end
    fun visit_EPackI this env data = 
      let
        val vtable = cast this
        val (t, i, e) = data
        val t = #visit_ty vtable this env t
        val i = #visit_idx vtable this env i
        val e = #visit_expr vtable this env e
      in
        EPackI (t, i, e)
      end
    fun visit_EUnpackI this env data =
      let
        val vtable = cast this
        val (e, bind) = data
        val e = #visit_expr vtable this env e
        val bind = (visit_ibind this o visit_ebind this) (#visit_expr vtable this) env bind
      in
        EUnpackI (e, bind)
      end
    fun visit_EAscTime this env data = 
      let
        val vtable = cast this
        val (e, i) = data
        val e = #visit_expr vtable this env e
        val i = #visit_idx vtable this env i
      in
        EAscTime (e, i)
      end
    fun visit_EAscType this env data = 
      let
        val vtable = cast this
        val (e, t) = data
        val e = #visit_expr vtable this env e
        val t = #visit_ty vtable this env t
      in
        EAscType (e, t)
      end
    fun visit_ENever this env data = 
      let
        val vtable = cast this
        val data = #visit_ty vtable this env data
      in
        ENever data
      end
    fun visit_ELet this env data =
      let
        val vtable = cast this
        val (e, bind) = data
        val e = #visit_expr vtable this env e
        val bind = visit_ebind this (#visit_expr vtable this) env bind
      in
        ELet (e, bind)
      end
  in
    {
      visit_expr = visit_expr,
      visit_EVar = visit_EVar,
      visit_EConst = visit_EConst,
      (* visit_ELoc = visit_ELoc, *)
      visit_EUnOp = visit_EUnOp,
      visit_EBinOp = visit_EBinOp,
      visit_EWrite = visit_EWrite,
      visit_ECase = visit_ECase,
      visit_EAbs = visit_EAbs,
      visit_ERec = visit_ERec,
      visit_EAbsT = visit_EAbsT,
      visit_EAppT = visit_EAppT,
      visit_EAbsI = visit_EAbsI,
      visit_EAppI = visit_EAppI,
      visit_EPack = visit_EPack,
      visit_EUnpack = visit_EUnpack,
      visit_EPackI = visit_EPackI,
      visit_EUnpackI = visit_EUnpackI,
      visit_EAscTime = visit_EAscTime,
      visit_EAscType = visit_EAscType,
      visit_ENever = visit_ENever,
      visit_ELet = visit_ELet,
      visit_var = visit_var,
      visit_idx = visit_idx,
      visit_sort = visit_sort,
      visit_kind = visit_noop,
      visit_ty = visit_ty,
      extend_i = extend_i,
      extend_t = extend_t,
      extend_e = extend_e
    }
  end

end
