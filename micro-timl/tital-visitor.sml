structure TiTALVisitor = struct

open TiTAL

infixr 0 $
         
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
       visit_IBinOp : 'this -> 'env ctx -> inst_bin_op * reg * reg * ('idx, 'ty) value inner -> ('idx2, 'ty2) inst,
       visit_IUnOp : 'this -> 'env ctx -> inst_un_op * reg * ('idx, 'ty) value inner -> ('idx2, 'ty2) inst,
       visit_IMallocPair : 'this -> 'env ctx -> reg * (('idx, 'ty) value inner * ('idx, 'ty) value inner) -> ('idx2, 'ty2) inst,
       visit_ILd : 'this -> 'env ctx -> reg * (reg * projector) -> ('idx2, 'ty2) inst,
       visit_ISt : 'this -> 'env ctx -> (reg * projector) * reg -> ('idx2, 'ty2) inst,
       visit_IUnpack : 'this -> 'env ctx -> tbinder * reg * ('idx, 'ty) value outer -> ('idx2, 'ty2) inst,
       visit_IUnpackI : 'this -> 'env ctx -> ibinder * reg * ('idx, 'ty) value outer -> ('idx2, 'ty2) inst,
       visit_IInj : 'this -> 'env ctx -> reg * injector * ('idx, 'ty) value inner * 'ty inner -> ('idx2, 'ty2) inst,
       visit_IAscTime : 'this -> 'env ctx -> 'idx inner -> ('idx2, 'ty2) inst,
       visit_ISCons : 'this -> 'env -> (('idx, 'ty) inst, ('idx, 'ty) insts) bind -> ('idx2, 'ty2) insts,
       visit_ISJmp : 'this -> 'env -> ('idx, 'ty) value -> ('idx2, 'ty2) insts,
       visit_ISHalt : 'this -> 'env -> 'ty -> ('idx2, 'ty2) insts,
       visit_word : 'this -> 'env -> 'ty word -> 'ty2 word,
       visit_value : 'this -> 'env -> ('idx, 'ty) value -> ('idx2, 'ty2) value,
       visit_inst : 'this -> 'env ctx -> ('idx, 'ty) inst -> ('idx2, 'ty2) inst,
       visit_insts : 'this -> 'env -> ('idx, 'ty) insts -> ('idx2, 'ty2) insts,
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

(***************** overrides  **********************)    

fun override_visit_insts (record : ('this, 'env, 'idx, 'ty, 'idx2, 'ty2) tital_visitor_vtable) new =
  {
    visit_WLabel = #visit_WLabel record,
    visit_WConst = #visit_WConst record,
    visit_WUninit = #visit_WUninit record,
    visit_WBuiltin = #visit_WBuiltin record,
    visit_WNever = #visit_WNever record,
    visit_VReg = #visit_VReg record,
    visit_VWord = #visit_VWord record,
    visit_VAppT = #visit_VAppT record,
    visit_VAppI = #visit_VAppI record,
    visit_VPack = #visit_VPack record,
    visit_VPackI = #visit_VPackI record,
    visit_VFold = #visit_VFold record,
    visit_IBinOp = #visit_IBinOp record,
    visit_IUnOp = #visit_IUnOp record,
    visit_IMallocPair = #visit_IMallocPair record,
    visit_ILd = #visit_ILd record,
    visit_ISt = #visit_ISt record,
    visit_IUnpack = #visit_IUnpack record,
    visit_IUnpackI = #visit_IUnpackI record,
    visit_IInj = #visit_IInj record,
    visit_IAscTime = #visit_IAscTime record,
    visit_ISCons = #visit_ISCons record,
    visit_ISJmp = #visit_ISJmp record,
    visit_ISHalt = #visit_ISHalt record,
    visit_word = #visit_word record,
    visit_value = #visit_value record,
    visit_inst = #visit_inst record,
    visit_insts = new,
    visit_idx = #visit_idx record,
    visit_ty = #visit_ty record,
    extend_i = #extend_i record,
    extend_t = #extend_t record
  }
    
    
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
    fun visit_inst this env data =
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
    fun visit_ibinder this env name =
      let
        val vtable = cast this
        val name = visit_binder (#extend_i vtable this) env name
      in
        name
      end
    fun visit_tbinder this env name =
      let
        val vtable = cast this
        val name = visit_binder (#extend_t vtable this) env name
      in
        name
      end
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
    fun visit_IInj this env (r, inj, v, t) = 
      let
        val vtable = cast this
        val v = visit_inner (#visit_value vtable this) env v
        val t = visit_inner (#visit_ty vtable this) env t
      in
        IInj (r, inj, v, t)
      end
    fun visit_IAscTime this env i = 
      let
        val vtable = cast this
        val i = visit_inner (#visit_idx vtable this) env i
      in
        IAscTime i
      end
    fun visit_insts this env data =
      let
        val vtable = cast this
      in
        case data of
            ISCons data => #visit_ISCons vtable this env data
          | ISJmp data => #visit_ISJmp vtable this env data
          | ISHalt data => #visit_ISHalt vtable this env data
          | ISDummy data => ISDummy data
      end
    fun visit_ISCons this env bind = 
      let
        val vtable = cast this
        val bind = visit_bind (#visit_inst vtable this) (#visit_insts vtable this) env bind
      in
        ISCons bind
      end
    fun visit_ISJmp this env v = 
      let
        val vtable = cast this
        val v = #visit_value vtable this env v
      in
        ISJmp v
      end
    fun visit_ISHalt this env t = 
      let
        val vtable = cast this
        val t = #visit_ty vtable this env t
      in
        ISHalt t
      end
  in
    {
      visit_WLabel = visit_WLabel,
      visit_WConst = visit_WConst,
      visit_WUninit = visit_WUninit,
      visit_WBuiltin = visit_WBuiltin,
      visit_WNever = visit_WNever,
      visit_VReg = visit_VReg,
      visit_VWord = visit_VWord,
      visit_VAppT = visit_VAppT,
      visit_VAppI = visit_VAppI,
      visit_VPack = visit_VPack,
      visit_VPackI = visit_VPackI,
      visit_VFold = visit_VFold,
      visit_IBinOp = visit_IBinOp,
      visit_IUnOp = visit_IUnOp,
      visit_IMallocPair = visit_IMallocPair,
      visit_ILd = visit_ILd,
      visit_ISt = visit_ISt,
      visit_IUnpack = visit_IUnpack,
      visit_IUnpackI = visit_IUnpackI,
      visit_IInj = visit_IInj,
      visit_IAscTime = visit_IAscTime,
      visit_ISCons = visit_ISCons,
      visit_ISJmp = visit_ISJmp,
      visit_ISHalt = visit_ISHalt,
      visit_word = visit_word,
      visit_value = visit_value,
      visit_inst = visit_inst,
      visit_insts = visit_insts,
      visit_idx = visit_idx,
      visit_ty = visit_ty,
      extend_i = extend_i,
      extend_t = extend_t
    }
  end

fun visit_sum visit1 visit2 env = map_inl_inr (visit1 env) (visit2 env)
fun visit_map map visit env = map (visit env)
                                  
fun visit_hval (extend_i, extend_t, visit_idx, visit_sort, visit_kind, visit_ty, visit_insts) env (h : ('idx, 'sort, 'kind, 'ty) hval) : ('idx2, 'sort2, 'kind2, 'ty2) hval =
  visit_bind
    (visit_tele $ visit_sum
                (visit_pair (visit_binder extend_i) (visit_outer $ visit_sort))
                (visit_pair (visit_binder extend_t) visit_kind))
    (visit_pair (visit_pair (visit_map Rctx.map visit_ty) visit_idx) visit_insts) env h
    
(*********** the "export" visitor: convertnig de Bruijn indices to nameful terms ***************)    

fun export_tital_visitor_vtable cast (omitted, visit_idx, visit_ty) =
  let
    fun extend_i this (depth, (sctx, kctx)) name = (depth, (Name2str name :: sctx, kctx))
    fun extend_t this (depth, (sctx, kctx)) name = (depth, (sctx, Name2str name :: kctx))
    fun ignore_this_depth f this (depth, ctx) = f ctx
    fun only_s f this (_, (sctx, kctx)) name = f sctx name
    fun only_sk f this (_, (sctx, kctx)) name = f (sctx, kctx) name
    val vtable = 
        default_tital_visitor_vtable
          cast
          extend_i
          extend_t
          (only_s visit_idx)
          (only_sk visit_ty)
    fun visit_insts this (depth, ctx) t = 
      let
        val (reached_depth_limit, depth) =
            case depth of
                NONE => (false, NONE)
              | SOME n => if n <= 0 then
                            (true, NONE)
                          else
                            (false, SOME (n-1))
      in
        if reached_depth_limit then omitted
        else
          (* call super *)
          #visit_insts vtable this (depth, ctx) t
      end
    val vtable = override_visit_insts vtable visit_insts
  in
    vtable
  end

fun new_export_tital_visitor params = new_tital_visitor export_tital_visitor_vtable params
                                                        
fun export_insts_fn params depth ctx e =
  let
    val visitor as (TiTALVisitor vtable) = new_export_tital_visitor params
  in
    #visit_insts vtable visitor (depth, ctx) e
  end

fun export_hval_fn visit_sort params depth h =
  let
    val visitor as (TiTALVisitor vtable) = new_export_tital_visitor params
    fun only_s f (_, (sctx, kctx)) name = f sctx name
  in
    visit_hval (#extend_i vtable visitor,
                #extend_t vtable visitor,
                #visit_idx vtable visitor,
                (only_s visit_sort),
                return2,
                #visit_ty vtable visitor,
                #visit_insts vtable visitor
               ) (depth, ([], [])) h
  end

end
