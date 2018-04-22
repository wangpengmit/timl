structure EVM1Visitor = struct

open EVM1

infixr 0 $
         
type ('this, 'env, 'idx, 'ty, 'idx2, 'ty2) evm1_visitor_vtable =
     {
       visit_word : 'this -> 'env -> 'ty word -> 'ty2 word,
       visit_inst : 'this -> 'env ctx -> ('idx, 'ty) inst -> ('idx2, 'ty2) inst,
       visit_insts : 'this -> 'env -> ('idx, 'ty) insts -> ('idx2, 'ty2) insts,
       visit_idx : 'this -> 'env -> 'idx -> 'idx2,
       visit_ty : 'this -> 'env -> 'ty -> 'ty2,
       visit_label : 'this -> 'env -> label -> label,
       extend_i : 'this -> 'env -> iname -> 'env * iname,
       extend_t : 'this -> 'env -> tname -> 'env * tname
     }
       
type ('this, 'env, 'idx, 'ty, 'idx2, 'ty2) evm1_visitor_interface =
     ('this, 'env, 'idx, 'ty, 'idx2, 'ty2) evm1_visitor_vtable
                                           
datatype ('env, 'idx, 'ty, 'idx2, 'ty2) evm1_visitor =
         EVM1Visitor of (('env, 'idx, 'ty, 'idx2, 'ty2) evm1_visitor, 'env, 'idx, 'ty, 'idx2, 'ty2) evm1_visitor_interface

fun evm1_visitor_impls_interface (this : ('env, 'idx, 'ty, 'idx2, 'ty2) evm1_visitor) :
    (('env, 'idx, 'ty, 'idx2, 'ty2) evm1_visitor, 'env, 'idx, 'ty, 'idx2, 'ty2) evm1_visitor_interface =
  let
    val EVM1Visitor vtable = this
  in
    vtable
  end

fun new_evm1_visitor vtable params =
  let
    val vtable = vtable evm1_visitor_impls_interface params
  in
    EVM1Visitor vtable
  end

(***************** overrides  **********************)    

fun override_visit_insts (record : ('this, 'env, 'idx, 'ty, 'idx2, 'ty2) evm1_visitor_vtable) new =
  {
    visit_word = #visit_word record,
    visit_inst = #visit_inst record,
    visit_insts = new,
    visit_idx = #visit_idx record,
    visit_ty = #visit_ty record,
    visit_label = #visit_label record,
    extend_i = #extend_i record,
    extend_t = #extend_t record
  }
    
fun override_visit_label (record : ('this, 'env, 'idx, 'ty, 'idx2, 'ty2) evm1_visitor_vtable) new =
  {
    visit_word = #visit_word record,
    visit_inst = #visit_inst record,
    visit_insts = #visit_insts record,
    visit_idx = #visit_idx record,
    visit_ty = #visit_ty record,
    visit_label = new,
    extend_i = #extend_i record,
    extend_t = #extend_t record
  }
    
(***************** the default visitor  **********************)    

open VisitorUtil
       
fun default_evm1_visitor_vtable
      (cast : 'this -> ('this, 'env, 'idx, 'ty, 'idx2, 'ty2) evm1_visitor_interface)
      extend_i
      extend_t
      visit_idx
      visit_ty
    : ('this, 'env, 'idx, 'ty, 'idx2, 'ty2) evm1_visitor_vtable =
  let
    fun visit_word this env data =
      let
        val vtable = cast this
        fun visit_word_const c =
          case c of
              WCLabel l => WCLabel $ #visit_label vtable this env l
            | _ => c
      in
        case data of
            WConst data => WConst $ visit_word_const data
          | WUninit t => WUninit $ #visit_ty vtable this env t
          | WBuiltin (name, t) => WBuiltin (name, #visit_ty vtable this env t)
          | WNever t => WNever $ #visit_ty vtable this env t
      end
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
    fun visit_inst this env data =
      let
        val vtable = cast this
      in
        case data of
            PUSH (n, w) => PUSH (n, visit_inner (#visit_word vtable this) env w)
          | VALUE_AppT t => VALUE_AppT $ visit_inner (#visit_ty vtable this) env t
          | VALUE_AppI i => VALUE_AppI $ visit_inner (#visit_idx vtable this) env i
          | VALUE_Pack (t, t2) => VALUE_Pack (visit_inner (#visit_ty vtable this) env t, visit_inner (#visit_ty vtable this) env t2)
          | VALUE_PackI (t, i) => VALUE_PackI (visit_inner (#visit_ty vtable this) env t, visit_inner (#visit_idx vtable this) env i)
          | VALUE_Fold t => VALUE_Fold $ visit_inner (#visit_ty vtable this) env t
          | VALUE_AscType t => VALUE_AscType $ visit_inner (#visit_ty vtable this) env t
          | UNPACK name => UNPACK $ visit_tbinder this env name
          | UNPACKI name => UNPACKI $ visit_ibinder this env name
          (* | PACK_SUM (inj, t) => PACK_SUM (inj, visit_inner (#visit_ty vtable this) env t) *)
          | ASCTIME i => ASCTIME $ visit_inner (#visit_idx vtable this) env i
          | MACRO_init_free_ptr n => MACRO_init_free_ptr n
          | MACRO_tuple_malloc ts => MACRO_tuple_malloc $ visit_inner (visit_list $ #visit_ty vtable this) env ts
          | ADD => ADD
          | MUL => MUL
          | SUB => SUB
          | DIV => DIV
          | SDIV => SDIV
          | MOD => MOD
          | LT => LT
          | GT => GT
          | SLT => SLT
          | SGT => SGT
          | EQ => EQ
          | ISZERO => ISZERO
          | AND => AND
          | OR => OR
          | BYTE => BYTE
          | POP => POP
          | MLOAD => MLOAD
          | MSTORE => MSTORE
          | MSTORE8 => MSTORE8
          | JUMPI => JUMPI
          | JUMPDEST => JUMPDEST
          | DUP a => DUP a
          | SWAP a => SWAP a
          | LOG a => LOG a
          | UNFOLD => UNFOLD
          | NAT2INT => NAT2INT
          | INT2NAT => INT2NAT
          | BYTE2INT => BYTE2INT
          (* | PRINTC => PRINTC *)
          | MARK_PreArray2ArrayPtr => MARK_PreArray2ArrayPtr
          | MARK_PreTuple2TuplePtr => MARK_PreTuple2TuplePtr
      end
    fun visit_insts this env data =
      let
        val vtable = cast this
      in
        case data of
            ISCons bind => ISCons $ visit_bind (#visit_inst vtable this) (#visit_insts vtable this) env bind
          | JUMP => JUMP
          | RETURN => RETURN
          | ISDummy a => ISDummy a
          | MACRO_halt t => MACRO_halt $ #visit_ty vtable this env t
      end
  in
    {
      visit_word = visit_word,
      visit_inst = visit_inst,
      visit_insts = visit_insts,
      visit_idx = visit_idx,
      visit_ty = visit_ty,
      visit_label = visit_noop,
      extend_i = extend_i,
      extend_t = extend_t
    }
  end

fun visit_sum visit1 visit2 env = map_inl_inr (visit1 env) (visit2 env)
fun visit_map map visit env = map (visit env)
fun visit_triple visit1 visit2 visit3 env (a, b, c) = (visit1 env a, visit2 env b, visit3 env c)
                                  
fun visit_hval (extend_i, extend_t, visit_idx, visit_sort, visit_kind, visit_ty, visit_insts) env (h : ('idx, 'sort, 'kind, 'ty) hval) : ('idx2, 'sort2, 'kind2, 'ty2) hval =
  visit_bind
    (visit_tele $ visit_sum
                (visit_pair (visit_binder extend_i) (visit_outer $ visit_sort))
                (visit_pair (visit_binder extend_t) visit_kind))
    (visit_pair (visit_triple (visit_map Rctx.map visit_ty)
                              (visit_list visit_ty)
                              visit_idx) visit_insts) env h
    
fun visit_prog (visit_label, visit_hval, visit_insts) env (H, I) =
  (visit_list (visit_pair (visit_pair visit_label return2) visit_hval) env H, visit_insts env I)

(*********** the "export" visitor: convertnig de Bruijn indices to nameful terms ***************)    

fun export_evm1_visitor_vtable cast (omitted, visit_idx, visit_ty) =
  let
    fun extend_i this (depth, (sctx, kctx)) name = ((depth, (Name2str name :: sctx, kctx)), name)
    fun extend_t this (depth, (sctx, kctx)) name = ((depth, (sctx, Name2str name :: kctx)), name)
    fun ignore_this_depth f this (depth, ctx) = f ctx
    fun only_s f this (_, (sctx, kctx)) name = f sctx name
    fun only_sk f this (_, (sctx, kctx)) name = f (sctx, kctx) name
    val vtable = 
        default_evm1_visitor_vtable
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

fun new_export_evm1_visitor params = new_evm1_visitor export_evm1_visitor_vtable params
                                                        
fun export_inst_fn params ctx e =
  let
    val visitor as (EVM1Visitor vtable) = new_export_evm1_visitor params
  in
    #visit_inst vtable visitor (env2ctx (NONE, ctx)) e
  end

fun export_insts_fn params depth ctx e =
  let
    val visitor as (EVM1Visitor vtable) = new_export_evm1_visitor params
  in
    #visit_insts vtable visitor (depth, ctx) e
  end

fun export_hval_fn visit_sort params depth h =
  let
    val visitor as (EVM1Visitor vtable) = new_export_evm1_visitor params
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

(***************** the "subst_i_insts" visitor  **********************)    

fun subst_i_evm1_visitor_vtable cast (visit_idx, visit_ty) =
  let
    fun extend_i this env name = (env + 1, name)
  in
    default_evm1_visitor_vtable
      cast
      extend_i
      extend_noop
      (ignore_this visit_idx)
      (ignore_this visit_ty)
  end

fun new_subst_i_evm1_visitor params = new_evm1_visitor subst_i_evm1_visitor_vtable params
    
fun subst_i_insts_fn params b =
  let
    val visitor as (EVM1Visitor vtable) = new_subst_i_evm1_visitor params
  in
    #visit_insts vtable visitor 0 b
  end

(***************** the "subst_t_insts" visitor  **********************)    

fun subst_t_evm1_visitor_vtable cast visit_ty =
  let
    fun extend_i this env name = (mapFst idepth_inc env, name)
    fun extend_t this env name = (mapSnd tdepth_inc env, name)
  in
    default_evm1_visitor_vtable
      cast
      extend_i
      extend_t
      visit_noop
      (ignore_this visit_ty)
  end

fun new_subst_t_evm1_visitor params = new_evm1_visitor subst_t_evm1_visitor_vtable params
    
fun subst_t_insts_fn params b =
  let
    val visitor as (EVM1Visitor vtable) = new_subst_t_evm1_visitor params
  in
    #visit_insts vtable visitor (IDepth 0, TDepth 0) b
  end

(***************** the "shift_i_insts" visitor  **********************)    
    
fun shift_i_evm1_visitor_vtable cast ((shift_i, shift_s, shift_t), n) =
  let
    fun extend_i this env name = (env + 1, name)
    fun do_shift shift this env b = shift env n b
  in
    default_evm1_visitor_vtable
      cast
      extend_i
      extend_noop
      (do_shift shift_i)
      (do_shift shift_t)
  end

fun new_shift_i_evm1_visitor params = new_evm1_visitor shift_i_evm1_visitor_vtable params
    
fun shift_i_insts_fn shifts x n b =
  let
    val visitor as (EVM1Visitor vtable) = new_shift_i_evm1_visitor (shifts, n)
  in
    #visit_insts vtable visitor x b
  end
    
(***************** the "shift_t_insts" visitor  **********************)    
    
fun shift_t_evm1_visitor_vtable cast (shift_t, n) =
  let
    fun extend_t this env name = (env + 1, name)
    fun do_shift shift this env b = shift env n b
  in
    default_evm1_visitor_vtable
      cast
      extend_noop
      extend_t
      visit_noop
      (do_shift shift_t)
  end

fun new_shift_t_evm1_visitor params = new_evm1_visitor shift_t_evm1_visitor_vtable params
    
fun shift_t_insts_fn shift_t x n b =
  let
    val visitor as (EVM1Visitor vtable) = new_shift_t_evm1_visitor (shift_t, n)
  in
    #visit_insts vtable visitor x b
  end
    
end
