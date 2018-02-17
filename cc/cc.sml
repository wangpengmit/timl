(* Closure Conversion *)

structure CC = struct

open Util
       
infixr 0 $
         
fun eq_fst ((x, _), (x', _)) = x = x'
                                     
fun free_vars_with_anno_0 f b =
  let
    val r = ref []
    fun output item = push_ref r item
    val _ = f output b
  in
    dedup eq_fst $ !r
  end

open Expr
open CompilerUtil
open MicroTiMLVisitor
open MicroTiMLExLongId
open MicroTiMLExLocallyNameless
open MicroTiMLExUtil
open MicroTiMLEx
       
fun override_visit_EAscType (record : ('this, 'env, 'var, 'idx, 'sort, 'kind, 'ty, 'var2, 'idx2, 'sort2, 'kind2, 'ty2) expr_visitor_vtable) new : ('this, 'env, 'var, 'idx, 'sort, 'kind, 'ty, 'var2, 'idx2, 'sort2, 'kind2, 'ty2) expr_visitor_vtable =
  {
    visit_expr = #visit_expr record,
    visit_EVar = #visit_EVar record,
    visit_EConst = #visit_EConst record,
    (* visit_ELoc = #visit_ELoc record, *)
    visit_EUnOp = #visit_EUnOp record,
    visit_EBinOp = #visit_EBinOp record,
    visit_EWrite = #visit_EWrite record,
    visit_ECase = #visit_ECase record,
    visit_EAbs = #visit_EAbs record,
    visit_ERec = #visit_ERec record,
    visit_EAbsT = #visit_EAbsT record,
    visit_EAppT = #visit_EAppT record,
    visit_EAbsI = #visit_EAbsI record,
    visit_EAppI = #visit_EAppI record,
    visit_EPack = #visit_EPack record,
    visit_EUnpack = #visit_EUnpack record,
    visit_EPackI = #visit_EPackI record,
    visit_EPackIs = #visit_EPackIs record,
    visit_EUnpackI = #visit_EUnpackI record,
    visit_EAscTime = #visit_EAscTime record,
    visit_EAscType = new,
    visit_ENever = #visit_ENever record,
    visit_EBuiltin = #visit_EBuiltin record,
    visit_ELet = #visit_ELet record,
    visit_ELetConstr = #visit_ELetConstr record,
    visit_EAbsConstr = #visit_EAbsConstr record,
    visit_EAppConstr = #visit_EAppConstr record,
    visit_EVarConstr = #visit_EVarConstr record,
    visit_ELetType = #visit_ELetType record,
    visit_ELetIdx = #visit_ELetIdx record,
    visit_EMatchSum = #visit_EMatchSum record,
    visit_EMatchPair = #visit_EMatchPair record,
    visit_EMatchUnfold = #visit_EMatchUnfold record,
    visit_var = #visit_var record,
    visit_cvar = #visit_cvar record,
    visit_idx = #visit_idx record,
    visit_sort = #visit_sort record,
    visit_kind = #visit_kind record,
    visit_ty = #visit_ty record,
    extend_i = #extend_i record,
    extend_t = #extend_t record,
    extend_c = #extend_c record,
    extend_e = #extend_e record
  }

fun override_visit_ERec (record : ('this, 'env, 'var, 'idx, 'sort, 'kind, 'ty, 'var2, 'idx2, 'sort2, 'kind2, 'ty2) expr_visitor_vtable) new : ('this, 'env, 'var, 'idx, 'sort, 'kind, 'ty, 'var2, 'idx2, 'sort2, 'kind2, 'ty2) expr_visitor_vtable =
  {
    visit_expr = #visit_expr record,
    visit_EVar = #visit_EVar record,
    visit_EConst = #visit_EConst record,
    (* visit_ELoc = #visit_ELoc record, *)
    visit_EUnOp = #visit_EUnOp record,
    visit_EBinOp = #visit_EBinOp record,
    visit_EWrite = #visit_EWrite record,
    visit_ECase = #visit_ECase record,
    visit_EAbs = #visit_EAbs record,
    visit_ERec = new,
    visit_EAbsT = #visit_EAbsT record,
    visit_EAppT = #visit_EAppT record,
    visit_EAbsI = #visit_EAbsI record,
    visit_EAppI = #visit_EAppI record,
    visit_EPack = #visit_EPack record,
    visit_EUnpack = #visit_EUnpack record,
    visit_EPackI = #visit_EPackI record,
    visit_EPackIs = #visit_EPackIs record,
    visit_EUnpackI = #visit_EUnpackI record,
    visit_EAscTime = #visit_EAscTime record,
    visit_EAscType = #visit_EAscType record,
    visit_ENever = #visit_ENever record,
    visit_EBuiltin = #visit_EBuiltin record,
    visit_ELet = #visit_ELet record,
    visit_ELetConstr = #visit_ELetConstr record,
    visit_EAbsConstr = #visit_EAbsConstr record,
    visit_EAppConstr = #visit_EAppConstr record,
    visit_EVarConstr = #visit_EVarConstr record,
    visit_ELetType = #visit_ELetType record,
    visit_ELetIdx = #visit_ELetIdx record,
    visit_EMatchSum = #visit_EMatchSum record,
    visit_EMatchPair = #visit_EMatchPair record,
    visit_EMatchUnfold = #visit_EMatchUnfold record,
    visit_var = #visit_var record,
    visit_cvar = #visit_cvar record,
    visit_idx = #visit_idx record,
    visit_sort = #visit_sort record,
    visit_kind = #visit_kind record,
    visit_ty = #visit_ty record,
    extend_i = #extend_i record,
    extend_t = #extend_t record,
    extend_c = #extend_c record,
    extend_e = #extend_e record
  }

fun override_visit_EAbs (record : ('this, 'env, 'var, 'idx, 'sort, 'kind, 'ty, 'var2, 'idx2, 'sort2, 'kind2, 'ty2) expr_visitor_vtable) new : ('this, 'env, 'var, 'idx, 'sort, 'kind, 'ty, 'var2, 'idx2, 'sort2, 'kind2, 'ty2) expr_visitor_vtable =
  {
    visit_expr = #visit_expr record,
    visit_EVar = #visit_EVar record,
    visit_EConst = #visit_EConst record,
    (* visit_ELoc = #visit_ELoc record, *)
    visit_EUnOp = #visit_EUnOp record,
    visit_EBinOp = #visit_EBinOp record,
    visit_EWrite = #visit_EWrite record,
    visit_ECase = #visit_ECase record,
    visit_EAbs = new,
    visit_ERec = #visit_ERec record,
    visit_EAbsT = #visit_EAbsT record,
    visit_EAppT = #visit_EAppT record,
    visit_EAbsI = #visit_EAbsI record,
    visit_EAppI = #visit_EAppI record,
    visit_EPack = #visit_EPack record,
    visit_EUnpack = #visit_EUnpack record,
    visit_EPackI = #visit_EPackI record,
    visit_EPackIs = #visit_EPackIs record,
    visit_EUnpackI = #visit_EUnpackI record,
    visit_EAscTime = #visit_EAscTime record,
    visit_EAscType = #visit_EAscType record,
    visit_ENever = #visit_ENever record,
    visit_EBuiltin = #visit_EBuiltin record,
    visit_ELet = #visit_ELet record,
    visit_ELetConstr = #visit_ELetConstr record,
    visit_EAbsConstr = #visit_EAbsConstr record,
    visit_EAppConstr = #visit_EAppConstr record,
    visit_EVarConstr = #visit_EVarConstr record,
    visit_ELetType = #visit_ELetType record,
    visit_ELetIdx = #visit_ELetIdx record,
    visit_EMatchSum = #visit_EMatchSum record,
    visit_EMatchPair = #visit_EMatchPair record,
    visit_EMatchUnfold = #visit_EMatchUnfold record,
    visit_var = #visit_var record,
    visit_cvar = #visit_cvar record,
    visit_idx = #visit_idx record,
    visit_sort = #visit_sort record,
    visit_kind = #visit_kind record,
    visit_ty = #visit_ty record,
    extend_i = #extend_i record,
    extend_t = #extend_t record,
    extend_c = #extend_c record,
    extend_e = #extend_e record
  }

fun free_ivars_with_anno_idx_visitor_vtable cast output =
  let
    fun visit_VarI this env (data as (var, sorts)) =
        case var of
            QID (_, (x, _)) =>
            (case sorts of
                 s :: _ => (output (Free_i x, s); VarI data)
               | [] => raise Impossible "free_ivars_with_anno_i/VarI/QID/ks=[]"
            )
          | _ => VarI data
    val vtable = 
        default_idx_visitor_vtable
          cast
          extend_noop
          (visit_imposs "free_ivars_with_anno_i/visit_var")
          visit_noop
          visit_noop
          visit_noop
          visit_noop
    val vtable = override_visit_VarI vtable visit_VarI
  in
    vtable
  end

fun new_free_ivars_with_anno_idx_visitor a = new_idx_visitor free_ivars_with_anno_idx_visitor_vtable a
    
fun free_ivars_with_anno_i_fn output b =
  let
    val visitor as (IdxVisitor vtable) = new_free_ivars_with_anno_idx_visitor output
  in
    #visit_idx vtable visitor () b
  end
    
fun free_ivars_with_anno_s_fn output b =
  let
    val visitor as (IdxVisitor vtable) = new_free_ivars_with_anno_idx_visitor output
  in
    #visit_sort vtable visitor () b
  end
    
fun free_ivars_with_anno_ty_visitor_vtable cast (output, visit_i, visit_s) =
    default_ty_visitor_vtable
      cast
      extend_noop
      extend_noop
      visit_noop
      visit_noop
      (ignore_this_env $ visit_i output)
      (ignore_this_env $ visit_s output)
      
fun new_free_ivars_with_anno_ty_visitor params = new_ty_visitor free_ivars_with_anno_ty_visitor_vtable params
    
fun free_ivars_with_anno_t_fn output b =
  let
    val visitor as (TyVisitor vtable) = new_free_ivars_with_anno_ty_visitor (output, free_ivars_with_anno_i_fn, free_ivars_with_anno_s_fn)
  in
    #visit_ty vtable visitor () b
  end

fun free_ivars_with_anno_expr_visitor_vtable cast (output, visit_i, visit_s, visit_t) =
    default_expr_visitor_vtable
      cast
      extend_noop
      extend_noop
      extend_noop
      extend_noop
      visit_noop
      visit_noop
      (ignore_this_env $ visit_i output)
      (ignore_this_env $ visit_s output)
      (ignore_this_env $ visit_t output)

fun new_free_ivars_with_anno_expr_visitor params = new_expr_visitor free_ivars_with_anno_expr_visitor_vtable params
    
fun free_ivars_with_anno_e_fn output b =
  let
    val visitor as (ExprVisitor vtable) = new_free_ivars_with_anno_expr_visitor (output, free_ivars_with_anno_i_fn, free_ivars_with_anno_s_fn, free_ivars_with_anno_t_fn)
  in
    #visit_expr vtable visitor () b
  end

fun free_ivars_with_anno_e e =
    let
      val vars = free_vars_with_anno_0 free_ivars_with_anno_e_fn e
                                       (* todo: rearrange [vars] to satisfy dependencies between them *)
    in
      vars
    end

fun free_tvars_with_anno_ty_visitor_vtable cast output (* : ('this, unit, 'var, 'bsort, 'idx, 'sort, 'var, 'bsort, 'idx, 'sort) ty_visitor_vtable *) =
  let
    fun visit_TVar this env (data as (var, ks)) =
        case var of
            QID (_, (x, _)) =>
            (case ks of
                 k :: _ => (output (Free_t x, k); TVar data)
               | [] => raise Impossible "free_tvars_with_anno_t/TVar/QID/ks=[]"
            )
          | _ => TVar data
    val vtable = 
        default_ty_visitor_vtable
          cast
          extend_noop
          extend_noop
          (visit_imposs "free_tvars_with_anno_t/visit_var")
          visit_noop
          visit_noop
          visit_noop
    val vtable = override_visit_TVar vtable visit_TVar
  in
    vtable
  end

fun new_free_tvars_with_anno_ty_visitor a = new_ty_visitor free_tvars_with_anno_ty_visitor_vtable a
    
fun free_tvars_with_anno_t_fn output b =
  let
    val visitor as (TyVisitor vtable) = new_free_tvars_with_anno_ty_visitor output
  in
    #visit_ty vtable visitor () b
  end
    
fun free_tvars_with_anno_t a = free_vars_with_anno_0 free_tvars_with_anno_t_fn a
      
fun free_tvars_with_anno_expr_visitor_vtable cast (output, visit_t) (* : ('this, int, 'var, 'idx, 'sort, 'kind, 'ty, 'var, 'idx, 'sort, 'kind, 'ty2) expr_visitor_vtable *) =
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
      (ignore_this_env $ visit_t output)

fun new_free_tvars_with_anno_expr_visitor params = new_expr_visitor free_tvars_with_anno_expr_visitor_vtable params
    
fun free_tvars_with_anno_e_fn output b =
  let
    val visitor as (ExprVisitor vtable) = new_free_tvars_with_anno_expr_visitor (output, free_tvars_with_anno_t_fn)
  in
    #visit_expr vtable visitor () b
  end

fun free_tvars_with_anno_e a = free_vars_with_anno_0 free_tvars_with_anno_e_fn a
    
fun free_evars_with_anno_expr_visitor_vtable cast output (* : ('this, unit, 'var, 'idx, 'sort, 'kind, 'ty, 'var, 'idx, 'sort, 'kind, 'ty) expr_visitor_vtable *) =
  let
    fun visit_EAscType this env (e, t) =
      let
        val (e_core, _) = collect_EAscTypeTime e
      in
        case e_core of
            EVar (QID (_, (x, _))) => (output (Free_e x, t); EAscType (e, t))
          | _ => EAscType (#visit_expr (cast this) this env e, t)
      end
    fun visit_var this env var =
        case var of
            QID _ => raise Impossible "free_evars_with_anno/visit_var/QID"
          | _ => var
    val vtable = 
        default_expr_visitor_vtable
          cast
          extend_noop
          extend_noop
          extend_noop
          extend_noop
          visit_var
          visit_noop
          visit_noop
          visit_noop
          visit_noop
    val vtable = override_visit_EAscType vtable visit_EAscType
  in
    vtable
  end

fun new_free_evars_with_anno_expr_visitor params = new_expr_visitor free_evars_with_anno_expr_visitor_vtable params

fun free_evars_with_anno_fn output b =
  let
    val visitor as (ExprVisitor vtable) = new_free_evars_with_anno_expr_visitor output
  in
    #visit_expr vtable visitor () b
  end

fun free_evars_with_anno a = free_vars_with_anno_0 free_evars_with_anno_fn a
      
fun open_collect_TForallIT t =
  case t of
      TQuanI (Forall, bind) =>
      let
        val (s, (name, t)) = unBindAnnoName bind
        val x = fresh_ivar ()
        val t = open0_i_t x t
        val (binds, t) = open_collect_TForallIT t
      in
        (inl (x, fst name, s) :: binds, t)
      end
    | TQuan (Forall, bind) =>
      let
        val (k, (name, t)) = unBindAnnoName bind
        val x = fresh_tvar ()
        val t = open0_t_t x t
        val (binds, t) = open_collect_TForallIT t
      in
        (inr (x, fst name, k) :: binds, t)
      end
    | _ => ([], t)

fun open_collect_EAbsIT e =
  case e of
      EAbsI bind =>
      let
        val (s, (name, e)) = unBindAnnoName bind
        val x = fresh_ivar ()
        val e = open0_i_e x e
        val (binds, e) = open_collect_EAbsIT e
      in
        (inl (x, fst name, s) :: binds, e)
      end
    | EAbsT bind =>
      let
        val (k, (name, e)) = unBindAnnoName bind
        val x = fresh_tvar ()
        val e = open0_t_e x e
        val (binds, e) = open_collect_EAbsIT e
      in
        (inr (x, fst name, k) :: binds, e)
      end
    | _ => ([], e)

fun close_TForallIT (bind, t) =
    case bind of
        inl (x, name, s) => TForallI $ close0_i_t_anno ((x, name, s), t)
      | inr (x, name, k) => TForall $ close0_t_t_anno ((x, name, k), t)
fun close_TForallITs (binds, t) = foldr close_TForallIT t binds
                                      
fun close_EAbsIT (bind, e) =
    case bind of
        inl (x, name, s) => EAbsI $ close0_i_e_anno ((x, name, s), e)
      | inr (x, name, k) => EAbsT $ close0_t_e_anno ((x, name, k), e)
fun close_EAbsITs (binds, t) = foldr close_EAbsIT t binds
                                      
fun IV (x, s) = VarI (make_Free_i x, [s])
fun TV (x, k) = TVar (make_Free_t x, [k])

fun TExists bind = TQuan (Exists (), bind)
                         
fun EAppIT (e, arg) =
    case arg of
        inl i => EAppI (e, i)
      | inr t => EAppT (e, t)
fun EAppITs (f, args) = foldl (swap EAppIT) f args
                     
fun ELetManyClose (ds, e) = foldr ELetClose e ds

val ETT = EConst ECTT

fun ceil_half n = (n + 1) div 2

fun callcc (f : ('a -> unit) -> 'a) : 'a = Cont.callcc (fn k => f (fn v => Cont.throw k v))
                                
(* convert lists to Unsafe.Array to support random access *)
fun make_Record_k make_Prod make_Unit ls return =
    let
      val make_Record = make_Record make_Prod make_Unit
      val len = length ls
      val () = if len = 0 then return make_Unit else ()
      val () = if len = 1 then return $ hd ls else ()
      val len_fst_half = ceil_half len
      val fst_half = take len_fst_half ls
      val snd_half = drop len_fst_half ls
    in
      make_Prod (make_Record fst_half, make_Record snd_half)
    end

and make_Record make_Prod make_Unit ls = callcc $ make_Record_k make_Prod make_Unit ls

fun TRecord a = make_Record TProd TUnit a
fun ERecord a = make_Record EPair ETT a

fun ERecordProj_k (len, i) e return =
    let
      val () = if len = 0 then return ETT else ()
      val () = if len = 1 then return e else ()
      val len_fst_half = ceil_half len
    in
      if i < len_fst_half then
        ERecordProj (len_fst_half, i) $ EFst e
      else
        ERecordProj (len - len_fst_half, i - len_fst_half) $ ESnd e
    end

and ERecordProj (len, i) e = callcc $ ERecordProj_k (len, i) e
      
fun assert_EAbs e =
  case e of
      EAbs bind => unBindAnnoName bind
    | _ => raise assert_fail "assert_EAbs"
                 
fun map_inr f a =
    case a of
        inl _ => a
      | inr b => inr $ f b

fun map_inl_inr f1 f2 s =
    case s of
        inl e => inl $ f1 e
      | inr e => inr $ f2 e

infixr 0 %$
fun a %$ b = EApp (a, b)

(* fun unBindSimpOpen_t bind = *)
(*     let *)
(*       val (name, b) = unBindSimpName bind *)
(*       val x = fresh_tvar () *)
(*       val b = open0_t_e x b *)
(*     in *)
(*       (x, name, b) *)
(*     end *)
                      
fun unBindSimpOpen_e bind =
    let
      val (name, b) = unBindSimpName bind
      val x = fresh_evar ()
      val b = open0_e_e x b
    in
      (x, name, b)
    end

fun EAbsIT (bind, e) =
    case bind of
        inl bind => EAbsI $ IBindAnno (bind, e)
      | inr bind => EAbsT $ TBindAnno (bind, e)
fun EAbsITs (binds, e) = foldr EAbsIT e binds
                                      
fun convert_EAbs_to_ERec_expr_visitor_vtable cast () =
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
    fun visit_ERec this env bind =
        let
          val (t_x, (name_x, e)) = unBindAnnoName bind
          val (binds, e) = collect_EAbsIT e
          val (t_y, (name_y, e)) = assert_EAbs e
          val e = #visit_expr (cast this) this env e
          val e = EAbs $ EBindAnno ((name_y, t_y), e)
        in
          ERec $ EBindAnno ((name_x, t_x), EAbsITs (binds, e))
        end
    fun visit_EAbs this env bind =
      let
        val (t_y, (name_y, e)) = unBindAnnoName bind
        val ((_, t_e), i) = mapFst assert_EAscType $ assert_EAscTime e
        val e = #visit_expr (cast this) this env e
        val e = EAbs $ EBindAnno ((name_y, t_y), e)
      in
        ERec $ EBindAnno ((("__f", dummy), TArrow (t_y, i, t_e)), shift01_e_e e)
      end
    val vtable = override_visit_ERec vtable visit_ERec
    val vtable = override_visit_EAbs vtable visit_EAbs
  in
    vtable
  end

fun new_convert_EAbs_to_ERec_expr_visitor params = new_expr_visitor convert_EAbs_to_ERec_expr_visitor_vtable params

fun convert_EAbs_to_ERec b =
  let
    val visitor as (ExprVisitor vtable) = new_convert_EAbs_to_ERec_expr_visitor ()
  in
    #visit_expr vtable visitor () b
  end

fun cc_t t =
  case t of
      TArrow _ =>
      cc_t_arrow t
    | TQuan (Forall, _) =>
      cc_t_arrow t
    | TQuanI (Forall, _) =>
      cc_t_arrow t
    | TVar _ => t
    | TConst _ => t
    | TBinOp (opr, t1, t2) => TBinOp (opr, cc_t t1, cc_t t2)
    | TQuan (q, bind) =>
      let
        val (k, (name, t)) = unBindAnnoName bind
        val a = fresh_tvar ()
        val t = open0_t_t a t
        val t = cc_t t
      in
        TQuan (q, TBindAnno ((name, k), t))
      end
    | TQuanI (q, bind) =>
      let
        val (s, (name, t)) = unBindAnnoName bind
        val a = fresh_ivar ()
        val t = open0_i_t a t
        val t = cc_t t
      in
        TQuanI (q, IBindAnno ((name, s), t))
      end
    | TRec bind =>
      let
        val (k, (name, t)) = unBindAnnoName bind
        val a = fresh_tvar ()
        val t = open0_t_t a t
        val t = cc_t t
      in
        TRec $ TBindAnno ((name, k), t)
      end
    | TAbsT bind =>
      let
        val (k, (name, t)) = unBindAnnoName bind
        val a = fresh_tvar ()
        val t = open0_t_t a t
        val t = cc_t t
      in
        TAbsT $ TBindAnno ((name, k), t)
      end
    | TAbsI bind =>
      let
        val (s, (name, t)) = unBindAnnoName bind
        val a = fresh_ivar ()
        val t = open0_i_t a t
        val t = cc_t t
      in
        TAbsI $ IBindAnno ((name, s), t)
      end
    | TNat _ => t
    | TAppT (t, t') => TAppT (cc_t t, cc_t t')
    | TAppI (t, i) => TAppI (cc_t t, i)
    | TArr (t, i) => TArr (cc_t t, i)

and cc_t_arrow t =
    let
      val (binds, t) = open_collect_TForallIT t
      val (t1, i, t2) = assert_TArrow t
      val t1 = cc_t t1
      val t2 = cc_t t2
      val alpha = fresh_tvar ()
      val t = TArrow (TProd (TV (alpha, KType), t1), i, t2)
      val t = close_TForallITs (binds, t)
      val t = TProd (t, TV (alpha, KType))
      val t = TExists $ close0_t_t_anno ((alpha, "'a", KType), t)
    in
      t
    end

fun cc_expr_un_op opr =
    case opr of
        EUProj _ => opr
      | EUInj (inj, t) => EUInj (inj, cc_t t)
      | EUFold t => EUFold $ cc_t t
      | EUUnfold => opr

fun cc e =
    case e of
        EBinOp (EBApp, e1, e2) =>
        let
          val (e1, itargs) = collect_EAppIT e1
          (* val (e1, t_e1) = assert_EAscType e1 *)
          (* val t_e1 = cc_t t_e1 *)
          (* val (_, t_pair) = assert_TExists t_e1 *)
          (* val (t_code, _) = assert_TProd t_pair *)
          val gamma = fresh_tvar ()
          val z = fresh_evar ()
          val z_code = fresh_evar ()
          val z_env = fresh_evar ()
          val e = EAppITs (e1, map (map_inr cc_t) itargs) %$ EPair (EV z_env, cc e2)
          val e = ELetManyClose ([(z_code, "z_code", EFst $ EV z), (z_env, "z_env", ESnd $ EV z)], e)
          val e = EUnpackClose (cc e1, (gamma, "'c"), (z, "z"), e)
        in
          e
        end
      | EBinOp (opr, e1, e2) => EBinOp (opr, cc e1, cc e2)
      | EAbsT _ => cc_abs e
      | EAbsI _ => cc_abs e
      | EAbs _ => cc_abs e
      | ERec _ => cc_abs e
      | ELet (e1, bind) =>
        let
          val e1 = cc e1
          val (x, name, e2) = unBindSimpOpen_e bind
          val e2 = cc e2
        in
          ELetClose ((x, fst name, e1), e2)
        end
      | ECase (e, bind1, bind2) =>
        let
          val e = cc e
          val (x1, name1, e1) = unBindSimpOpen_e bind1
          val (x2, name2, e2) = unBindSimpOpen_e bind2
        in
          ECaseClose (e, ((x1, fst name1), e1), ((x2, fst name2), e2))
        end
      | EPack (tp, t, e) => EPack (cc_t tp, cc_t t, cc e)
      | EUnpack (e1, bind) =>
        let
          val e1 = cc e1
          val (name_a, bind) = unBindSimpName bind
          val (name_x, e2) = unBindSimpName bind
          val a = fresh_tvar ()
          val x = fresh_evar ()
          val e2 = open0_t_e a e2
          val e2 = open0_e_e x e2
          val e2 = cc e2
        in
          EUnpackClose (e1, (a, fst name_a), (x, fst name_x), e2)
        end
      | EPackI (tp, i, e) => EPackI (cc_t tp, i, cc e)
      | EUnpackI (e1, bind) =>
        let
          val e1 = cc e1
          val (name_a, bind) = unBindSimpName bind
          val (name_x, e2) = unBindSimpName bind
          val a = fresh_ivar ()
          val x = fresh_evar ()
          val e2 = open0_i_e a e2
          val e2 = open0_e_e x e2
          val e2 = cc e2
        in
          EUnpackIClose (e1, (a, fst name_a), (x, fst name_x), e2)
        end
      | EVar _ => e
      | EConst _ => e
      | EUnOp (opr, e) => EUnOp (cc_expr_un_op opr, cc e)
      | EAscType (e, t) => EAscType (cc e, cc_t t)
      | EAscTime (e, i) => EAscTime (cc e, i)
      | ENever t => ENever (cc_t t)
      | EBuiltin t => EBuiltin (cc_t t)
      | _ => raise Unimpl "cc"

and cc_abs e_all =
    let
      val (binds, e) = open_collect_EAbsIT e_all
    in
      case e of
          ERec bind => cc_ERec e_all binds bind
        (* | EAbs bind => cc_EAbs e_all binds bind *)
        | _ => raise Impossible "cc_abs"
    end

and cc_ERec e_all outer_binds bind =
    let
      val (t_x, (name_x, e)) = unBindAnnoName bind
      val x = fresh_evar ()
      val e = open0_e_e x e
      val (inner_binds, e) = open_collect_EAbsIT e
      val (t_z, (name_z, e)) = assert_EAbs e
      val z = fresh_evar ()
      val e = open0_e_e z e
      val (_, t_arrow) = open_collect_TForallIT t_x
      val (_, i, _) = assert_TArrow t_arrow
      val (ys, sigmas) = unzip $ free_evars_with_anno e_all
      fun add_name prefix (i, (a, b)) = (a, prefix ^ str_int (1+i), b)
      val free_ivars = mapi (add_name "a") $ free_ivars_with_anno_e e_all
      val free_tvars = mapi (add_name "'a") $ free_tvars_with_anno_e e_all
      val betas = map inl free_ivars @ map inr free_tvars
      val t_env = cc_t $ TRecord sigmas
      val t_z = cc_t t_z
      val t_arrow = TArrow (TProd (t_env, t_z), i, TUnit)
      val z_code = fresh_evar ()
      val z_env = fresh_evar ()
      fun EAppITs_binds (e, binds) =
          let
            (* fun proj_3_1 (a1, _, _) = a1 *)
            fun make_var f (x, _, anno) = f (x, anno)
          in
            EAppITs (e, map (map_inl_inr (make_var IV) (make_var TV)) binds)
          end
      val def_x = EPack (cc_t t_x, t_env, EPair (EAppITs_binds (EV z_code, betas @ outer_binds), EV z_env))
      val len_ys = length ys
      val ys_defs = mapi (fn (i, y) => (y, "y" ^ str_int (1+i), ERecordProj (len_ys, i) $ EV z_env)) ys
      val e = ELetManyClose ((x, fst name_x, def_x) :: ys_defs, cc e)
      val e = EAbsPairClose ((z_env, "z_env", t_env), (z, fst name_z, t_z), e)
      val e = close_EAbsITs (betas @ outer_binds @ inner_binds, e)
      val t_rawcode = close_TForallITs (betas @ outer_binds @ inner_binds, t_arrow)
      (* val t_code = TForallITClose (inner_binds, t_arrow) *)
      val v_code = ERec $ close0_e_e_anno ((z_code, fst name_x ^ "_code", t_rawcode), e)
      val v_env = ERecord $ map EV ys
      (* val x_code = fresh_evar () *)
      val e = EPack (cc_t $ close_TForallITs (outer_binds, t_x), t_env, EPair (EAppITs_binds ((* EV x_code *)v_code, betas), v_env))
      (* val e = ELetClose ((x_code, name_x ^ "_code", v_code), e) *)
    in
      e
    end

(* and cc_EAbs e_all outer_binds bind = *)
(*     let *)
(*       val (t_z, (name_z, e)) = unBindAnnoName bind *)
(*       val z = fresh_evar () *)
(*       val e = open0_e_e z e *)
(*       val (e, i) = assert_EAscTime e *)
(*       val t_e_all = TForallIT (outer_binds, TArrow (t_z, i, TUnit)) *)
(*       val (ys, sigmas) = unzip $ free_vars_with_anno e_all *)
(*       val betas = free_tvars e_all *)
(*       val t_env = cc_t $ TRecord sigmas *)
(*       val t_z = cc_t t_z *)
(*       val t_arrow = TArrow (TProd (t_env, t_z), i, TUnit) *)
(*       (* val t_rawcode = TForallITClose (betas @ outer_binds, t_arrow) *) *)
(*       (* val t_code = TForallITClose (outer_binds, t_arrow) *) *)
(*       val z_env = fresh_evar () *)
(*       val len_ys = length ys *)
(*       val ys_defs = mapi (fn (i, y) => (y, "y" ^ str_int (1+i), ERecordProj (len_ys, i) $ EV z_env)) ys *)
(*       val e = ELetManyClose (ys_defs, cc e) *)
(*       val e = EAbsPairClose ((z_env, "z_env", t_env), (z, name_z, t_z), e) *)
(*       val v_code = EAbsITClose (betas @ outer_binds, e) *)
(*       val v_env = ERecord ys *)
(*       val e = EPack (cc_t $ t_e_all, t_env, EPair (EAppITs (v_code, betas), v_env)) *)
(*     in *)
(*       e *)
(*     end *)

(* fun free_itvars_with_anno_e e = *)
(*     let *)
(*     in *)
(*     end *)

val cc = fn e => cc $ convert_EAbs_to_ERec e

structure UnitTest = struct

structure TestUtil = struct

open CPS
open LongId
open Util
open MicroTiML
open MicroTiMLVisitor
open MicroTiMLExLongId
open MicroTiMLEx
       
infixr 0 $
infixr 0 !!
         
fun short_to_long_id x = ID (x, dummy)
fun export_var (sel : 'ctx -> string list) (ctx : 'ctx) id =
  let
    fun unbound s = "__unbound_" ^ s
    (* fun unbound s = raise Impossible $ "Unbound identifier: " ^ s *)
  in
    case id of
        ID (x, _) =>
        short_to_long_id $ nth_error (sel ctx) x !! (fn () => unbound $ str_int x)
        (* short_to_long_id $ str_int x *)
      | QID _ => short_to_long_id $ unbound $ CanToString.str_raw_var id
  end
(* val export_i = return2 *)
fun export_i a = ToString.export_i Gctx.empty a
fun export_s a = ToString.export_s Gctx.empty a
fun export_t a = export_t_fn (export_var snd, export_i, export_s) a
fun export a = export_e_fn (export_var #4, export_var #3, export_i, export_s, export_t) a
val str = PP.string
fun str_var x = LongId.str_raw_long_id id(*str_int*) x
fun str_i a =
  (* ToStringRaw.str_raw_i a *)
  ToString.SN.strn_i a
  (* const_fun "<idx>" a *)
fun str_bs a =
  ToStringRaw.str_raw_bs a
fun str_s a =
  (* ToStringRaw.str_raw_s a *)
  ToString.SN.strn_s a
  (* const_fun "<sort>" a *)
fun pp_t_to s b =
  MicroTiMLPP.pp_t_to_fn (str_var, str_bs, str_i, str_s, const_fun "<kind>") s b
  (* str s "<ty>" *)
fun pp_t b = MicroTiMLPP.pp_t_fn (str_var, str_bs, str_i, str_s, const_fun "<kind>") b
fun pp_e a = MicroTiMLExPP.pp_e_fn (
    str_var,
    str_i,
    str_s,
    const_fun "<kind>",
    pp_t_to
  ) a
fun fail () = OS.Process.exit OS.Process.failure
                   
end

open TestUtil
       
fun test1 dirname =
  let
    val filename = join_dir_file (dirname, "cc-test1.pkg")
    val filenames = ParseFilename.expand_pkg (fn msg => raise Impossible msg) filename
    open Parser
    val prog = concatMap parse_file filenames
    open Elaborate
    val prog = elaborate_prog prog
    open NameResolve
    val (prog, _, _) = resolve_prog empty prog
                                    
    open TypeCheck
    val () = TypeCheck.turn_on_builtin ()
    val () = println "Started TiML typechecking ..."
    val ((prog, _, _), (vcs, admits)) = typecheck_prog empty prog
    val vcs = VCSolver.vc_solver filename vcs
    val () = if null vcs then ()
             else
               raise curry TypeCheck.Error dummy $ (* str_error "Error" filename dummy *) [sprintf "Typecheck Error: $ Unproved obligations:" [str_int $ length vcs], ""] @ (
               (* concatMap (fn vc => str_vc true filename vc @ [""]) $ map fst vcs *)
               concatMap (VCSolver.print_unsat true filename) vcs
             )
    val () = println "Finished TiML typechecking"
                     
    open MergeModules
    val decls = merge_prog prog []
    open TiML2MicroTiML
    val e = SMakeELet (Teles decls, Expr.ETT dummy)
    val () = println "Simplifying ..."
    val e = SimpExpr.simp_e [] e
    val () = println "Finished simplifying"
    (* val () = println $ str_e empty ToStringUtil.empty_ctx e *)
    (* val () = println "" *)
    val () = println "Started translating ..."
    val e = trans_e e
    val () = println "Finished translating"
    (* val () = pp_e $ export ToStringUtil.empty_ctx e *)
    (* val () = println "" *)
                     
    open MicroTiMLTypecheck
    open TestUtil
    val () = println "Started MicroTiML typechecking #1 ..."
    val ((e, t, i), vcs, admits) = typecheck ([], [], [](* , HeapMap.empty *)) e
    val () = println "Finished MicroTiML typechecking #1"
    val () = println "Type:"
    val () = pp_t $ export_t ([], []) t
    val () = println "Time:"
    val i = simp_i i
    val () = println $ ToString.str_i Gctx.empty [] i
    (* val () = println $ "#VCs: " ^ str_int (length vcs) *)
    (* val () = println "VCs:" *)
    (* val () = app println $ concatMap (fn ls => ls @ [""]) $ map (str_vc false "") vcs *)
    (* val () = pp_e $ export ToStringUtil.empty_ctx e *)
    (* val () = println "" *)
                     
    val () = println "Started CPS conversion ..."
    val (e, _) = cps (e, TUnit) (Eid TUnit, T_0)
    val () = println "Finished CPS conversion"
    val () = pp_e $ export ToStringUtil.empty_ctx e
    val () = println ""
    val () = println "Started MicroTiML typechecking #2 ..."
    val ((e, t, i), vcs, admits) = typecheck ([], [], [](* , HeapMap.empty *)) e
    val () = println "Finished MicroTiML typechecking #2"
    val () = println "Type:"
    val () = pp_t $ export_t ([], []) t
    val () = println "Time:"
    val i = simp_i i
    val () = println $ ToString.str_i Gctx.empty [] i
                     
    val () = println "Started CC ..."
    val e = cc e
    val () = println "Finished CC"
    val () = pp_e $ export ToStringUtil.empty_ctx e
    val () = println ""
    val () = println "Started MicroTiML typechecking #3 ..."
    val ((e, t, i), vcs, admits) = typecheck ([], [], [](* , HeapMap.empty *)) e
    val () = println "Finished MicroTiML typechecking #3"
    val () = println "Type:"
    val () = pp_t $ export_t ([], []) t
    val () = println "Time:"
    val i = simp_i i
    val () = println $ ToString.str_i Gctx.empty [] i
                     
  in
    ((* t, e *))
  end
  handle MicroTiMLTypecheck.MTCError msg => (println $ "MTiMLTC.MTCError: " ^ substr 0 1000 msg; fail ())
       | TypeCheck.Error (_, msgs) => (app println $ "TC.Error: " :: msgs; fail ())
       | NameResolve.Error (_, msg) => (println $ "NR.Error: " ^ msg; fail ())
    
val test_suites = [
      test1
]
                            
end
                       
end
