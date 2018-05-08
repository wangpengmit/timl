structure TiML2MicroTiML = struct

structure TiML = Expr
structure S = TiML
open S
open Subst
open MicroTiML
open MicroTiMLVisitor
open MicroTiML
structure Op = Operators
open Util
open Bind
open ShiftUtil
open Unbound
       
infixr 0 $
infixr 0 !!

exception T2MTError of string

open MicroTiMLUtilTiML
open MicroTiMLUtil
       
fun on_k ((n, bs) : S.kind) : bsort kind = KArrowTypes n $ KArrows bs KType

fun foldr' f init xs = foldl' f init $ rev xs

fun TSums ts = foldr' TSum TEmpty ts
fun unTSums t =
  case t of
      TBinOp (TBSum, t1, t2) => t1 :: unTSums t2
    | _ => [t]
fun EInj (ts, n, e) =
  case ts of
      [] => raise Impossible "EInj []"
    | [t] =>
      let
        val () = assert (fn () => n = 0) "EInj(): n = 0"
      in
        e
      end
    | t :: ts =>
      if n <= 0 then
        EInl (TSums ts, e)
      else
        EInr (t, EInj (ts, n-1, e))

fun int2var x = ID (x, dummy)

fun PEqs pairs = combine_And $ map PEq pairs
  
val BSUnit = Base UnitSort

fun on_mt (t : S.mtype) =
  case t of
      S.Arrow ((i1, t1), i, (i2, t2)) => TArrow ((IState i1, on_mt t1), i, (IState i2, on_mt t2))
    | S.TyNat (i, _) => TNat i
    | S.TiBool (i, _) => TiBool i
    | S.TyArray (t, i) => TArr (on_mt t, i)
    | S.Unit _ => TUnit
    | S.Prod (t1, t2) => TProd (on_mt t1, on_mt t2)
    | S.UniI (s, Bind.Bind (name, t), r) => TQuanI (Forall, IBindAnno ((name, s), on_mt t))
    | S.MtVar x => TVar (x, [])
    | S.MtApp (t1, t2) => TAppT (on_mt t1, on_mt t2)
    | S.MtAbs (k, Bind.Bind (name, t), _) => TAbsT $ TBindAnno ((name, on_k k), on_mt t)
    | S.MtAppI (t, i) => TAppI (on_mt t, i)
    | S.MtAbsI (b, Bind.Bind (name, t), _) => TAbsI $ IBindAnno ((name, b), on_mt t)
    | S.BaseType (t, r) => TConst (TCTiML t)
    | S.UVar (x, _) =>
      (* exfalso x *)
      raise Impossible "to-micro-timl/on_mt/UVar"
    | S.TSumbool (s1, s2) => TSumbool (s1, s2)
    | S.TDatatype (Bind.Bind (dt_name, tbinds), _) =>
      let
        val (tname_kinds, (bsorts, constrs)) = unfold_binds tbinds
        val tnames = map fst tname_kinds
        fun on_constr (ibinds : S.mtype S.constr_core) =
          let
            val len_bsorts = length bsorts
            val ibinds = on_i_ibinds shiftx_i_s (on_pair (shiftx_i_mt, on_list shiftx_i_i)) 0 len_bsorts ibinds
            val (name_sorts, (t, is)) = unfold_binds ibinds
            val () = assert (fn () => length is = len_bsorts) "length is = len_bsorts"
            val formal_iargs = map (fn x => VarI (int2var x, [])) $ rev $ range $ len_bsorts
            val t = shiftx_i_mt 0 1 t
            val is = map (shiftx_i_i 0 1) is
            val formal_iargs = map (shiftx_i_i 0 (length name_sorts + 1)) formal_iargs
            val prop = PEqs $ zip (is, formal_iargs)
            (* val extra_sort_name = "__datatype_constraint" *)
            val extra_sort_name = "__VC"
            val extra_sort = Subset ((BSUnit, dummy), Bind.Bind ((extra_sort_name, dummy), prop), dummy)
            val t = on_mt t
            val t = TExistsI_Many (rev $ map (mapFst IName) $ ((extra_sort_name, dummy), extra_sort) :: rev name_sorts, t)
          in
            t
          end
        val len_tnames = length tnames
        val k = KArrowTypes len_tnames $ KArrows bsorts KType
        val ts = map (fn (_, c, _) => on_constr c) constrs
        val t = TSums ts
        fun attach_names namespace f ls = mapi (fn (n, b) => (namespace (f n, dummy), b)) ls
        val t = TAbsI_Many (rev $ attach_names IName (fn n => "_i" ^ str_int n) $ rev bsorts, t)
        val t = TAbsT_Many (rev $ attach_names TName (fn n => "_t" ^ str_int n) $ repeat len_tnames KType, t)
      in
        TRec $ BindAnno ((TName dt_name, k), t)
      end
    | S.TMap t => TMap $ on_mt t
    | S.TState (x, _) => TState x
    | S.TTuplePtr (ts, n, _) => TStorageTuplePtr (map on_mt ts, INat n)

val trans_mt = on_mt
                 
open MicroTiMLLongId
open PatternEx
structure S = TiML
                
fun shift_e_pn a = shift_e_pn_fn shift_e_e a

fun SEV n = S.EVar (ID (n, dummy), true)
fun SMakeECase (e, rules) = S.ECase (e, (NONE, NONE), map Bind rules, dummy)
fun SMakeELet (decls, e) = S.ELet ((NONE, NONE), Bind (decls, e), dummy)

structure SS = struct
open ExprShift
open ExprSubst
end
                 
fun EV n = EVar (ID (n, dummy))

fun on_e (e : S.expr) =
  let
    fun err () = raise Impossible $ "unknown case in tc: " ^ ToString.str_e Gctx.empty ToStringUtil.empty_ctx e
  in
  case e of
      S.EVar (x, _) => EVar x
    | S.EConst (c, _) => EConst c
    | S.EState (x, _) => EState x
    | S.EUnOp (opr, e, _) => EUnOp (EUTiML opr, on_e e)
    | S.EBinOp (opr, e1, e2) => EBinOp (opr, on_e e1, on_e e2)
    | S.ETriOp (opr, e1, e2, e3) => ETriOp (opr, on_e e1, on_e e2, on_e e3)
    | S.EEI (opr, e, i) =>
      (case opr of
           Op.EEIAppI => EAppI (on_e e, i)
         | Op.EEIAscTime => EAscTime (on_e e, i)
      )
    | S.EET (opr, e, t) =>
      (case opr of
           EETAsc => EAscType (on_e e, on_mt t)
         | EETAppT => EAppT (on_e e, on_mt t)
         | EETHalt => EHalt (on_e e, on_mt t)
      )
    | S.ET (opr, t, r) =>
      (case opr of
           Op.ETNever => ENever (on_mt t)
         | Op.ETBuiltin name => EBuiltin (name, on_mt t)
      )
    | S.ENewArrayValues (t, es, r) => ENewArrayValues (on_mt t, map on_e es)
    | S.ECaseSumbool (e, bind1, bind2, r) =>
      let
        fun on_bind bind =
          let
            val (iname, e) = unBindSimpName bind
            val e = on_e e
            val e = EUnpackI (EV 0, IBind (iname, EBind (("__u", r), shift_e_e 0 2 e)))
          in
            EBind (("__ex", r), e)
          end
      in
        ECase (on_e e, on_bind bind1, on_bind bind2)
      end
    | S.EIfi (e, bind1, bind2, r) =>
      let
        fun on_bind bind =
          let
            val (iname, e) = unBindSimpName bind
            val e = on_e e
            val e = EUnpackI (EV 0, IBind (iname, EBind (("__u", r), shift_e_e 0 2 e)))
          in
            EBind (("__ex", r), e)
          end
      in
        EIfi (on_e e, on_bind bind1, on_bind bind2)
      end
    | S.ECase (e, return, rules, r) =>
      let
        (* todo: use information in [return] *)
        val e = on_e e
        val rules = map (mapPair (from_TiML_ptrn, on_e) o unBind) rules
        val name = default (EName ("__x", dummy)) $ firstSuccess get_pn_alias $ map fst rules
        val pns = map PnBind rules
        val pns = map (shift_e_pn 0 1) pns
        (* val shift_i_e = fn x => fn n => fn e => *)
        (*   let *)
        (*     val e' = shift_i_e x n e *)
        (*     val () =  *)
        (*         case (e, e') of *)
        (*             (EVar y, EVar y') => *)
        (*             let *)
        (*               val () = println $ sprintf "shift_i EVar: n=$, e=$, e'=$" [str_int n, LongId.str_raw_long_id str_int y, LongId.str_raw_long_id str_int y'] *)
        (*             in *)
        (*               () *)
        (*             end *)
        (*           | _ => () *)
        (*   in *)
        (*     e' *)
        (*   end *)
        (* val shift_e_e = fn x => fn n => fn e => *)
        (*   let *)
        (*     val e' = shift_e_e x n e *)
        (*     val () = println $ sprintf "shift_e: x=$, n=$, e=$, e'=$" [str_int x, str_int n, pp_e_to_string e, pp_e_to_string e'] *)
        (*   in *)
        (*     e' *)
        (*   end *)
        fun export_pp_e_to_s e = ExportPP.pp_e_to_string (NONE, NONE) $ ExportPP.export (NONE, NONE) ([], [], [], []) e
        val e2 = to_expr (shift_i_e, shift_e_e, subst_e_e, EV, export_pp_e_to_s) (EV 0) pns
      in
        ELet (e, BindSimp (name, e2))
      end
    (* todo: EAbs should delegate to ECase *)
    (* | S.EAbs bind => *)
    (*   let *)
    (*     val (pn, e) = unBind bind *)
    (*     val (pn, Outer t) = case pn of S.AnnoP a => a | _ => raise Impossible "must be AnnoP" *)
    (*     val t = on_mt t *)
    (*     val e = on_e e *)
    (*     val pn = from_TiML_ptrn pn *)
    (*     val name = default (EName ("__x", dummy)) $ get_pn_alias pn *)
    (*     val pn = PnBind (pn, e) *)
    (*     val pn = shift_e_pn 0 1 pn *)
    (*     val e = to_expr (shift_i_e, shift_e_e, subst_e_e, EV) (EV 0) [pn] *)
    (*   in *)
    (*     EAbs $ BindAnno ((name, t), e) *)
    (*   end *)
    | S.EAbs (st, bind) =>
      (* delegate to ECase *)
      let
        val (pn, e) = unBind bind
        val (pn, Outer t) = case pn of S.AnnoP a => a | _ => raise Impossible "to-micro-timl/EAbs: must be AnnoP"
        val name = default (EName ("__x", dummy)) $ get_pn_alias $ from_TiML_ptrn pn
        val t = on_mt t
        fun shift_e_rule a = DerivedTrans.for_rule SS.shift_e_e a
        val e = SMakeECase (SEV 0, [shift_e_rule (pn, e)])
        val e = on_e e
      in
        EAbs (IState st, BindAnno ((name, t), e))
      end
    | S.EAbsI (bind, _) =>
      let
        val ((name, s), e) = unBindAnno bind
      in
        EAbsI $ BindAnno ((name, s), on_e e)
      end
    (* | S.EAppConstr ((x, eia), ts, is, e, ot) => *)
    (*   let *)
    (*     val () = if eia then () else raise Impossible "to-micro-timl/AppConstr/eia" *)
    (*     val (pos, t) = ot !! (fn () => raise Impossible "to-micro-timl/AppConstr/ot") *)
    (*     val dt = case t of TDatatype (dt, _) => dt | _ => raise Impossible "to-micro-timl/AppConstr/TDatatype" *)
    (*     val e = make_constr (pos, ts, is, e, dt) *)
    (*   in *)
    (*     e *)
    (*   end *)
    | S.EAppConstr ((x, eia), ts, is, e, ot) =>
      let
        val () = if eia then () else raise Impossible "to-micro-timl/AppConstr/eia"
        val ts = map on_mt ts
        val e = on_e e
        val e = EAppConstr (EVarConstr x, ts, is, e)
      in
        e
      end
    | S.ELet (return, bind, r) => 
      let
        (* todo: use information in [return] *)
        val (decls, e) = Unbound.unBind bind
      in
	on_decls (decls, e)
      end
    | S.ESetModify _ => err ()
    | S.EGet _ => err ()
  end
                 
and add_constr_decls (dt, e_body) =
    let
      val Bind.Bind (name, tbinds) = dt
      val (tname_kinds, (bsorts, constr_decls)) = unfold_binds tbinds
      val tnames = map fst tname_kinds
      val tlen = length tname_kinds
      fun make_constr_bind (pos, (cname, core, _)) =
        let
          val (name_sorts, _) = unfold_binds core
          val inames = map fst name_sorts
          val ilen = length name_sorts
          fun IV n = S.VarI (ID (n, dummy), [])
          fun TV n = S.MtVar $ ID (n, dummy)
          val ts = rev $ Range.map TV (0, tlen)
          val is = rev $ Range.map IV (0, ilen)
          fun shiftx_i_dt x n = DerivedTrans.for_dt $ shiftx_i_mt x n
          fun shiftx_t_dt x n = DerivedTrans.for_dt $ shiftx_t_mt x n
          val dt = shiftx_t_dt 0 tlen dt
          val dt = shiftx_i_dt 0 ilen dt
          val e = make_constr (pos, ts, is, SEV 0, dt)
          val ename = ("__x", dummy)
          val e = MakeEAbsConstr (tnames, inames, ename, e)
        in
          (cname, e)
        end
      val constrs = mapi make_constr_bind constr_decls
      val e_body = foldr (fn ((name, e), e_body) => MakeELetConstr (e, name, e_body)) e_body constrs
    in
      e_body
    end
      
and make_constr (pos, ts, is, e, dt) =
    let
      open ToStringRaw
      open ToString
      (* fun str_var (_, (x, _)) = str_int x *)
      (* fun str_var x = LongId.str_raw_long_id str_int x *)
      (* val pp_t = MicroTiMLPP.pp_t_fn (str_var, str_bs, str_raw_i, str_raw_s, const_fun "<kind>") *)
      val t = TDatatype (dt, dummy)
      val t_rec = on_mt t
      (* val () = println "t_rec:" *)
      (* val () = pp_t t_rec *)
      val Bind.Bind (name, tbinds) = dt
      val (tname_kinds, (bsorts, constr_decls)) = unfold_binds tbinds
      val constr_decl as (_, core, _) = nth_error constr_decls pos !! (fn () => raise Impossible "to-micro-timl/AppConstr: nth_error constr_decls")
      val (name_sorts, (_, result_is)) = unfold_binds core
      val () = assert (fn () => length is = length name_sorts) "length is = length name_sorts"
      (* val () = println "result_is:" *)
      (* val () = println $ str_ls (ToString.str_i Gctx.empty []) result_is *)
      (* val () = println "is:" *)
      (* val () = println $ str_ls (ToString.str_i Gctx.empty []) is *)
      (* val result_is = foldl (fn (v, b) => map (subst_i_i v) b) result_is is *)
      (* val () = println "result_is after:" *)
      (* val () = println $ str_ls (ToString.str_i Gctx.empty []) result_is *)
      val fold_anno = TAppIs (TAppTs (t_rec, map on_mt ts), result_is)
      (* val () = println "fold_anno:" *)
      (* val () = println $ PP_E.pp_t_to_string fold_anno *)
      fun unroll t_rec_apps =
        let
          fun collect_until_TRec t =
            case t of
                TAppI (t, i) =>
                let
                  val (t, args) = collect_until_TRec t
                in
                  (t, args @ [inl i])
                end
              | TAppT (t, t') =>
                let
                  val (t, args) = collect_until_TRec t
                in
                  (t, args @ [inr t'])
                end
              | TRec bind =>
                let
                  val (_, t_body) = unBindAnno bind
                in
                  ((t, t_body), [])
                end
              | _ => raise Impossible "collect_until_TRec"
          val ((t_rec, t_body), args) = collect_until_TRec t_rec_apps
          val t = subst0_t_t t_rec t_body
          fun TApp (t, arg) =
            case arg of
                inl i => TAppI (t, i)
              | inr t' => TAppT (t, t')
          val t = foldl (swap TApp) t args
          val t = normalize_t t
        in
          t
        end
      val unrolled = unroll fold_anno
      (* val () = println "unrolled:" *)
      (* val () = println $ PP_E.pp_t_to_string unrolled *)
      val inj_anno = unTSums unrolled
      (* val () = println $ sprintf "$, $" [str_int $ length inj_anno, str_int pos] *)
      val pack_anno = nth_error inj_anno pos !! (fn () => raise Impossible $ sprintf "to-micro-timl/AppConstr: nth_error inj_anno: $, $" [str_int $ length inj_anno, str_int pos])
      (* val exists = peel_exists (length is + 1) pack_anno *)
      val is = is @ [TTI dummy]
      val e = on_e e
      val e = EPackIs (pack_anno, is, e)
      val e = EInj (inj_anno, pos, e)
      val e = EFold (fold_anno, e)
    in
      e
    end

and on_decls (decls, e_body) =
    case decls of
        TeleNil => on_e e_body
      | TeleCons (decl, Rebind decls) =>
        let
          (* val () = println "translating decl" *)
          (* val () = println $ sprintf "translating: $" [fst $ ToString.str_decl Gctx.empty ToStringUtil.empty_ctx decl] *)
        in
          case decl of
              S.DVal data =>
              let
                val name = unBinderName $ #1 data
                val (e, _) = on_DVal data
                val e_body = on_decls (decls, e_body)
              in
                MakeELet (e, name, e_body)
              end
            | S.DValPtrn (pn, Outer e, r) =>
              let
                val e_body = SMakeELet (decls, e_body)
              in
                on_e $ SMakeECase (e, [(pn, e_body)])
              end
	    | S.DRec data => 
	      let
                val name = unBinderName $ #1 data
                val (e, t) = on_DRec data
                val e_body = on_decls (decls, e_body)
              in
                MakeELet (e, name, e_body)
	      end
            | S.DAbsIdx ((iname, Outer s, Outer i), Rebind inner_decls, r) =>
              let
                val iname = unBinderName iname
                fun make_Unpack_Pack ename (e, t) =
                  let
                    val ename = unBinderName $ ename
                    val t = MakeTExistsI (iname, s, t)
                    val e = EPackI (t, i, MakeELetIdx (i, iname, e))
                    val e_body = on_decls (decls, e_body)
                    val e = MakeEUnpackI (e, iname, ename, e_body)
                  in
                    e
                  end
              in
                case unTeles inner_decls of
                    [S.DRec data] => 
                    let
                      val (e, t) = on_DRec data
                      val e = make_Unpack_Pack (#1 data) (e, t)
                    in
                      e
                    end
                  | [S.DVal data] =>
                    let
                      val (e, t) = on_DVal data
                      val t = t !! (fn () => raise Impossible $ "RHS of DVal inside DAbsIdx must be EAsc:" ^ (fst $ ToString.str_decl Gctx.empty ToStringUtil.empty_ctx decl))
                      val e = make_Unpack_Pack (#1 data) (e, t)
                    in
                      e
                    end
                  | _ => raise Impossible $ "to-micro-timl/DAbsIdx: can only translate when the inner declarations are just one DRec" ^ " or one DVal"
              end
            | S.DOpen (m, octx) =>
              let
                val m = unInner m
                val ctx as (sctx, kctx, cctx, tctx) = octx !! (fn () => raise Impossible "to-micro-timl/DOpen: octx must be SOME")
                val e = SMakeELet (decls, e_body)
                open Package
                val e = (self_compose (length tctx) $ package0_e_e m) $ e
                val e = (self_compose (length cctx) $ package0_c_e m) $ e
                val e = (self_compose (length kctx) $ package0_t_e m) $ e
                val e = (self_compose (length sctx) $ package0_i_e m) $ e
                val e = on_e e
              in
                e
              end
            (* | S.DTypeDef (name, Outer t) => *)
            (*   let *)
            (*     val e = SMakeELet (decls, e_body) *)
            (*     val e = SS.subst_t_e t e *)
            (*     val e = on_e e *)
            (*     val e = case t of *)
            (*                 S.TDatatype (dt, _) => add_constr_decls (dt, e) *)
            (*               | _ => e *)
            (*   in *)
            (*     e *)
            (*   end *)
            | S.DTypeDef (name, Outer mt) =>
              let
                val e = on_decls (decls, e_body)
                val t = on_mt mt
                val e = MakeELetType (t, unBinderName name, e)
                val e = case mt of
                            S.TDatatype (dt, _) => add_constr_decls (dt, e)
                          | _ => e
              in
                e
              end
            (* | S.DIdxDef (name, _, Outer i) => *)
            (*   let *)
            (*     val e = SMakeELet (decls, e_body) *)
            (*     val e = SS.subst_i_e i e *)
            (*     val e = on_e e *)
            (*   in *)
            (*     e *)
            (*   end *)
            (* | S.DAbsIdx2 (name, _, Outer i) => *)
            (*   let *)
            (*     val e = SMakeELet (decls, e_body) *)
            (*     val e = SS.subst_i_e i e *)
            (*     val e = on_e e *)
            (*   in *)
            (*     e *)
            (*   end *)
            | S.DIdxDef (name, _, Outer i) =>
              let
                val e = on_decls (decls, e_body)
                val e = MakeELetIdx (i, unBinderName name, e)
              in
                e
              end
            | S.DConstrDef (name, Outer x) =>
              let
                val e = on_decls (decls, e_body)
                val e = MakeELetConstr (EVarConstr x, unBinderName name, e)
              in
                e
              end
            | S.DAbsIdx2 (name, _, Outer i) =>
              let
                val e = on_decls (decls, e_body)
                val e = MakeELetIdx (i, unBinderName name, e)
              in
                e
              end
        end
          
and on_DVal (ename, Outer bind, r) =
    let
      val name = unBinderName ename
      val (tnames, e) = Unbound.unBind bind
      val tnames = map unBinderName tnames
      val (e, t) = case e of
                       S.EET (EETAsc, e, t) => (e, SOME t)
                     | _ => (e, NONE)
      val e = on_e e
      val e = EAbsTKind_Many (tnames, e)
      val t = Option.map (curry TUniKind_Many tnames o on_mt) t
    in
      (e, t)
    end
      
and on_DRec (name, bind, _) =
    let
      val name = unBinderName name
      val ((tnames, Rebind binds), ((pre, post), (t, i), e)) = Unbound.unBind $ unInner bind
      (* val t = t !! (fn () => raise Impossible "to-micro-timl/DRec: t must be SOME") *)
      (* val i = i !! (fn () => raise Impossible "to-micro-timl/DRec: i must be SOME") *)
      val tnames = map unBinderName tnames
      val binds = unTeles binds
      fun on_bind (bind, e) =
        case bind of
            S.SortingST (name, Outer s) => S.MakeEAbsI (unBinderName name, s, e, dummy)
          | S.TypingST pn => S.MakeEAbs (StMap.empty, pn, e)
      val e =
          case rev binds of
              S.TypingST pn :: binds =>
              foldl on_bind (S.MakeEAbs (pre, pn, e)) binds
            | _ => raise Impossible "to-micro-timl/DRec: Recursion must have a typing bind as the last bind"
      val e = on_e e
      fun on_bind_t (bind, t) =
        case bind of
            S.SortingST (name, Outer s) => S.MakeUniI (s, unBinderName name, t, dummy)
          | S.TypingST pn =>
            case pn of
                AnnoP (_, Outer t1) => S.Arrow ((StMap.empty, t1), T0 dummy, (StMap.empty, t))
              | _ => raise Impossible "to-micro-timl/DRec: must be AnnoP"
      val t = 
          case rev binds of
              S.TypingST (AnnoP (_, Outer t1)) :: binds =>
              foldl on_bind_t (S.Arrow ((pre, t1), i, (post, t))) binds
            | [] => t
            | _ => raise Impossible "to-micro-timl/DRec: Recursion must have an annotated typing bind as the last bind"
      val t = on_mt t
      val e = MakeERec (name, t, e)
      val t = TUniKind_Many (tnames, t)
      val e = EAbsTKind_Many (tnames, e)
    in
      (e, t)
    end

fun trans_e e = MicroTiMLPostProcess.post_process $ on_e e
(* val trans_decls = on_decls *)

(* fun on_mod m = *)
(*   case m of *)
(*       ModComponents (decls, _) => *)
(*       let *)
(*         val e = on_decls (decls, ETT) *)
(*         val (es, _) = collect_decls e *)
(*       in *)
(*         es *)
(*       end *)
(*     | _ => raise Unimpl "on_mod" *)

(* todo: functor application will be translated by first fibering together actual argument and formal argument, and then doing a module translation  *)
          
structure UnitTest = struct

structure U = UnderscoredExpr

open ExportPP
                
(* fun test1 dirname = *)
(*   let *)
(*     val filename = join_dir_file (dirname, "test1.timl") *)
(*     open Parser *)
(*     val prog = parse_file filename *)
(*     open Elaborate *)
(*     val prog = elaborate_prog prog *)
(*     open NameResolve *)
(*     val (prog, _, _) = resolve_prog empty prog *)
(*     val decls = case hd prog of *)
(*                     (_, TopModBind (ModComponents (decls, _))) => decls *)
(*                   | _ => raise Impossible "" *)
(*     open TypeCheck *)
(*     val ((decls, _, _, _), _) = typecheck_decls empty empty_ctx decls *)
(*     val dt = case hd decls of *)
(*                  DTypeDef (_, Outer (TDatatype (dt, _))) => dt *)
(*                | _ => raise Impossible "" *)
(*     val bind = case nth (decls, 1) of *)
(*                    DVal (_, Outer bind, _) => bind *)
(*                  | _ => raise Impossible "" *)
(*     val (_, e) = Unbound.unBind bind *)
(*     (* val dt = TypeTrans.on_dt dt *) *)
(*     val t_list = TiML.TDatatype (dt, dummy) *)
(*     val t = trans_mt t_list *)
(*     (* val () = println $ str_e empty ([], ["'a", "list"], ["Cons", "Nil"], []) e *) *)
(*     val e = SimpExpr.simp_e [("'a", KeKind Type), ("list", KeKind (1, [BSNat]))] e *)
(*     val () = println $ str_e empty ([], ["'a", "list"], ["Cons", "Nil2", "Nil"], []) e *)
(*     val () = println "" *)
(*     (* fun visit_subst_t_pn a = PatternVisitor.visit_subst_t_pn_fn (use_idepth_tdepth substx_t_mt) a *) *)
(*     val e = ExprSubst.substx_t_e (0, 1) 1 t_list e *)
(*     val e = trans_e e *)
(*     val e = export (NONE, NONE) ([], ["'a"], ["Cons", "Nil2", "Nil"], []) e *)
(*     val () = pp_e (NONE, NONE) e *)
(*     val () = println "" *)
(*   in *)
(*     ((* t, e *)) *)
(*   end *)
(*   (* handle NameResolve.Error (_, msg) => (println $ "NR.Error: " ^ msg; raise Impossible "End") *) *)
(*   (*      | TypeCheck.Error (_, msgs) => (app println $ "TC.Error: " :: msgs; raise Impossible "End") *) *)
(*   (*      | T2MTError msg => (println $ "T2MT.Error: " ^ msg; raise Impossible "End") *) *)
(*   (*      | Impossible msg => (println $ "Impossible: " ^ msg; raise Impossible "End") *) *)
                          
(* fun test2 dirname = *)
(*   let *)
(*     val filename = join_dir_file (dirname, "test2.timl") *)
(*     open Parser *)
(*     val prog = parse_file filename *)
(*     open Elaborate *)
(*     val prog = elaborate_prog prog *)
(*     open NameResolve *)
(*     val (prog, _, _) = resolve_prog empty prog *)
(*     val decls = case hd prog of *)
(*                     (_, TopModBind (ModComponents (decls, _))) => decls *)
(*                   | _ => raise Impossible "" *)
(*     open TypeCheck *)
(*     val () = TypeCheck.turn_on_builtin () *)
(*     val ((decls, _, _, _), _) = typecheck_decls empty empty_ctx decls *)
(*     val e = SMakeELet (Teles decls, Expr.ETT dummy) *)
(*     val e = SimpExpr.simp_e [] e *)
(*     val () = println $ str_e empty ToStringUtil.empty_ctx e *)
(*     val () = println "" *)
(*     val e = trans_e e *)
(*     val e = export (NONE, NONE) ToStringUtil.empty_ctx e *)
(*     val () = pp_e (NONE, NONE) e *)
(*     val () = println "" *)
(*   in *)
(*     ((* t, e *)) *)
(*   end *)
(*   handle NameResolve.Error (_, msg) => (println $ "NR.Error: " ^ msg; raise Impossible "End") *)
(*        | TypeCheck.Error (_, msgs) => (app println $ "TC.Error: " :: msgs; raise Impossible "End") *)
(*   (*      | T2MTError msg => (println $ "T2MT.Error: " ^ msg; raise Impossible "End") *) *)
(*   (*      | Impossible msg => (println $ "Impossible: " ^ msg; raise Impossible "End") *) *)

(* fun test3 dirname = *)
(*   let *)
(*     val filename = join_dir_file (dirname, "test3.timl") *)
(*     open Parser *)
(*     val prog = parse_file filename *)
(*     open Elaborate *)
(*     val prog = elaborate_prog prog *)
(*     open NameResolve *)
(*     val (prog, _, _) = resolve_prog empty prog *)
(*     open TypeCheck *)
(*     val () = TypeCheck.turn_on_builtin () *)
(*     val ((prog, _, _), _) = typecheck_prog empty prog *)
(*     open MergeModules *)
(*     val decls = merge_prog prog [] *)
(*     val e = SMakeELet (Teles decls, Expr.ETT dummy) *)
(*     val e = SimpExpr.simp_e [] e *)
(*     val () = println $ str_e empty ToStringUtil.empty_ctx e *)
(*     val () = println "" *)
(*     val e = trans_e e *)
(*     val e = export (NONE, NONE) ToStringUtil.empty_ctx e *)
(*     val () = pp_e (NONE, NONE) e *)
(*     val () = println "" *)
(*   in *)
(*     ((* t, e *)) *)
(*   end *)
(*   handle NameResolve.Error (_, msg) => (println $ "NR.Error: " ^ msg; raise Impossible "End") *)
(*        | TypeCheck.Error (_, msgs) => (app println $ "TC.Error: " :: msgs; raise Impossible "End") *)
(*   (*      | T2MTError msg => (println $ "T2MT.Error: " ^ msg; raise Impossible "End") *) *)
(*   (*      | Impossible msg => (println $ "Impossible: " ^ msg; raise Impossible "End") *) *)

fun test4 dirname =
  let
    val () = println "TiML2MicroTiML.UnitTest started"
    val filename = join_dir_file (dirname, "to-micro-timl-test4.pkg")
    val filenames = map snd $ ParseFilename.expand_pkg (fn msg => raise Impossible msg) (true, filename)
    open Parser
    val prog = concatMap parse_file filenames
    open Elaborate
    val prog = elaborate_prog prog
    open NameResolve
    val (prog, _, _) = resolve_prog empty prog
    open TypeCheck
    val () = TypeCheck.turn_on_builtin ()
    val () = println "Started typechecking ..."
    val () = TypeCheck.st_types_ref := StMap.empty
    val ((prog, _, _), _) = typecheck_prog empty prog
    val st_types = !TypeCheck.st_types_ref
    val () = println "Finished typechecking"
    open MergeModules
    val decls = merge_prog prog []
    val e = SMakeELet (Teles decls, Expr.ETT dummy)
    val () = println "Simplifying ..."
    val e = SimpExpr.simp_e [] e
    val () = println "Finished simplifying"
    (* val () = println $ str_e empty ToStringUtil.empty_ctx e *)
    (* val () = println "" *)
    val () = println "Started translating ..."
    val e = trans_e e
    val st_types = StMap.map (mapSnd trans_mt) st_types
    val () = println "Finished translating"
    val e = export (NONE, NONE) ToStringUtil.empty_ctx e
    val () = pp_e (NONE, NONE) e
    val () = println ""
    val () = println "TiML2MicroTiML.UnitTest passed"
  in
    ((* t, e *))
  end
  handle NameResolve.Error (_, msg) => (println $ "NR.Error: " ^ msg; raise Impossible "End")
       | TypeCheck.Error (_, msgs) => (app println $ "TC.Error: " :: msgs; raise Impossible "End")
  (*      | T2MTError msg => (println $ "T2MT.Error: " ^ msg; raise Impossible "End") *)
  (*      | Impossible msg => (println $ "Impossible: " ^ msg; raise Impossible "End") *)

val test_suites = [
  (* test1 *)
  (* test2 *)
  (* test3, *)
  test4
]
  
end
                             
end
