structure CompilerUtil = struct

open MicroTiMLExLocallyNameless
open MicroTiMLExUtil

infixr 0 $

fun close0_anno bind close ((x, name, anno), b) = bind (((name, dummy), anno), close x b)
fun close0_i_t_anno a = close0_anno IBindAnno close0_i_t a
fun close0_t_t_anno a = close0_anno TBindAnno close0_t_t a
fun close0_i_e_anno a = close0_anno IBindAnno close0_i_e a
fun close0_t_e_anno a = close0_anno TBindAnno close0_t_e a
fun close0_e_e_anno a = close0_anno EBindAnno close0_e_e a

structure ExportPP = struct

open LongId
open Util
open MicroTiML
open MicroTiMLVisitor
open MicroTiMLExLongId
open MicroTiMLEx
       
infixr 0 $
infixr 0 !!
         
fun short_to_long_id x = ID (x, dummy)
fun export_var sel ctx id =
  let
    fun unbound s = "__unbound_" ^ s
    (* fun unbound s = raise Impossible $ "Unbound identifier: " ^ s *)
  in
    case id of
        ID (x, _) =>
        short_to_long_id $ nth_error (sel ctx) x !! (fn () => unbound $ str_int x)
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
fun pp_t_to_string b = MicroTiMLPP.pp_t_to_string_fn (str_var, str_bs, str_i, str_s, const_fun "<kind>") b
fun pp_e_to_string a = MicroTiMLExPP.pp_e_to_string_fn (
    str_var,
    str_i,
    str_s,
    const_fun "<kind>",
    pp_t_to
  ) a

end

fun assert_fail msg = Impossible $ "Assert failed: " ^ msg
                             
fun assert_TArrow t =
  case t of
      TArrow a => a
    | _ => raise assert_fail $ "assert_TArrow; got: " ^ (ExportPP.pp_t_to_string NONE $ ExportPP.export_t ([], []) t)
                 
fun assert_EAbs e =
  case e of
      EAbs bind => unBindAnnoName bind
    | _ => raise assert_fail "assert_EAbs"
                 
fun assert_EAscType e =
  let
    val (e, is) = collect_EAscTime e
  in
    case e of
        EAscType (e, t) => (EAscTimes (e, is), t)
      | _ => raise assert_fail $ "assert_EAscType; got:\n" ^ (ExportPP.pp_e_to_string (NONE, NONE) $ ExportPP.export ([], [], [], []) e)
  end
    
fun assert_EAscTime e =
  let
    val (e, ts) = collect_EAscType e
  in
    case e of
        EAscTime (e, i) => (EAscTypes (e, ts), i)
      | _ => raise assert_fail $ "assert_EAscTime; got:\n" ^ (ExportPP.pp_e_to_string (NONE, NONE) $ ExportPP.export ([], [], [], []) e)
  end
    
fun EV x = EVar $ make_Free_e x
                
fun ELetClose ((x, name, e1), e2) = MakeELet (e1, (name, dummy), close0_e_e x e2)
fun ELetManyClose (ds, e) = foldr ELetClose e ds

fun EAbsPairClose ((x1, name1, t1), (x2, name2, t2), e) =
  let
    val x = fresh_evar ()
    val e = ELetClose ((x2, name2, ESnd (EV x)), e)
    val e = ELetClose ((x1, name1, EFst (EV x)), e)
  in
    EAbs $ close0_e_e_anno ((x, "x", TProd (t1, t2)), e)
  end
    
fun EUnpackClose (e1, (a, name_a), (x, name_x), e2) =
  EUnpack (e1, curry TBind (name_a, dummy) $ curry EBind (name_x, dummy) $ close0_t_e a $ close0_e_e x e2)
fun EUnpackIClose (e1, (a, name_a), (x, name_x), e2) =
    EUnpackI (e1, curry IBind (name_a, dummy) $ curry EBind (name_x, dummy) $ close0_i_e a $ close0_e_e x e2)
             
fun ECaseClose (e, ((x1, name1), e1), ((x2, name2), e2)) =
    ECase (e, EBind ((name1, dummy), close0_e_e x1 e1), EBind ((name2, dummy), close0_e_e x2 e2))
          
fun EAppIT (e, arg) =
    case arg of
        inl i => EAppI (e, i)
      | inr t => EAppT (e, t)
fun EAppITs (f, args) = foldl (swap EAppIT) f args
                     
fun EAbsIT (bind, e) =
    case bind of
        inl bind => EAbsI $ IBindAnno (bind, e)
      | inr bind => EAbsT $ TBindAnno (bind, e)
fun EAbsITs (binds, e) = foldr EAbsIT e binds
                                      
fun EAscTypeTime (e, arg) =
    case arg of
        inr i => EAscTime (e, i)
      | inl t => EAscType (e, t)
fun EAscTypeTimes (f, args) = foldl (swap EAscTypeTime) f args
                     
fun open_collect_TForallIT_whnf whnf t =
  case t of
      TQuanI (Forall, bind) =>
      let
        val (s, (name, t)) = unBindAnnoName bind
        val x = fresh_ivar ()
        val t = open0_i_t x t
        val (binds, t) = open_collect_TForallIT_whnf whnf t
      in
        (inl (x, fst name, s) :: binds, t)
      end
    | TQuan (Forall, bind) =>
      let
        val (k, (name, t)) = unBindAnnoName bind
        val x = fresh_tvar ()
        val t = open0_t_t x t
        val (binds, t) = open_collect_TForallIT_whnf whnf t
      in
        (inr (x, fst name, k) :: binds, t)
      end
    | _ => ([], t)

fun collect_TForallIT_open_with_whnf whnf vars t =
  case t of
      TQuanI (Forall, bind) =>
      let
        val (s, (name, t)) = unBindAnnoName bind
        val (x, vars) = case vars of
                    inl (x, _, _) :: vars => (x, vars)
                  | _ => raise Impossible "collect_TForallIT_open_with_whnf whnf"
        val t = open0_i_t x t
        val (binds, t) = collect_TForallIT_open_with_whnf whnf vars t
      in
        (inl (x, fst name, s) :: binds, t)
      end
    | TQuan (Forall, bind) =>
      let
        val (k, (name, t)) = unBindAnnoName bind
        val (x, vars) = case vars of
                    inr (x, _, _) :: vars => (x, vars)
                  | _ => raise Impossible "collect_TForallIT_open_with_whnf whnf"
        val t = open0_t_t x t
        val (binds, t) = collect_TForallIT_open_with_whnf whnf vars t
      in
        (inr (x, fst name, k) :: binds, t)
      end
    | _ => ([], t)

fun open_collect_TForallIT t = open_collect_TForallIT_whnf id t
fun collect_TForallIT_open_with vars t = collect_TForallIT_open_with_whnf id vars t
    
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
    val mark_begin = "__$begin$_"
    val len_mark_begin = String.size mark_begin
    val mark_end = #"$"
    val default_fun_name = "__f"
    fun visit_EAbs this env bind =
      let
        val (t_y, ((name_y, r), e)) = unBindAnnoName bind
        val () = println $ "visit_EAbs()/name_y: " ^ name_y
        val (fun_name, name_y) =
            if String.isPrefix mark_begin name_y then
              (case String.fields (curry op= mark_end) $ String.extract (name_y, len_mark_begin, NONE) of
                   [fun_name, name_y] => (fun_name, name_y)
                 | _ => (default_fun_name, name_y)
              )
            else (default_fun_name, name_y)
        val ((_, t_e), i) = mapFst assert_EAscType $ assert_EAscTime e
        val e = #visit_expr (cast this) this env e
        val e = EAbs $ EBindAnno (((name_y, r), t_y), e)
      in
        ERec $ EBindAnno (((fun_name, dummy), TArrow (t_y, i, t_e)), shift01_e_e e)
      end
    fun visit_ELet this env (data as (e1, bind)) =
        let
          val ((name_x, _), _) = unBindSimpName bind
          val (e1, ascs) = collect_EAscTypeTime e1
          val (binds, e1) = collect_EAbsIT e1
          val e1 = 
              case e1 of
                  EAbs bind1 =>
                  let
                    val (t_y, ((name_y, r), e1)) = unBindAnnoName bind1
                  in
                    EAbs $ EBindAnno (((mark_begin ^ name_x ^ String.str mark_end ^ name_y, r), t_y), e1)
                  end
                | _ => e1
          val e1 = EAbsITs (binds, e1)
          val e1 = EAscTypeTimes (e1, ascs)
        in
          (* call super *)
          #visit_ELet vtable this env (e1, bind)
        end
    val vtable = override_visit_ERec vtable visit_ERec
    val vtable = override_visit_EAbs vtable visit_EAbs
    val vtable = override_visit_ELet vtable visit_ELet
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

fun reduce_ELets e =
    case fst $ collect_EAscTypeTime e of
        ELet (e1, bind) =>
        let
          val (name_x, e2) = unBindSimpName bind
        in
          reduce_ELets $ subst0_e_e e1 e2
        end
      | _ => e
               
end
