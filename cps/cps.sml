(* Continuation-Passing-Style (CPS) Conversion *)

structure CPS = struct

open Expr
open MicroTiMLExLongId
open MicroTiMLExLocallyNameless
open MicroTiMLExUtil
open MicroTiMLEx
structure S = MicroTiMLEx

infixr 0 $
infixr 0 $$

infix 6 %+ 
         
fun IV x = VarI $ Free x
fun EV x = EVar $ Free x
val T_0 = T0 dummy
val T_1 = T1 dummy

fun unBindAnno2 data =
  let
    val ((name, anno), t) = unBindAnno data
    val name = Name2str name
  in
    ((name, anno), t)
  end

fun unBindSimp2 bind = mapFst Name2str $ unBindSimp bind
            
fun close0_anno bind close ((x, name, anno), b) = bind (((name, dummy), anno), close x b)
fun close0_i_t_anno a = close0_anno IBindAnno close0_i_t a
fun close0_t_t_anno a = close0_anno TBindAnno close0_t_t a
fun close0_i_e_anno a = close0_anno IBindAnno close0_i_e a
fun close0_t_e_anno a = close0_anno TBindAnno close0_t_e a
fun close0_e_e_anno a = close0_anno EBindAnno close0_e_e a

fun TForallTimeClose ((x, name), t) = TForallI $ close0_i_t_anno ((x, name, STime), t)
fun ELetClose ((x, name, e1), e2) = MakeELet (e1, (name, dummy), close0_e_e x e2)
fun EAbsPairClose (((x1, name1, t1), (x2, name2, t2)), e) =
  let
    val x = fresh_evar ()
    val e = ELetClose ((x2, name2, ESnd (EV x)), e)
    val e = ELetClose ((x1, name1, ESnd (EV x)), e)
  in
    EAbs $ close0_e_e_anno ((x, "x", TProd (t1, t2)), e)
  end
fun EAbsTimeClose ((x, name), e) = EAbsI $ close0_i_e_anno ((x, name, STime), e)
fun ECaseClose (e, ((x1, name1), e1), ((x2, name2), e2)) =
  ECase (e, EBind ((name1, dummy), close0_e_e x1 e1), EBind ((name2, dummy), close0_e_e x2 e2))
fun EUnpackClose (e1, (a, name_a), (x, name_x), e2) =
  EUnpack (e1, curry TBind (name_a, dummy) $ curry EBind (name_x, dummy) $ close0_t_e a $ close0_e_e x e2)
fun ELetConstrClose ((x, name), e1, e2) = MakeELetConstr (e1, (name, dummy), close0_c_e x e2)
  
fun Eid t = EAbs $ EBindAnno ((("x", dummy), t), EVar $ Bound 0)
        
fun a $$ b = EApp (a, b)

fun assert_fail msg = Impossible $ "Assert failed: " ^ msg
                             
fun assert_TArrow t =
  case t of
      TArrow a => a
    | _ => raise assert_fail "assert_TArrow"
fun assert_TProd t =
  case t of
      TBinOp (TBProd, t1, t2) => (t1, t2)
    | _ => raise assert_fail "assert_TProd"
fun assert_TSum t =
  case t of
      TBinOp (TBSum, t1, t2) => (t1, t2)
    | _ => raise assert_fail "assert_TSum"
fun assert_TAbsT t =
  case t of
      TAbsT bind => unBindAnno bind
    | _ => raise assert_fail "assert_TAbsT"
fun assert_EAscType e =
  case e of
      EAscType a => a
    | _ => raise assert_fail "assert_EAscType"

fun assert_and_reduce_beta e =
  case e of
      EBinOp (EBApp, EAbs bind, e2) =>
      let
        val (_, e1) = unBindAnno bind
      in
        subst0_e_e e2 e1
      end
    | _ => raise assert_fail "assert_and_reduce_beta"

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

fun blowup_time (i : idx, j : idx) = i
fun blowup_time_t (j : idx) = j
  
(* CPS conversion on types *)
fun cps_t t =
  case t of
      TArrow (t1, i, t2) =>
      let
        val t1 = cps_t t1
        val t2 = cps_t t2
        val j = fresh_ivar ()
        val t = TProd (t1, TArrow (t2, IV j, TUnit))
        val t = TArrow (t, blowup_time (i, IV j), TUnit)
      in
        TForallTimeClose ((j, "j"), t)
      end
    | TQuan (Forall, bind) =>
      let
        val ((name_alpha, kd_alpha), t) = unBindAnno2 bind
        val alpha = fresh_tvar ()
        val t = open0_t_t alpha t
        val t = cps_t t
        val j = fresh_ivar ()
        val t = TArrow (t, IV j, TUnit)
        val t = TArrow (t, IV j %+ T_1, TUnit)
        val t = TForallTimeClose ((j, "j"), t)
      in
        TForall $ close0_t_t_anno ((alpha, name_alpha, kd_alpha), t)
      end
    | TVar _ => t
    | TConst _ => t
    | _ => raise Unimpl "cps_t"

fun cont_type (t, i) = TArrow (t, i, TUnit)

(* CPS conversion on terms *)
(* pre: ... |- k : [[t_e]] --j_k-=> unit |> 0 *)
(* the 'unit' part can be relaxed if e is a value *)
fun cps (e, t_e) (k, j_k) =
  case e of
      S.EVar x =>
      (* [[ x ]](k) = k x *)
      (k $$ EVar x, j_k %+ T_1)
    | S.EAbs bind =>
      (* [[ \x.e ]](k) = k (\\j. \(x, c). [[e]](c) |> blowup_time(i, j))
         where [i] is the time bound of [e], blowup_time(i,j) = b(i+1)+2i+1+j, [b] is blow-up factor *)
      let
        val ((name_x, _), e) = unBindAnno2 bind
        val (t_x, i, t_e) = assert_TArrow t_e
        val x = fresh_evar ()
        val e = open0_e_e x e
        val c = fresh_evar ()
        val j = fresh_ivar ()
        val (e, _) = cps (e, t_e) (EV c, IV j)
        val e = EAscTime (e, blowup_time (i, IV j))
        val t_e = cps_t t_e
        val t_c = cont_type (t_e, IV j)
        val t_x = cps_t t_x
        val e = EAbsPairClose (((x, name_x, t_x), (c, "c", t_c)), e)
        val e = EAbsTimeClose ((j, "j"), e)
      in
        (k $$ e, j_k %+ T_1)
      end
    | S.EBinOp (EBApp, e1, e2) =>
      (* [[ e1 e2 ]](k) = [[e1]] (\x1. [[e2]] (\x2. x1 {k.j} (x2, k))) *)
      let
        val (e1, t_e1) = assert_EAscType e1
        val (t_e2, i, _) = assert_TArrow t_e1
        val x1 = fresh_evar ()
        val x2 = fresh_evar ()
        val e = EAppI (EV x1, j_k) $$ EPair (EV x2, k)
        val t_x2 = cps_t t_e2
        val e = EAbs $ close0_e_e_anno ((x2, "x2", t_x2), e)
        val (e, i_e) = cps (e2, t_e2) (e, blowup_time (i, j_k))
        val t_x1 = cps_t t_e1
        val e = EAbs $ close0_e_e_anno ((x1, "x1", t_x1), e)
      in
        cps (e1, t_e1) (e, i_e)
      end
    | S.EConst c =>
      (* [[ x ]](c) = k c *)
      (k $$ EConst c, j_k %+ T_1)
    | S.ERec bind =>
      (* [[ fix x.e ]](k) = k (fix x. [[e]](id)) *)
      let
        val ((name_x, _), e) = unBindAnno2 bind
        val x = fresh_evar ()
        val e = open0_e_e x e
        val t_x = cps_t t_e
        val () = assert_b "cps/ERec/1" $ is_value e
        val (e, i_e) = cps (e, t_e) (Eid t_x, T_0) (* CPS with id is not strictly legal, since id doesn't return unit. It's OK because e should be a value. Values can be CPSed with continuations that return non-unit. *)
        val e = assert_and_reduce_beta e
        val () = assert_b "cps/ERec/2" $ is_value e
        val e = ERec $ close0_e_e_anno ((x, name_x, t_x), e)
      in
        (k $$ e, j_k %+ T_1)
      end
    | S.EAbsT bind =>
      (* [[ \\alpha.e ]](k) = k (\\alpha. \\j. \c. [[e]](c)) *)
      let
        val ((name_alpha, kd_alpha), e) = unBindAnno2 bind
        val (_, t_e) = assert_TAbsT t_e
        val alpha = fresh_tvar ()
        val e = open0_t_e alpha e
        val t_e = open0_t_t alpha t_e
        val j = fresh_ivar ()
        val c = fresh_evar ()
        val () = assert_b "cps/EAbsT" $ is_value e
        val (e, _) = cps (e, t_e) (EV c, IV j)
        val e = EAscTime (e, blowup_time_t (IV j))
        val t_e = cps_t t_e
        val t_c = cont_type (t_e, IV j)
        val e = EAbs $ close0_e_e_anno ((c, "c", t_c), e)
        val e = EAbsTimeClose ((j, "j"), e)
        val e = EAbsT $ close0_t_e_anno ((alpha, name_alpha, kd_alpha), e)
      in
        (k $$ e, j_k %+ T_1)
      end
    | S.EAppT (e, t) =>
      (* [[ e[t] ]](k) = [[e]](\x. x[t]{k.j}(k)) *)
      let
        val (e, t_e) = assert_EAscType e
        val x = fresh_evar ()
        val c = EAppI (EAppT (EV x, t), j_k) $$ k
        val t_x = cps_t t_e
        val c = EAbs $ close0_e_e_anno ((x, "x", t_x), c)
      in
        cps (e, t_e) (c, blowup_time_t j_k)
      end
    | S.EUnOp (EUFold t_fold, e) =>
      (* [[ fold e ]](k) = [[e]](\x. k (fold x)) *)
      let
        val (e, t_e) = assert_EAscType e
        val x = fresh_evar ()
        val t_fold = cps_t t_fold
        val c = EFold (t_fold, EV x)
        val c = k $$ c
        val t_x = cps_t t_e
        val c = EAbs $ close0_e_e_anno ((x, "x", t_x), c)
      in
        cps (e, t_e) (c, j_k %+ T_1)
      end
    | S.EUnOp (EUUnfold, e) =>
      (* [[ unfold e ]](k) = [[e]](\x. k (unfold x)) *)
      let
        val (e, t_e) = assert_EAscType e
        val x = fresh_evar ()
        val c = EUnfold (EV x)
        val c = k $$ c
        val t_x = cps_t t_e
        val c = EAbs $ close0_e_e_anno ((x, "x", t_x), c)
      in
        cps (e, t_e) (c, j_k %+ T_1)
      end
    | S.EPack (t_pack, t, e) =>
      (* [[ pack <t, e> ]](k) = [[e]](\x. k (pack <t, x>)) *)
      let
        val (e, t_e) = assert_EAscType e
        val x = fresh_evar ()
        val t_pack = cps_t t_pack
        val t = cps_t t
        val c = EPack (t_pack, t, EV x)
        val c = k $$ c
        val t_x = cps_t t_e
        val c = EAbs $ close0_e_e_anno ((x, "x", t_x), c)
      in
        cps (e, t_e) (c, j_k %+ T_1)
      end
    | S.EUnpack (e1, bind) =>
      (* [[ unpack e1 as <alpha, x> in e2 ]](k) = [[e1]](\x1. unpack x1 as <alpha, x> in [[e2]](k)) *)
      let
        val (e1, t_e1) = assert_EAscType e1
        val (name_alpha, e2) = unBindSimp2 bind
        val (name_x, e2) = unBindSimp2 e2
        val alpha = fresh_tvar ()
        val x = fresh_evar ()
        val e2 = open0_t_e alpha e2
        val e2 = open0_e_e x e2
        val x1 = fresh_evar ()
        val t_e2 = t_e
        val (c, i_c) = cps (e2, t_e2) (k, j_k)
        val c = EUnpackClose (EV x1, (alpha, name_alpha), (x, name_x), c)
        val t_x1 = cps_t t_e1
        val c = EAbs $ close0_e_e_anno ((x1, "x1", t_x1), c)
      in
        cps (e1, t_e1) (c, i_c)
      end
    | S.EBinOp (EBPair, e1, e2) =>
      (* [[ (e1, e2) ]](k) = [[e1]] (\x1. [[e2]] (\x2. k (x1, x2))) *)
      let
        val (t_e1, t_e2) = assert_TProd t_e
        val x1 = fresh_evar ()
        val x2 = fresh_evar ()
        val t_x1 = cps_t t_e1
        val t_x2 = cps_t t_e2
        val e = k $$ EPair (EV x1, EV x2)
        val e = EAbs $ close0_e_e_anno ((x2, "x2", t_x2), e)
        val (e, i_e) = cps (e2, t_e2) (e, j_k %+ T_1)
        val e = EAbs $ close0_e_e_anno ((x1, "x1", t_x1), e)
      in
        cps (e1, t_e1) (e, i_e)
      end
    | S.EUnOp (EUProj proj, e) =>
      (* [[ e.p ]](k) = [[e]](\x. k (x.p)) *)
      let
        val (e, t_e) = assert_EAscType e
        val x = fresh_evar ()
        val c = EUnOp (EUProj proj, EV x)
        val c = k $$ c
        val t_x = cps_t t_e
        val c = EAbs $ close0_e_e_anno ((x, "x", t_x), c)
      in
        cps (e, t_e) (c, j_k %+ T_1)
      end
    | S.EUnOp (EUInj (inj, t_other), e) =>
      (* [[ l.e ]](k) = [[e]](\x. k (l.x)) *)
      let
        val t1_t2 = assert_TSum t_e
        val t_e = choose_inj t1_t2 inj
        val x = fresh_evar ()
        val t_other = cps_t t_other
        val c = EUnOp (EUInj (inj, t_other), EV x)
        val c = k $$ c
        val t_x = cps_t t_e
        val c = EAbs $ close0_e_e_anno ((x, "x", t_x), c)
      in
        cps (e, t_e) (c, j_k %+ T_1)
      end
    | S.ECase (e, bind1, bind2) =>
      (* [[ case e (x.e1) (x.e2) ]](k) = [[e]](\y. case y (x. [[e1]](k)) (x. [[e2]](k))) *)
      let
        val (name_x_1, e1) = unBindSimp2 bind1
        val (name_x_2, e2) = unBindSimp2 bind2
        val x = fresh_evar ()
        val e1 = open0_e_e x e1
        val e2 = open0_e_e x e2
        val t_res = t_e
        val (e, t_e) = assert_EAscType e
        val t_res = cps_t t_res
        val (e1, i_e1) = cps (e1, t_res) (k, j_k)
        val (e2, i_e2) = cps (e2, t_res) (k, j_k)
        val y = fresh_evar ()
        val c = ECaseClose (EV y, ((x, name_x_1), e1), ((x, name_x_2), e2))
        val t_y = cps_t t_e
        val c = EAbs $ close0_e_e_anno ((y, "y", t_y), c)
        val i_c = IMax (i_e1, i_e2)
      in
        cps (e, t_e) (c, i_c)
      end
    | S.ELet (e1, bind) =>
      (* [[ let x = e1 in e2 ]](k) = [[e1]](\x. [[e2]](k)) *)
      let
        val (e1, t_e1) = assert_EAscType e1
        val t_res = t_e
        val (name_x, e2) = unBindSimp2 bind
        val x = fresh_evar ()
        val e2 = open0_e_e x e2
        val (c, i_c) = cps (e2, t_res) (k, j_k)
        val t_x = cps_t t_e1
        val c = EAbs $ close0_e_e_anno ((x, name_x, t_x), c)
      in
        cps (e1, t_e1) (c, i_c)
      end
    | S.EAscType (e, t) =>
      cps (e, t) (k, j_k)  (* todo: may need to do more *)
    | S.EAscTime (e, i) =>
      cps (e, t_e) (k, j_k) (* todo: may need to do more *)
    | S.EBinOp (EBPrim opr, e1, e2) =>
      (* [[ e1 o e2 ]](k) = [[e1]] (\x1. [[e2]] (\x2. k (x1 o x2))) *)
      let
        val (e1, t_e1) = assert_EAscType e1
        val (e2, t_e2) = assert_EAscType e2
        val x1 = fresh_evar ()
        val x2 = fresh_evar ()
        val t_x1 = cps_t t_e1
        val t_x2 = cps_t t_e2
        val e = k $$ EBinOp (EBPrim opr, EV x1, EV x2)
        val e = EAbs $ close0_e_e_anno ((x2, "x2", t_x2), e)
        val (e, i_e) = cps (e2, t_e2) (e, j_k %+ T_1)
        val e = EAbs $ close0_e_e_anno ((x1, "x1", t_x1), e)
      in
        cps (e1, t_e1) (e, i_e)
      end
    | S.EBinOp (EBRead, e1, e2) =>
      (* [[ read e1 e2 ]](k) = [[e1]] (\x1. [[e2]] (\x2. k (read x1 x2))) *)
      let
        val (e1, t_e1) = assert_EAscType e1
        val (e2, t_e2) = assert_EAscType e2
        val x1 = fresh_evar ()
        val x2 = fresh_evar ()
        val t_x1 = cps_t t_e1
        val t_x2 = cps_t t_e2
        val e = k $$ EBinOp (EBRead, EV x1, EV x2)
        val e = EAbs $ close0_e_e_anno ((x2, "x2", t_x2), e)
        val (e, i_e) = cps (e2, t_e2) (e, j_k %+ T_1)
        val e = EAbs $ close0_e_e_anno ((x1, "x1", t_x1), e)
      in
        cps (e1, t_e1) (e, i_e)
      end
    | S.EWrite (e1, e2, e3) =>
      (* [[ write e1 e2 e3 ]](k) = [[e1]] (\x1. [[e2]] (\x2. [[e3]] (\x3. k (write x1 x2 x3)))) *)
      let
        val (e1, t_e1) = assert_EAscType e1
        val (e2, t_e2) = assert_EAscType e2
        val (e3, t_e3) = assert_EAscType e3
        val x1 = fresh_evar ()
        val x2 = fresh_evar ()
        val x3 = fresh_evar ()
        val t_x1 = cps_t t_e1
        val t_x2 = cps_t t_e2
        val t_x3 = cps_t t_e3
        val e = k $$ EWrite (EV x1, EV x2, EV x3)
        val e = EAbs $ close0_e_e_anno ((x3, "x3", t_x3), e)
        val (e, i_e) = cps (e3, t_e3) (e, j_k %+ T_1)
        val e = EAbs $ close0_e_e_anno ((x2, "x2", t_x2), e)
        val (e, i_e) = cps (e2, t_e2) (e, i_e)
        val e = EAbs $ close0_e_e_anno ((x1, "x1", t_x1), e)
      in
        cps (e1, t_e1) (e, i_e)
      end
    (* extensions from MicroTiML *)
    | S.ELetConstr (e1, bind) =>
      (* [[ let constr x = e1 in e2 ]](k) = [[e1]](\y. let constr x = y in [[e2]](k)) *)
      let
        val (e1, t_e1) = assert_EAscType e1
        val t_res = t_e
        val (name_x, e2) = unBindSimp2 bind
        val x = fresh_cvar ()
        val e2 = open0_c_e x e2
        val (c, i_c) = cps (e2, t_res) (k, j_k)
        val y = fresh_evar ()
        val c = ELetConstrClose ((x, name_x), EV y, c)
        val t_y = cps_t t_e1
        val c = EAbs $ close0_e_e_anno ((y, "y", t_y), c)
      in
        cps (e1, t_e1) (c, i_c)
      end
    | _ =>
      let
        val s = (* substr 0 100 $  *)ExportPP.pp_e_to_string $ ExportPP.export ([], [], [], []) e
      in
        raise Unimpl $ "cps() on: " ^ s
      end
      
end

structure CPSUnitTest = struct

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

infixr 0 $
infixr 0 !!
         
fun test1 dirname =
  let
    val filename = join_dir_file (dirname, "cps-test1.pkg")
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
    val () = pp_e $ export ToStringUtil.empty_ctx e
    val () = println ""
                     
    open MicroTiMLTypecheck
    open TestUtil
    val () = println "Started MicroTiML typechecking #1 ..."
    val ((t, i), vcs, admits) = typecheck ([], [], [], HeapMap.empty) e
    val () = println "Finished MicroTiML typechecking #1"
    val () = println "Type:"
    val () = pp_t $ export_t ([], []) t
    val () = println "Time:"
    val i = simp_i i
    val () = println $ ToString.str_i Gctx.empty [] i
    (* val () = println $ "#VCs: " ^ str_int (length vcs) *)
    (* val () = println "VCs:" *)
    (* val () = app println $ concatMap (fn ls => ls @ [""]) $ map (str_vc false "") vcs *)
                     
    val () = println "Started CPS conversion ..."
    val (e, _) = cps (e, TUnit) (Eid TUnit, T_0)
    val () = println "Finished CPS conversion ..."
    val () = pp_e $ export ToStringUtil.empty_ctx e
    val () = println ""
    val () = println "Started MicroTiML typechecking #2 ..."
    val ((t, i), vcs, admits) = typecheck ([], [], [], HeapMap.empty) e
    val () = println "Finished MicroTiML typechecking #2"
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
