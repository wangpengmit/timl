(* Continuation-Passing-Style (CPS) Conversion *)

structure CPS = struct

open MicroTiMLExUtil
open MicroTiMLEx
structure S = MicroTiMLEx

fun fresh_ivar () = ()

fun IV x = ()

fun blowup_time (i, j) = i
  
(* CPS conversion on types *)
fun cps_t t =
  case t of
      TArrow (t1, i, t2) =>
      let
        val t1 = cps_t t1
        val t2 = cps_t t2
        val j = fresh_ivar ()
        val t = TProd (t1, TArrow (t2, IV j, TUnit))
        val t = TArrow (t, blowup_time (i, j), TUnit)
      in
        TForallTime ((j, "j"), t)
      end
    | TQuan (Forall, bind) =>
      let
        val ((name_alpha, kd_alpha), t) = unBindAnno bind
        val alpha = fresh_tvar ()
        val t = open_t_t alpha t
        val t = cps_t t
        val j = fresh_ivar ()
        val t = TArrow (t, IV j, TUnit)
        val t = TArrow (t, IV j %+ T1, TUnit)
        val t = TForallTime ((j, "j"), t)
      in
        TForall $ close_t_t_anno ((alpha, name_alpha, kd_alpha), t)
      end
    | TVar _ => t
    | TConst _ => t
    | _ => raise "Unimpl"

(* CPS conversion on terms *)
(* pre: ... |- k : [[t_e]] --j_k-=> unit |> 0 *)
(* the 'unit' part can be relaxed if e is a value *)
fun cps (e, t_e) (k, j_k) =
  case e of
      S.EVar x =>
      (* [[ x ]](k) = k x *)
      (k $$ EV x, j_k %+ T1)
    | S.EAbs bind =>
      (* [[ \x.e ]](k) = k (\\j. \(x, c). [[e]](c) |> blowup_time(i, j))
         where [i] is the time bound of [e], blowup_time(i,j) = b(i+1)+2i+1+j, [b] is blow-up factor *)
      let
        val ((name_x, _), e) = unBindAnno bind
        val (t_x, i, t_e) = assert_TArrow t_e
        val x = fresh_evar ()
        val e = open_e_e x e
        val c = fresh_evar ()
        val j = fresh_ivar ()
        val (e, _) = cps (e, t_e) (EV c, IV j)
        val e = EAscTime (e, blowup_time (i, j))
        val t_e = cps_t t_e
        val t_c = cont_type (t_e, j)
        val t_x = cps_t t_x
        val e = EAbsTuple ([(x, name_x, t_x), (c, "c", t_c)], e)
        val e = EAbsTime ((j, "j"), e)
      in
        (k $$ e, j_k %+ T1)
      end
    | S.EBinOp (EBApp, e1, e2) =>
      (* [[ e1 e2 ]](k) = [[e1]] (\x1. [[e2]] (\x2. x1 {k.j} (x2, k))) *)
      let
        val (e1, t_e1) = assert_EAsc e1
        val (t_e2, i, _) = assert_TArrow t_e1
        val x1 = fresh_evar ()
        val x2 = fresh_evar ()
        val e = EAppTuple (EAppI (EV x1, IV j_k), [EV x2, EV k])
        val t_x2 = cps_t t_e2
        val e = EAbs $ close_e_e_anno ((x2, "x2", t_x2), e)
        val (e, i_e) = cps (e2, t_e2) (e, blowup_time (i, j_k))
        val t_x1 = cps_t t_e1
        val e = EAbs $ close_e_e_anno ((x1, "x1", t_x1), e)
      in
        cps (e1, t_e1) (e, i_e)
      end
    | S.EConst c =>
      (* [[ x ]](c) = k c *)
      (k $$ EConst c, j_k %+ T1)
    | S.ERec bind =>
      (* [[ fix x.e ]](k) = k (fix x. [[e]](id)) *)
      let
        val ((name_x, _), e) = unBindAnno bind
        val x = fresh_evar ()
        val e = open_e_e x e
        val t_e = t
        val t_x = cps_t t_e
        val () = assert $ is_value e
        val (e, i_e) = cps (e, t_e) (Eid t_x, T0) (* CPS with id is not strictly legal, since id doesn't return unit. It's OK because e should be a value. Values can be CPSed with continuations that return non-unit. *)
        val e = assert_beta e
        val () = assert $ is_value e
        val e = ERec $ close_e_e_anno ((x, name_x, t_x), e)
      in
        (k $$ e, j_k %+ T1)
      end
    | S.EAbsT bind =>
      (* [[ \\alpha.e ]](k) = k (\\alpha. \\j. \c. [[e]](c)) *)
      let
        val ((name_alpha, kd_alpha), e) = unBindAnno bind
        val (_, t_e) = assert_TAbsT t_e
        val alpha = fresh_tvar ()
        val e = open_t_e alpha e
        val t_e = open_t_t alpha t_e
        val j = fresh_ivar ()
        val c = fresh_evar ()
        val () = assert $ is_value e
        val (e, _) = cps (e, t_e) (EV c, IV j)
        val e = EAscTime (e, blowup_time_t j)
        val t_e = cps_t t_e
        val t_c = cont_type (t_e, j)
        val e = EAbs $ close_e_e_anno ((c, "c", t_c), e)
        val e = EAbsTime ((j, "j"), e)
        val e = EAbsT $ close_t_e_anno ((alpha, name_alpha, kd_alpha), e)
      in
        (k $$ e, j_k %+ T1)
      end
    | S.AppT (e, i) =>
      (* [[ e[t] ]](k) = [[e]](\x. x[t]{k.j}(k)) *)
      let
        val (e, t_e) = assert_EAsc e
        val (t_e2, i, _) = assert_TArrow t_e1
        val x = fresh_evar ()
        val c = EAppI (EAppT (EV x, t), IV j_k) $$ k
        val t_x = cps_t t_e
        val c = EAbs $ close_e_e ((x, "x", t_x), c)
      in
        cps (e, t_e) (c, blowup_time_t j)
      end
    | S.EUnOp (EUFold t_fold, e) =>
      (* [[ fold e ]](k) = [[e]](\x. k (fold x)) *)
      let
        val (e, t_e) = assert_EAsc e
        val x = fresh_evar ()
        val t_fold = cps_t t_fold
        val c = EFold (t_fold, EV x)
        val c = k $$ c
        val t_x = cps_t t_e
        val c = EAbs $ close_e_e_anno ((x, "x", t_x), c)
      in
        cps (e, t_e) (c, j_k %+ T1)
      end
    | S.EUnOp (EUUnfold, e) =>
      (* [[ unfold e ]](k) = [[e]](\x. k (unfold x)) *)
      let
        val (e, t_e) = assert_EAsc e
        val x = fresh_evar ()
        val c = EUnfold (EV x)
        val c = k && c
        val t_x = cps_t t_e
        val c = EAbs $ close_e_e_anno ((x, "x", t_x), c)
      in
        cps (e, t_e) (c, j_k %+ T1)
      end
    | S.EPack (t_pack, t, e) =>
      (* [[ pack <t, e> ]](k) = [[e]](\x. k (pack <t, x>)) *)
      let
        val (e, t_e) = assert_EAsc e
        val x = fresh_evar ()
        val t_pack = cps_t t_pack
        val t = cps_t t
        val c = EPack (t_pack, t, EV x)
        val c = k $$ c
        val t_x = cps_t t_e
        val c = EAbs $ close_e_e_anno ((x, "x", t_x), c)
      in
        cps (e, t_e) (c, j_k %+ T1)
      end
    | S.EUnpack (e1, bind) =>
      (* [[ unpack e1 as <alpha, x> in e2 ]](k) = [[e1]](\x1. unpack x1 as <alpha, x> in [[e2]](k)) *)
      let
        val (e1, t_e1) = assert_EAsc e1
        val (name_alpha, e2) = unBind e2
        val (name_x, e2) = unBind e2
        val alpha = fresh_tvar ()
        val x = fresh_evar ()
        val e2 = open_t_e alpha e2
        val e2 = open_e_e x e2
        val x1 = fresh_evar ()
        val t_e2 = t_e
        val (c, i_c) = cps (e2, t_e2) (k, j)
        val c = EUnpackClose (EV x1, (alpha, name_alpha), (x, name_x), c)
        val t_x1 = cps_t t_e1
        val c = EAbs $ close_e_e_anno ((x1, "x1", t_x1), c)
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
        val e = EAppTuple (k, [EV x1, EV x2])
        val e = EAbs $ close_e_e_anno ((x2, "x2", t_x2), e)
        val (e, i_e) = cps (e2, t_e2) (e, j_k %+ T1)
        val e = EAbs $ close_e_e_anno ((x1, "x1", t_x1), e)
      in
        cps (e1, t_e1) (e, i_e)
      end
    | S.EUnOp (EUProj proj, e) =>
      (* [[ e.p ]](k) = [[e]](\x. k (x.p)) *)
      let
        val (e, t_e) = assert_EAsc e
        val x = fresh_evar ()
        val c = EUnOp (EUProj proj, EV x)
        val c = k && c
        val t_x = cps_t t_e
        val c = EAbs $ close_e_e_anno ((x, "x", t_x), c)
      in
        cps (e, t_e) (c, j_k %+ T1)
      end
    | S.EUnOp (EUInjj, e) =>
      (* [[ l.e ]](k) = [[e]](\x. k (l.x)) *)
      let
        val t1_t2 = assert_TSum t_e
        val t_e = choose_injj t1_t2
        val x = fresh_evar ()
        val c = EUnOp (EUInjj, EV x)
        val c = k && c
        val t_x = cps_t t_e
        val c = EAbs $ close_e_e_anno ((x, "x", t_x), c)
      in
        cps (e, t_e) (c, j_k %+ T1)
      end
    | S.ECase (e, bind1, bind2) =>
      (* [[ case e (x.e1) (x.e2) ]](k) = [[e]](\y. case y (x. [[e1]](k)) (x. [[e2]](k))) *)
      let
        val (name_x_1, e1) = unBind bind1
        val (name_x_2, e2) = unBind bind2
        val x = fresh_evar ()
        val e1 = open_e_e x e1
        val e2 = open_e_e x e2
        val t_res = t_e
        val (e, t_e) = assert_EAsc e
        val t_res = cps_t t_res
        val (e1, i_e1) = cps (e1, t_res) (k, j_k)
        val (e2, i_e2) = cps (e2, t_res) (k, j_k)
        val y = fresh_evar ()
        val c = ECaseClose (EV y, ((x, name_x_1), e1), ((x, name_x_2), e2))
        val t_y = cps_t t_e
        val c = EAbs $ close_e_e_anno ((y, "y", t_y), c)
        val i_c = Tmax i_e1 i_e2
      in
        cps (e, t_e) (c, i_c)
      end
    | S.ELet (e1, bind) =>
      (* [[ let x = e1 e2 ]](k) = [[e1]](\x. [[e2]](k)) *)
      let
        val (e1, t_e1) = assert_EAsc e1
        val (name_x, e2) = unBind bind
        val x = fresh_evar ()
        val e2 = open_e_e x e2
        val (c, i_c) = cps (e2, t_res) (k, j_k)
        val t_x = cps_t t_e1
        val c = EAbs $ close_e_e_anno ((x, name_x, t_x), c)
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
        val (e1, t_e1) = assert_EAsc e1
        val (e2, t_e2) = assert_EAsc e2
        val x1 = fresh_evar ()
        val x2 = fresh_evar ()
        val t_x1 = cps_t t_e1
        val t_x2 = cps_t t_e2
        val e = k $$ EBinOp (EBPrim opr, EV x1, EV x2)
        val e = EAbs $ close_e_e_anno ((x2, "x2", t_x2), e)
        val (e, i_e) = cps (e2, t_e2) (e, j_k %+ T1)
        val e = EAbs $ close_e_e_anno ((x1, "x1", t_x1), e)
      in
        cps (e1, t_e1) (e, i_e)
      end
    | S.EBinOp (EBRead, e1, e2) =>
      (* [[ read e1 e2 ]](k) = [[e1]] (\x1. [[e2]] (\x2. k (read x1 x2))) *)
      let
        val (e1, t_e1) = assert_EAsc e1
        val (e2, t_e2) = assert_EAsc e2
        val x1 = fresh_evar ()
        val x2 = fresh_evar ()
        val t_x1 = cps_t t_e1
        val t_x2 = cps_t t_e2
        val e = k $$ EBinOp (EBRead, EV x1, EV x2)
        val e = EAbs $ close_e_e_anno ((x2, "x2", t_x2), e)
        val (e, i_e) = cps (e2, t_e2) (e, j_k %+ T1)
        val e = EAbs $ close_e_e_anno ((x1, "x1", t_x1), e)
      in
        cps (e1, t_e1) (e, i_e)
      end
    | S.EWrite (e1, e2, e3) =>
      (* [[ write e1 e2 e3 ]](k) = [[e1]] (\x1. [[e2]] (\x2. [[e3]] (\x3. k (write x1 x2 x3)))) *)
      let
        val (e1, t_e1) = assert_EAsc e1
        val (e2, t_e2) = assert_EAsc e2
        val (e3, t_e3) = assert_EAsc e3
        val x1 = fresh_evar ()
        val x2 = fresh_evar ()
        val x2 = fresh_evar ()
        val t_x1 = cps_t t_e1
        val t_x2 = cps_t t_e2
        val t_x3 = cps_t t_e3
        val e = k $$ EWrite (EV x1, EV x2, EV x3)
        val e = EAbs $ close_e_e_anno ((x3, "x3", t_x3), e)
        val (e, i_e) = cps (e3, t_e3) (e, j_k %+ T1)
        val e = EAbs $ close_e_e_anno ((x2, "x2", t_x2), e)
        val (e, i_e) = cps (e2, t_e2) (e, i_e)
        val e = EAbs $ close_e_e_anno ((x1, "x1", t_x1), e)
      in
        cps (e1, t_e1) (e, i_e)
      end
    | _ => raise "Unimpl"
      
end
