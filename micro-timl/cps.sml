(* Continuation-Passing-Style (CPS) Conversion *)

structure CPS = struct

open Expr
open CompilerUtil
open MicroTiMLLongId
open MicroTiMLLocallyNameless
open MicroTiMLUtil
open MicroTiML
structure S = MicroTiML

infixr 0 $

infix 9 %@
infix 8 %^
infix 7 %*
infix 6 %+ 
infix 6 %++ 
infix 4 %<=
infix 4 %>=
infix 4 %=
infixr 3 /\
infixr 2 \/
infixr 1 -->
infix 1 <->

fun a %++ b = IUnion (a, b)
  
fun IV x = VarI (make_Free_i x, [])
                
val STime = STime dummy
val SNat = SNat dummy
val SBool = SBool dummy
val SUnit = SUnit dummy

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
            
fun TForallIClose (x, t) = TForallI $ close0_i_t_anno (x, t)
fun TForallICloseMany (xs, b) = foldr TForallIClose b xs
fun TForallTimeClose ((x, name), t) = TForallIClose ((x, name, STime), t)
fun EAbsIClose (x, e) = EAbsI $ close0_i_e_anno (x, e)
fun EAbsICloseMany (xs, b) = foldr EAbsIClose b xs
fun EAbsTimeClose ((x, name), e) = EAbsIClose ((x, name, STime), e)
fun ELetConstrClose ((x, name), e1, e2) = MakeELetConstr (e1, (name, dummy), close0_c_e x e2)
  
fun Eid t = EAbs (IEmptyState, EBindAnno ((("x", dummy), t), EVar $ Bound 0))
fun EHaltFun t_arg t_result = EAbs (IEmptyState, EBindAnno ((("x", dummy), t_arg), EHalt (EVar $ Bound 0, t_result)))

infix 0 %:
fun a %: b = EAscType (a, b)
infix 0 |>
fun a |> b = EAscTime (a, b)

(* smart EApp that converts topmost beta-redex to ELet and creates aliases for e1 and e2 *)
(* pre: e1 and e2 must be value *)
fun EApp_alias_fun_arg (e1, e2) =
    case e1 of
        EAbs (st, bind) =>
        let
          val (t_x, (name_x, e_body)) = unBindAnnoName bind
          val e = MakeELet (e2 (* %: t_x *), name_x, e_body)
        in
          e
        end
      | _ =>
        let
          val e = EApp (EVar $ ID (1, dummy), EVar $ ID (0, dummy))
          val e = MakeELet (shift01_e_e e2, ("x2", dummy), e)
          val e = MakeELet (e1, ("x1", dummy), e)
        in
          e
        end
(* smart EApp that converts topmost beta-redex to ELet and creates aliases for e2 (not e1) *)
(* used for CPS of EApp and EAppI/T when the function part shouldn't be aliased because that may create a EAppI/T not followed by EApp, which CC can't handle *)
(* pre: e2 must be value *)
fun EApp_alias_arg (e1, e2) =
    case e1 of
        EAbs (st, bind) =>
        let
          val (t_x, (name_x, e_body)) = unBindAnnoName bind
          val e = MakeELet (e2 (* %: t_x *), name_x, e_body)
        in
          e
        end
      | _ =>
        let
          (* val () = assert_b "EApp_alias_arg" $ is_value e2 *)
          val e = MakeELet (e2, ("x", dummy), EApp (shift01_e_e e1, EVar $ ID (0, dummy)))
        in
          e
        end
        
infixr 0 %%
fun a %% b = EApp (a, b)
infixr 0 %$
fun a %$ b = EApp_alias_arg (a, b)
infixr 0 $$
fun a $$ b = EApp_alias_fun_arg (a, b)
                  
(* fun assert_and_reduce_beta e = *)
(*   case e of *)
(*       EBinOp (EBApp, EAbs bind, e2) => *)
(*       let *)
(*         val (_, e1) = unBindAnno bind *)
(*       in *)
(*         subst0_e_e e2 e1 *)
(*       end *)
(*     | _ => raise assert_fail "assert_and_reduce_beta" *)

fun assert_and_reduce_letxx e =
    let
      fun error () = raise assert_fail $ "assert_and_reduce_letxx: " ^ (ExportPP.pp_e_to_string (NONE, NONE) $ ExportPP.export (NONE, NONE) ([], [], [], []) e)
    in
      case e of
          ELet (e1, bind) =>
          let
            val (name_x, e2) = unBindSimpName bind
            val () = case e2 of
                         EVar (ID (x, _)) =>
                         if x = 0 then () else error ()
                       | _ => error ()
          in
            e1
          end
        | _ => error ()
    end

val whnf = fn t => whnf ([], []) t
                       
fun blowup_time (i : idx, j : idx) = i %* ConstIT (TimeType.fromInt 999, dummy) %+ j
fun blowup_time_t (j : idx) = j %* ConstIT (TimeType.fromInt 888, dummy)
fun blowup_time_i (j : idx) = j %* ConstIT (TimeType.fromInt 777, dummy)

val Void = (IEmptyState, TUnit)
                                
(* CPS conversion on types *)
fun cps_t t =
  let
    (* val () = println $ "cps_t() on: " ^ (ExportPP.pp_t_to_string $ ExportPP.export_t ([], []) t) *)
    (* val t = whnf t *)
    (* [[ \\a.t ]] = \\a. \\j F. {F, ({F, [[t]]} --j--> void)} -- blowup_time_t(j) --> void *)
    fun cps_Forall t =
      let
        val t = cps_t t
        val j = fresh_ivar ()
        val F = fresh_ivar ()
        val t = TArrow ((IV F, t), IV j, Void)
        val t = TArrow ((IV F, t), IV j %+ T_1, Void)
        val t = TForallICloseMany ([(j, "j", STime), (F, "F", SState)], t)
      in
        t
      end
    val t =                                         
    case whnf t of
      TArrow ((st1, t1), i, (st2, t2)) =>
      (* [[ {st1, t1} --i--> {st2, t2} ]] = \\j F. {st1+F, [[t1]]*(st2+F, {[[t2]]} --j--> void)} -- blowup_time(i, j) --> void *)
      let
        val t1 = cps_t t1
        val t2 = cps_t t2
        val j = fresh_ivar ()
        val F = fresh_ivar ()
        val t = TProd (t1, TArrow ((st2 %++ IV F, t2), IV j, Void))
        val t = TArrow ((st1 %++ IV F, t), blowup_time (i, IV j), Void)
      in
        TForallICloseMany ([(j, "j", STime), (F, "F", SState)], t)
      end
    | TQuan (Forall, bind) =>
      let
        val ((name_a, kd_a), t) = unBindAnno2 bind
        val a = fresh_tvar ()
        val t = open0_t_t a t
        val t = cps_Forall t
      in
        TForall $ close0_t_t_anno ((a, name_a, kd_a), t)
      end
    | TQuanI (Forall, bind) =>
      let
        val ((name_a, s_a), t) = unBindAnno2 bind
        val a = fresh_ivar ()
        (* val () = println $ "a=" ^ str_int (unFree_i a) *)
        (* val () = println $ "before open0_i_t(): " ^ (ExportPP.pp_t_to_string $ ExportPP.export_t ([], []) t) *)
        val t = open0_i_t a t
        (* val () = println $ "after open0_i_t(): " ^ (ExportPP.pp_t_to_string $ ExportPP.export_t ([], []) t) *)
        val t = cps_Forall t
      in
        TForallI $ close0_i_t_anno ((a, name_a, s_a), t)
      end
    | TVar _ => t
    | TConst _ => t
    | TNat _ => t
    | TiBool _ => t
    | TBinOp (opr, t1, t2) => TBinOp (opr, cps_t t1, cps_t t2)
    | TArr (t, i) => TArr (cps_t t, i)
    | TQuan (Exists ex, bind) => 
      let
        val ((name_alpha, kd_alpha), t) = unBindAnno2 bind
        val alpha = fresh_tvar ()
        val t = open0_t_t alpha t
        val t = cps_t t
        val t = close0_t_t_anno ((alpha, name_alpha, kd_alpha), t)
      in
        TQuan (Exists ex, t)
      end
    | TQuanI (Exists ex, bind) => 
      let
        val ((name_a, s_a), t) = unBindAnno2 bind
        val a = fresh_ivar ()
        val t = open0_i_t a t
        val t = cps_t t
        val t = close0_i_t_anno ((a, name_a, s_a), t)
      in
        TQuanI (Exists ex, t)
      end
    | TRec bind => 
      let
        val ((name_alpha, kd_alpha), t) = unBindAnno2 bind
        val alpha = fresh_tvar ()
        val t = open0_t_t alpha t
        val t = cps_t t
        val t = close0_t_t_anno ((alpha, name_alpha, kd_alpha), t)
      in
        TRec t
      end
    | TAbsT bind => 
      let
        val ((name_alpha, kd_alpha), t) = unBindAnno2 bind
        val alpha = fresh_tvar ()
        val t = open0_t_t alpha t
        val t = cps_t t
        val t = close0_t_t_anno ((alpha, name_alpha, kd_alpha), t)
      in
        TAbsT t
      end
    | TAppT (t1, t2) => TAppT (cps_t t1, cps_t t2)
    | TAbsI bind => 
      let
        val ((name_a, s_a), t) = unBindAnno2 bind
        val a = fresh_ivar ()
        val t = open0_i_t a t
        val t = cps_t t
        val t = close0_i_t_anno ((a, name_a, s_a), t)
      in
        TAbsI t
      end
    | TAppI (t, i) => TAppI (cps_t t, i)
    | _ =>
      let
        val s = (* substr 0 100 $  *)ExportPP.pp_t_to_string NONE $ ExportPP.export_t NONE ([], []) t
      in
        raise Impossible $ "cps_t() on: " ^ s
      end
    (* val () = println $ "cps_t() result: " ^ (ExportPP.pp_t_to_string $ ExportPP.export_t ([], []) t) *)
  in
    t
  end

fun cont_type (t, i) = TArrow (t, i, Void)

(* CPS conversion on terms *)
(* pre: ... |- k : [[t_e]] --j_k-=> unit |> 0 *)
(* the 'unit' part can be relaxed if e is a value *)
fun cps (e, t_e, F) (k, j_k) =
  let
    (* val () = println $ "CPS on " ^ (substr 0 400 $ ExportPP.pp_e_to_string $ ExportPP.export ([], [], [], []) e) *)
    (* [[ \\a.e ]](k) = k (\\a. \\j F. \c {F}. [[e]](c)) *)
    val cps_with_frame = cps
    fun cps (e, t_e) (k, j_k) = cps_with_frame (e, t_e, F) (k, j_k)
    fun cps_EAbsIT (e, t_e) =
      let
        val j = fresh_ivar ()
        val F = fresh_ivar ()
        val c = fresh_evar ()
        val () = assert_b_m (fn () => "is_value() on " ^ (ExportPP.pp_e_to_string (NONE, NONE) $ ExportPP.export (NONE, NONE) ([], [], [], []) e)) $ is_value e
        val (e, _) = cps_with_frame (e, t_e, F) (EV c, IV j)
        val e = EAscTime (e, blowup_time_t (IV j))
        val t_e = cps_t t_e
        val t_c = cont_type ((IV F, t_e), IV j)
        val e = EAbs (IV F, close0_e_e_anno ((c, "c", t_c), e))
        val e = EAbsICloseMany ([(j, "j", STime), (F, "F", SState)], e)
      in
        e
      end
    fun main () =
  case e of
      S.EVar x =>
      (* [[ x ]](k) = k x *)
      (k $$ EVar x, j_k %+ T_1)
    | S.EAbs (_, bind) =>
      (* [[ \x {pre_st}. e {post_st} ]](k) = k (\\j F. \(x, c) {pre_st+F}. [[e]](c) |> blowup_time(i, j))
         where [i] is the time bound of [e], blowup_time(i,j) = b(i+1)+2i+1+j, [b] is blow-up factor *)
      let
        val ((name_x, _), e) = unBindAnno2 bind
        val t_e = whnf t_e
        val ((pre_st, t_x), i, (post_st, t_e)) = assert_TArrow t_e
        val x = fresh_evar ()
        val e = open0_e_e x e
        val c = fresh_evar ()
        val j = fresh_ivar ()
        val F = fresh_ivar ()
        val (e, _) = cps_with_frame (e, t_e, F) (EV c, IV j)
        val e = EAscTime (e, blowup_time (i, IV j))
        val t_e = cps_t t_e
        val t_c = cont_type ((post_st %++ IV F, t_e), IV j)
        val t_x = cps_t t_x
        val e = EAbsPairClose (pre_st %++ IV F, (x, name_x, t_x), (c, "c", t_c), e)
        val e = EAbsICloseMany ([(j, "j", STime), (F, "F", SState)], e)
      in
        (k $$ e, j_k %+ T_1)
      end
    | S.EBinOp (EBApp, e1, e2) =>
      (* [[ e1 e2 ]](k) = [[e1]] (\x1. [[e2]] (\x2. x1 {k.j} (x2, k))) *)
      let
        val (e1, st_e1) = assert_EAscState e1
        val (e1, t_e1) = assert_EAscType e1
        val (e2, st_e2) = assert_EAscState e2
        val t_e1 = whnf t_e1
        val ((_, t_e2), i, _) = assert_TArrow t_e1
        val x1 = fresh_evar ()
        val x2 = fresh_evar ()
        val xk = fresh_evar ()
        val e = EAppI (EV x1, j_k) %$ EPair (EV x2, EV xk)
        val e = ELetClose ((xk, "k", k), e)
        val t_x2 = cps_t t_e2
        val e = EAbs (st_e2 %++ IV F, close0_e_e_anno ((x2, "x2", t_x2), e))
        val (e, i_e) = cps (e2, t_e2) (e, blowup_time (i, j_k))
        val t_x1 = cps_t t_e1
        val e = EAbs (st_e1 %++ IV F, close0_e_e_anno ((x1, "x1", t_x1), e))
      in
        cps (e1, t_e1) (e, i_e)
      end
    | S.EConst c =>
      (* [[ x ]](c) = k c *)
      (k $$ EConst c, j_k %+ T_1)
    | S.ENever t =>
      (* [[ never ]](k) = k(never) *)
      (k $$ ENever (cps_t t), j_k %+ T_1)
    | S.EBuiltin (name, t) =>
      (* [[ builtin ]](k) = k(builtin) *)
      (k $$ EBuiltin (name, cps_t t), j_k %+ T_1)
    | S.ERec bind =>
      (* [[ fix x.e ]](k) = k (fix x. [[e]](id)) *)
      let
        val ((name_x, _), e) = unBindAnno2 bind
        val () = println $ "cps() on: " ^ name_x
        val x = fresh_evar ()
        val e = open0_e_e x e
        val t_x = cps_t t_e
        val () = assert_b "cps/ERec/1" $ is_value e
        val (e, i_e) = cps (e, t_e) (Eid t_x, T_0) (* CPS with id is not strictly legal, since id doesn't return unit. It's OK because e should be a value. Values can be CPSed with continuations that return non-unit. *)
        val e = assert_and_reduce_letxx e
        val (e, _) = collect_EAscTypeTime e
        val () = assert_b "cps/ERec/2" $ is_value e
        val () = case snd $ collect_EAbsIT e of
                     EAbs _ => ()
                   | _ => raise Impossible "ERec: body after CPS should be EAbsITMany (EAbs (...))"
        val e = ERec $ close0_e_e_anno ((x, name_x, t_x), e)
      in
        (k $$ e, j_k %+ T_1)
      end
    | S.EAbsT bind =>
      let
        val ((name_a, kd_a), e) = unBindAnno2 bind
        val t_e = whnf t_e
        val (_, t_e) = assert_TForall t_e
        val a = fresh_tvar ()
        val e = open0_t_e a e
        val t_e = open0_t_t a t_e
        val e = cps_EAbsIT (e, t_e)
        val e = EAbsT $ close0_t_e_anno ((a, name_a, kd_a), e)
      in
        (k $$ e, j_k %+ T_1)
      end
    | S.EAbsI bind =>
      let
        val ((name_a, s_a), e) = unBindAnno2 bind
        val t_e = whnf t_e
        val (_, t_e) = assert_TForallI t_e
        val a = fresh_ivar ()
        val e = open0_i_e a e
        val t_e = open0_i_t a t_e
        val e = cps_EAbsIT (e, t_e)
        val e = EAbsI $ close0_i_e_anno ((a, name_a, s_a), e)
      in
        (k $$ e, j_k %+ T_1)
      end
    | S.EAppT (e, t) =>
      (* [[ e[t] ]](k) = [[e]](\x. x[t]{k.j}(k)) *)
      let
        val (e, st_e) = assert_EAscState e
        val (e, t_e) = assert_EAscType e
        val x = fresh_evar ()
        val c = EAppI (EAppT (EV x, cps_t t), j_k) %$ k
        val t_x = cps_t t_e
        val c = EAbs (st_e %++ IV F, close0_e_e_anno ((x, "x", t_x), c))
      in
        cps (e, t_e) (c, blowup_time_t j_k)
      end
    | S.EAppI (e, i) =>
      (* [[ e[i] ]](k) = [[e]](\x. x[i]{k.j}(k)) *)
      let
        val (e, st_e) = assert_EAscState e
        val (e, t_e) = assert_EAscType e
        val x = fresh_evar ()
        val c = EAppI (EAppI (EV x, i), j_k) %$ k
        val t_x = cps_t t_e
        val c = EAbs (st_e %++ IV F, close0_e_e_anno ((x, "x", t_x), c))
      in
        cps (e, t_e) (c, blowup_time_i j_k)
      end
    | S.EPack (t_pack, t, e) =>
      (* [[ pack <t, e> ]](k) = [[e]](\x. k (pack <t, x>)) *)
      let
        val (e, st_e) = assert_EAscState e
        val (e, t_e) = assert_EAscType e
        val x = fresh_evar ()
        val t_pack = cps_t t_pack
        val t = cps_t t
        val c = EPack (t_pack, t, EV x)
        val c = k $$ c
        val t_x = cps_t t_e
        val c = EAbs (st_e %++ IV F, close0_e_e_anno ((x, "x", t_x), c))
      in
        cps (e, t_e) (c, j_k %+ T_1)
      end
    | S.EPackI (t_pack, i, e) =>
      (* [[ packI <i, e> ]](k) = [[e]](\x. k (packI <i, x>)) *)
      let
        val (e, st_e) = assert_EAscState e
        val (e, t_e) = assert_EAscType e
        val x = fresh_evar ()
        val t_pack = cps_t t_pack
        val c = EPackI (t_pack, i, EV x)
        val c = k $$ c
        val t_x = cps_t t_e
        val c = EAbs (st_e %++ IV F, close0_e_e_anno ((x, "x", t_x), c))
      in
        cps (e, t_e) (c, j_k %+ T_1)
      end
    | S.EUnpack (e1, bind) =>
      (* [[ unpack e1 as <alpha, x> in e2 ]](k) = [[e1]](\x1. unpack x1 as <alpha, x> in [[e2]](k)) *)
      let
        val (e1, st_e1) = assert_EAscState e1
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
        val c = EAbs (st_e1 %++ IV F, close0_e_e_anno ((x1, "x1", t_x1), c))
      in
        cps (e1, t_e1) (c, i_c)
      end
    | S.EUnpackI (e1, bind) =>
      (* [[ unpackI e1 as <a, x> in e2 ]](k) = [[e1]](\x1. unpack x1 as <a, x> in [[e2]](k)) *)
      let
        val (e1, st_e1) = assert_EAscState e1
        val (e1, t_e1) = assert_EAscType e1
        val (name_a, e2) = unBindSimp2 bind
        val (name_x, e2) = unBindSimp2 e2
        val a = fresh_ivar ()
        val x = fresh_evar ()
        val e2 = open0_i_e a e2
        val e2 = open0_e_e x e2
        val x1 = fresh_evar ()
        val t_e2 = t_e
        val (c, i_c) = cps (e2, t_e2) (k, j_k)
        val c = EUnpackIClose (EV x1, (a, name_a), (x, name_x), c)
        val t_x1 = cps_t t_e1
        val c = EAbs (st_e1 %++ IV F, close0_e_e_anno ((x1, "x1", t_x1), c))
      in
        cps (e1, t_e1) (c, i_c)
      end
    | S.EBinOp (opr, e1, e2) =>
      (* [[ e1 o e2 ]](k) = [[e1]] (\x1. [[e2]] (\x2. k (x1 o x2))) *)
      let
        val (e1, st_e1) = assert_EAscState e1
        val (e2, st_e2) = assert_EAscState e2
        fun get_comp_types (e1, e2) t_e =
          case opr of
              EBPair => ((e1, e2), assert_TProd t_e)
            | _ =>
              let
                val (e1, t_e1) = assert_EAscType e1
                val (e2, t_e2) = assert_EAscType e2
              in
                ((e1, e2), (t_e1, t_e2))
              end
        val t_e = whnf t_e
        val ((e1, e2), (t_e1, t_e2)) = get_comp_types (e1, e2) t_e
        val x1 = fresh_evar ()
        val x2 = fresh_evar ()
        val t_x1 = cps_t t_e1
        val t_x2 = cps_t t_e2
        val e = k $$ EBinOp (opr, EV x1, EV x2)
        val e = EAbs (st_e2 %++ IV F, close0_e_e_anno ((x2, "x2", t_x2), e))
        val (e, i_e) = cps (e2, t_e2) (e, j_k %+ T_1)
        val e = EAbs (st_e1 %++ IV F, close0_e_e_anno ((x1, "x1", t_x1), e))
      in
        cps (e1, t_e1) (e, i_e)
      end
    | S.ENewArrayValues (t, es) =>
      let
        val t_x = cps_t t
        val xs_names_es = mapi (fn (i, e) => (fresh_evar (), "x" ^ str_int (i+1), assert_EAscState e)) es
        val xs = map (fn (x, _, _) => x) xs_names_es
        val ek = k $$ ENewArrayValues (t_x, map EV xs)
        fun f ((x, name, (e, st_e)), (ek, i_ek)) =
          let
            val ek = EAbs (st_e %++ IV F, close0_e_e_anno ((x, name, t_x), ek))
          in
            cps (e, t) (ek, i_ek)
          end
      in
        foldr f (ek, j_k %+ T_1) xs_names_es
      end
    | S.EUnOp (opr, e) =>
      (* [[ opr e ]](k) = [[e]](\x. k (opr x)) *)
      let
        val (e, st_e) = assert_EAscState e
        fun cps_EUnOp t_e f =
          let
            val x = fresh_evar ()
            val c = f x
            val c = k $$ c
            val t_x = cps_t t_e
            val c = EAbs (st_e %++ IV F, close0_e_e_anno ((x, "x", t_x), c))
          in
            cps (e, t_e) (c, j_k %+ T_1)
          end
        val (t_e, opr) = 
            case opr of
                EUInj (inj, t_other) =>
                let
                  val t_e = whnf t_e
                  val t1_t2 = assert_TSum t_e
                  val t_e = choose_inj t1_t2 inj
                  val t_other = cps_t t_other
                in
                  (t_e, EUInj (inj, t_other))
                end
              | EUFold t_fold =>
                let
                  val (e, t_e) = assert_EAscType e
                  val t_fold = cps_t t_fold
                in
                  (t_e, EUFold t_fold)
                end
              | EUUnfold =>
                let
                  val (e, t_e) = assert_EAscType e
                in
                  (t_e, opr)
                end
              | EUTiML (EUProj _) =>
                let
                  val (e, t_e) = assert_EAscType e
                in
                  (t_e, opr)
                end
              | EUTiML EUPrintc =>
                (TByte, opr)
              (* | EUTiML EUPrint => *)
              (*   (TString, opr) *)
              | EUTiML EUInt2Str =>
                (TInt, opr)
      in
        cps_EUnOp t_e (fn x => EUnOp (opr, EV x))
      end
    | S.ECase (e, bind1, bind2) =>
      (* [[ case e (x.e1) (x.e2) ]](k) = [[e]](\y. case y (x. [[e1]](k)) (x. [[e2]](k))) *)
      let
        val (e, st_e) = assert_EAscState e
        val (name_x_1, e1) = unBindSimp2 bind1
        val (name_x_2, e2) = unBindSimp2 bind2
        val x = fresh_evar ()
        val e1 = open0_e_e x e1
        val e2 = open0_e_e x e2
        val t_res = t_e
        val (e, t_e) = assert_EAscType e
        val t_res = cps_t t_res
        val x_k = fresh_evar ()
        val (e1, i_e1) = cps (e1, t_res) (EV x_k, j_k)
        val (e2, i_e2) = cps (e2, t_res) (EV x_k, j_k)
        val y = fresh_evar ()
        val c = ECaseClose (EV y, ((x, name_x_1), e1), ((x, name_x_2), e2))
        val c = ELetClose ((x_k, "k", k), c)
        val t_y = cps_t t_e
        val c = EAbs (st_e %++ IV F, close0_e_e_anno ((y, "y", t_y), c))
        val i_c = IMax (i_e1, i_e2)
      in
        cps (e, t_e) (c, i_c)
      end
    | S.EIfi (e, bind1, bind2) =>
      (* [[ ifi e (x.e1) (x.e2) ]](k) = [[e]](\y. ifi y (x. [[e1]](k)) (x. [[e2]](k))) *)
      let
        val (e, st_e) = assert_EAscState e
        val (name_x_1, e1) = unBindSimp2 bind1
        val (name_x_2, e2) = unBindSimp2 bind2
        val x = fresh_evar ()
        val e1 = open0_e_e x e1
        val e2 = open0_e_e x e2
        val t_res = t_e
        val (e, t_e) = assert_EAscType e
        val t_res = cps_t t_res
        val x_k = fresh_evar ()
        val (e1, i_e1) = cps (e1, t_res) (EV x_k, j_k)
        val (e2, i_e2) = cps (e2, t_res) (EV x_k, j_k)
        val y = fresh_evar ()
        val c = EIfiClose (EV y, ((x, name_x_1), e1), ((x, name_x_2), e2))
        val c = ELetClose ((x_k, "k", k), c)
        val t_y = cps_t t_e
        val c = EAbs (st_e %++ IV F, close0_e_e_anno ((y, "y", t_y), c))
        val i_c = IMax (i_e1, i_e2)
      in
        cps (e, t_e) (c, i_c)
      end
    | S.ETriOp (ETIte, e, e1, e2) =>
      (* [[ if e then e1 else e2 ]](k) = [[e]](\y. if y then [[e1]](k) else [[e2]](k)) *)
      let
        val (e, st_e) = assert_EAscState e
        val t_res = t_e
        val t_e = TBool
        val t_res = cps_t t_res
        val x_k = fresh_evar ()
        val (e1, i_e1) = cps (e1, t_res) (EV x_k, j_k)
        val (e2, i_e2) = cps (e2, t_res) (EV x_k, j_k)
        val y = fresh_evar ()
        val c = ETriOp (ETIte, EV y, e1, e2)
        val c = ELetClose ((x_k, "k", k), c)
        val t_y = cps_t t_e
        val c = EAbs (st_e %++ IV F, close0_e_e_anno ((y, "y", t_y), c))
        val i_c = IMax (i_e1, i_e2)
      in
        cps (e, t_e) (c, i_c)
      end
    | S.ELet (e1, bind) =>
      (* [[ let x = e1 in e2 ]](k) = [[e1]](\x. [[e2]](k)) *)
      let
        val (e1, st_e1) = assert_EAscState e1
        val (e1, t_e1) = assert_EAscType e1
        val t_res = t_e
        val (name_x, e2) = unBindSimp2 bind
        val x = fresh_evar ()
        val e2 = open0_e_e x e2
        val (c, i_c) = cps (e2, t_res) (k, j_k)
        val t_x = cps_t t_e1
        val c = EAbs (st_e1 %++ IV F, close0_e_e_anno ((x, name_x, t_x), c))
      in
        cps (e1, t_e1) (c, i_c)
      end
    | S.EAscType (e, t) =>
      (* let *)
      (*   val x = fresh_evar () *)
      (*   val t = cps_t t *)
      (*   val t_x = cps_t t_e *)
      (*   val k = k $$ (EV x %: t) *)
      (*   val k = EAbs $ close0_e_e_anno ((x, "x", t_x), k) *)
      (* in *)
      (*   cps (e, t) (k, j_k) *)
      (* end *)
      cps (e, t) (k, j_k)  (* todo: may need to do more *)
    | S.EAscTime (e, i) =>
      let
        val (e, i') = cps (e, t_e) (k, j_k)
        val i = blowup_time (i, j_k)
      in
        (e (* |> i' *) |> i, i)
      end
    | S.ETriOp (ETWrite, e1, e2, e3) =>
      (* [[ write e1 e2 e3 ]](k) = [[e1]] (\x1. [[e2]] (\x2. [[e3]] (\x3. k (write x1 x2 x3)))) *)
      let
        val (e1, st_e1) = assert_EAscState e1
        val (e1, t_e1) = assert_EAscType e1
        val (e2, st_e2) = assert_EAscState e2
        val (e2, t_e2) = assert_EAscType e2
        val (e3, st_e3) = assert_EAscState e3
        val (e3, t_e3) = assert_EAscType e3
        val x1 = fresh_evar ()
        val x2 = fresh_evar ()
        val x3 = fresh_evar ()
        val t_x1 = cps_t t_e1
        val t_x2 = cps_t t_e2
        val t_x3 = cps_t t_e3
        val e = k $$ EWrite (EV x1, EV x2, EV x3)
        val e = EAbs (st_e1 %++ IV F, close0_e_e_anno ((x3, "x3", t_x3), e))
        val (e, i_e) = cps (e3, t_e3) (e, j_k %+ T_1)
        val e = EAbs (st_e2 %++ IV F, close0_e_e_anno ((x2, "x2", t_x2), e))
        val (e, i_e) = cps (e2, t_e2) (e, i_e)
        val e = EAbs (st_e3 %++ IV F, close0_e_e_anno ((x1, "x1", t_x1), e))
      in
        cps (e1, t_e1) (e, i_e)
      end
    (* extensions from MicroTiML *)
    | S.EHalt (e, _) =>
      (* [[ halt e [_] ]](k) = [[e]](\x. halt x [unit]) *)
      let
        val (e, st_e) = assert_EAscState e
        val (e, t_e) = assert_EAscType e
        val x = fresh_evar ()
        val c = EHalt (EV x, TUnit)
        val t_x = cps_t t_e
        val c = EAbs (st_e %++ IV F, close0_e_e_anno ((x, "x", t_x), c))
      in
        cps (e, t_e) (c, T_1)
      end
    (* | S.ELetConstr (e1, bind) => *)
    (*   (* [[ let constr x = e1 in e2 ]](k) = [[e1]](\y. let constr x = y in [[e2]](k)) *) *)
    (*   let *)
    (*     val (e1, t_e1) = assert_EAscType e1 *)
    (*     val t_res = t_e *)
    (*     val (name_x, e2) = unBindSimp2 bind *)
    (*     val x = fresh_cvar () *)
    (*     val e2 = open0_c_e x e2 *)
    (*     val (c, i_c) = cps (e2, t_res) (k, j_k) *)
    (*     val y = fresh_evar () *)
    (*     val c = ELetConstrClose ((x, name_x), EV y, c) *)
    (*     val t_y = cps_t t_e1 *)
    (*     val c = EAbs $ close0_e_e_anno ((y, "y", t_y), c) *)
    (*   in *)
    (*     cps (e1, t_e1) (c, i_c) *)
    (*   end *)
    | _ =>
      let
        val s = (* substr 0 100 $  *)ExportPP.pp_e_to_string (NONE, NONE) $ ExportPP.export (NONE, NONE) ([], [], [], []) e
      in
        raise Unimpl $ "cps() on: " ^ s
      end
    fun extra_msg () = "\nwhen cps-ing:\n" ^ (ExportPP.pp_e_to_string (NONE, NONE) $ ExportPP.export (SOME 1, SOME 5) ([], [], [], []) e)
    val ret = main ()
              handle Impossible m => raise Impossible (m ^ extra_msg ())
  in
    ret
  end

val cps_tc_flags =
    let
      open MicroTiMLTypecheck
    in
      [Anno_EApp, Anno_EAppT, Anno_EAppI, Anno_EFold, Anno_EUnfold, Anno_EPack, Anno_EPackI, Anno_EUnpack, Anno_EUnpackI, Anno_EBPrim, Anno_ENew, Anno_ERead, Anno_ENat, Anno_ENatCmp, Anno_EProj, Anno_ECase, Anno_ELet, Anno_EWrite, Anno_EHalt]
    end
                     
(* Checks the form invariants after CPS, according to the 'System F to TAL' paper. *)
      
fun check_CPSed_ty_visitor_vtable cast () =
  let
    val vtable = 
        default_ty_visitor_vtable
          cast
          extend_noop
          extend_noop
          visit_noop
          visit_noop
          visit_noop
          visit_noop
    fun visit_TQuanI this env (data as (q, _)) =
      case q of
          Forall =>
          let
            val (binds, t) = collect_TForallIT $ TQuanI data
            val _ = assert_TArrow t
            val _ = #visit_ty (cast this) this env t
          in
            TQuanI data
          end
        | _ => #visit_TQuanI vtable this env data (* call super *)
    fun visit_TQuan this env (data as (q, _)) =
      case q of
          Forall =>
          let
            val (binds, t) = collect_TForallIT $ TQuan data
            val _ = assert_TArrow t
            val _ = #visit_ty (cast this) this env t
          in
            TQuan data
          end
        | _ => #visit_TQuan vtable this env data (* call super *)
    fun visit_TArrow this env (data as (t1, i, t2)) =
      let
        val _ = #visit_ty (cast this) this env t1
        val () = assert_TUnit "check_CPSed_type(): result type of TArrow must be TUnit" t2
      in
        TArrow data
      end
    val vtable = override_visit_TQuanI vtable visit_TQuanI
    val vtable = override_visit_TQuan vtable visit_TQuan
    val vtable = override_visit_TArrow vtable visit_TArrow
  in
    vtable
  end

fun new_check_CPSed_ty_visitor a = new_ty_visitor check_CPSed_ty_visitor_vtable a
    
fun check_CPSed_type b =
  let
    val visitor as (TyVisitor vtable) = new_check_CPSed_ty_visitor ()
  in
    #visit_ty vtable visitor () b
  end
    
fun check_CPSed_type_expr_visitor_vtable cast () =
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
    (ignore_this_env check_CPSed_type)

fun new_check_CPSed_type_expr_visitor params = new_expr_visitor check_CPSed_type_expr_visitor_vtable params

fun check_CPSed_type_e b =
  let
    val visitor as (ExprVisitor vtable) = new_check_CPSed_type_expr_visitor ()
  in
    ignore $ #visit_expr vtable visitor () b
  end

fun check_CPSed_expr e =
  let
    val loop = check_CPSed_expr
  in
  case fst $ collect_EAscType e of
      ELet (e1, bind) =>
      let
        val () = check_decl e1
        val (_, e2) = unBind bind
      in
        loop e2
      end
    | EUnpack (e1, bind) =>
      let
        val () = check_value e1
        val (_, bind) = unBind bind
        val (_, e2) = unBind bind
      in
        loop e2
      end
    | EUnpackI (e1, bind) =>
      let
        val () = check_value e1
        val (_, bind) = unBind bind
        val (_, e2) = unBind bind
      in
        loop e2
      end
    | EBinOp (EBApp, e1, e2) =>
      (check_value e1;
       check_value e2)
    | ECase (e, bind1, bind2) =>
      let
        val () = check_value e
        val (_, e1) = unBind bind1
        val (_, e2) = unBind bind2
      in
        (loop e1;
         loop e2)
      end
    | EIfi (e, bind1, bind2) =>
      let
        val () = check_value e
        val (_, e1) = unBind bind1
        val (_, e2) = unBind bind2
      in
        (loop e1;
         loop e2)
      end
    | ETriOp (ETIte, e, e1, e2) =>
      let
        val () = check_value e
      in
        (loop e1;
         loop e2)
      end
    | EHalt (e, _) => check_value e
    | EAscTime (e, _) => loop e
    | _ => raise Impossible $ "check_CPSed_expr():\n" ^ (ExportPP.pp_e_to_string (NONE, NONE) $ ExportPP.export (NONE, NONE) ([], [], [], []) e)
  end

and check_decl e =
    case fst $ collect_EAscType e of
        EUnOp (_, e) => check_value e
      | EBinOp (opr, e1, e2) =>
        (assert_b "check_decl/EBinOp/opr <> EBApp" $ opr <> EBApp;
         check_value e1;
         check_value e2)
      | ETriOp (ETWrite, e1, e2, e3) =>
        (check_value e1;
         check_value e2;
         check_value e3)
      | ENewArrayValues (t, es) => app check_value es
      | EMallocPair _ => ()
      | EPairAssign (e1, _, e2) =>
        (check_value e1;
         check_value e2)
      | EProjProtected (_, e) => check_value e
      | _ => check_value e
             handle Impossible msg =>
                    raise Impossible $ "check_decl():\n" ^ msg
        
and check_value e =
  case e of
      EConst _ => ()
    | EBinOp (EBPair, e1, e2) => (check_value e1; check_value e2)
    | EUnOp (EUInj _, e) => check_value e
    | EAbs bind =>
      let
        val (_, e) = unBindAnno bind
      in
        check_CPSed_expr e
      end
    | EAbsT bind => 
      let
        val (_, e) = unBindAnno bind
      in
        check_value e
      end
    | EAbsI bind => 
      let
        val (_, e) = unBindAnno bind
      in
        check_value e
      end
    | EPack (_, _, e) => check_value e
    | EPackI (_, _, e) => check_value e
    | EPackIs (_, _, e) => check_value e
    | EUnOp (EUFold _, e) => check_value e
    | EAscType (e, _) => check_value e
    | EAppT (e, _) => check_value e
    | EAppI (e, _) => check_value e
    | ERec data =>
      let
        val (_, e) = unBindAnno data
      in
        check_value e
      end
    | EVar _ => () (* variables denote values *)
    | ENever _ => ()
    | EBuiltin _ => ()
    | _ => raise Impossible $ "check_value():\n" ^ (ExportPP.pp_e_to_string (NONE, NONE) $ ExportPP.export (NONE, NONE) ([], [], [], []) e)

val check_CPSed_expr = fn e => (check_CPSed_type_e e; check_CPSed_expr e)
                              
structure UnitTest = struct

structure TestUtil = struct

open LongId
open Util
open MicroTiML
open MicroTiMLVisitor
open MicroTiMLLongId
open MicroTiML
       
fun fail () = OS.Process.exit OS.Process.failure
                   
end

open TestUtil

infixr 0 $
infixr 0 !!
         
fun test1 dirname =
  let
    val () = println "CPS.UnitTest started"
    val filename = join_dir_file (dirname, "cps-test1.pkg")
    val filenames = map snd $ ParseFilename.expand_pkg (fn msg => raise Impossible msg) (true, filename)
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
    val empty_ctx = ToStringUtil.empty_ctx
    (* val () = println $ str_e empty empty_ctx e *)
    (* val () = println "" *)
    val () = println "Started translating ..."
    val e = trans_e e
    val () = println "Finished translating"
    (* val () = pp_e $ export empty_ctx e *)
    (* val () = println "" *)
                     
    open MicroTiMLTypecheck
    open TestUtil
    val () = println "Started MicroTiML typechecking #1 ..."
    val ((e, t, i), vcs, admits) = typecheck cps_tc_flags ([], [], []) e
    val () = println "Finished MicroTiML typechecking #1"
    val () = println "Type:"
    open ExportPP
    val () = pp_t NONE $ export_t NONE ([], []) t
    val () = println "Time:"
    val i = simp_i i
    val () = println $ ToString.str_i Gctx.empty [] i
    (* val () = println $ "#VCs: " ^ str_int (length vcs) *)
    (* val () = println "VCs:" *)
    (* val () = app println $ concatMap (fn ls => ls @ [""]) $ map (str_vc false "") vcs *)
    val () = pp_e (NONE, NONE) $ export (NONE, NONE) empty_ctx e
    val () = println ""
                     
    val () = println "Started CPS conversion ..."
    val (e, _) = cps (e, TUnit) (EHaltFun TUnit TUnit, T_0)
    (* val (e, _) = cps (e, TUnit) (Eid TUnit, T_0) *)
    val () = println "Finished CPS conversion ..."
    val () = pp_e (NONE, NONE) $ export (NONE, NONE) empty_ctx $ uniquefy_e empty_ctx $ MicroTiMLPostProcess.post_process e
    val () = println ""
    val () = println "Started post-CPS form checking"
    val () = check_CPSed_expr e
    val () = println "Finished post-CPS form checking"
    val () = println "Started MicroTiML typechecking #2 ..."
    val ((e, t, i), vcs, admits) = typecheck [] ([], [], []) e
    val () = println "Finished MicroTiML typechecking #2"
    val () = println "Type:"
    val () = pp_t NONE $ export_t NONE ([], []) t
    val () = println "Time:"
    val i = simp_i i
    val () = println $ ToString.str_i Gctx.empty [] i
    val () = println "CPS.UnitTest passed"
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
