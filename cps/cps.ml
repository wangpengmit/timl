(* Continuation-Passing-Style (CPS) Conversion *)

(* let rec cps (e, t) (k, j) = *)
(*   match e with *)
(*       S.EVar x -> k <| EVar x *)
(*     | S.EAbs bind -> *)
(*       (\* [[ \x.e ]]_k = k (\\j. \(x, c). [[e]]_c |> blowup_time(b, i, j)) *\) *)
(*       (\* where [b] is blow-up factor, [i] is the time bound of [e],  *)
(*           time(b,i,j) = b(i+1)+2i+1+j *\) *)
(*       let ((name, t), e) = unEBindAnno bind in *)
(*       let e = shift01_i_e e in *)
(*       let e = shift01_e_e e in *)
(*       let t_e = () in  *)
(*       let e = cps (e, t_e) (EV 0, IV 0) in *)
(*       k <| f *)

(* CPS conversion on types *)
let rec cps_t t =
  match t with
    | TArrow (t1, i, t2) ->
      let t1 = cps_t t1 in
      let t2 = cps_t t2 in
      let j = fresh_ivar () in
      let t = TProd (t1, TArrow (t2, IV j, TUnit)) in
      let t = TArrow (t, blowup_time (i, j), TUnit) in
      TForallTime ((j, "j"), t)
    | TQuan (Forall, bind) ->
      let ((name_alpha, kd_alpha), t) = unBindAnno bind in
      let alpha = fresh_tvar () in
      let t = open_t_t alpha t in
      let t = cps_t t in
      let j = fresh_ivar () in
      let t = TArrow (t, IV j, TUnit) in
      let t = TArrow (t, IV j +% T1, TUnit) in
      let t = TForallTime ((j, "j"), t) in
      TForall $ close_t_t_anno ((alpha, name_alpha, kd_alpha), t)
    | TVar _ -> t
    | TConst _ -> t
    | _ -> raise "Unimpl"

(* CPS conversion on terms *)
(* pre: ... |- k : [[t_e]] --j_k--> unit |> 0 *)
(* the 'unit' part can be relaxed if e is a value *)
let rec cps (e, t_e) (k, j_k) =
  match e with
    | S.EVar x ->
      (* [[ x ]](k) = k x *)
      (k $$ EV x, j_k +% T1)
    | S.EAbs bind ->
      (* [[ \x.e ]](k) = k (\\j. \(x, c). [[e]](c) |> blowup_time(i, j))
         where [i] is the time bound of [e], blowup_time(i,j) = b(i+1)+2i+1+j, [b] is blow-up factor *)
      let ((name_x, _), e) = unBindAnno bind in
      let (t_x, i, t_e) = assert_TArrow t_e in
      let x = fresh_evar () in
      let e = open_e_e x e in
      let c = fresh_evar () in
      let j = fresh_ivar () in
      let (e, _) = cps (e, t_e) (EV c, IV j) in
      let e = EAscTime (e, blowup_time (i, j)) in
      let t_e = cps_t t_e in
      let t_c = cont_type (t_e, j) in
      let t_x = cps_t t_x in
      let e = EAbsTuple ([(x, name_x, t_x), (c, "c", t_c)], e) in
      let e = EAbsTime ((j, "j"), e) in
      (k $$ e, j_k +% T1)
    | S.EBinOp (EBApp, e1, e2) ->
      (* [[ e1 e2 ]](k) = [[e1]] (\x1. [[e2]] (\x2. x1 {k.j} (x2, k))) *)
      let (e1, t_e1) = assert_EAsc e1 in
      let (t_e2, i, _) = assert_TArrow t_e1 in
      let x1 = fresh_evar () in
      let x2 = fresh_evar () in
      let e = EAppTuple (EAppI (EV x1, IV j_k), [EV x2, EV k]) in
      let t_x2 = cps_t t_e2 in
      let e = EAbs $ close_e_e_anno ((x2, "x2", t_x2), e) in
      let (e, i_e) = cps (e2, t_e2) (e, blowup_time (i, j_k)) in
      let t_x1 = cps_t t_e1 in
      let e = EAbs $ close_e_e_anno ((x1, "x1", t_x1), e) in
      cps (e1, t_e1) (e, i_e)
    | S.EConst c ->
      (* [[ x ]](c) = k c *)
      (k $$ EConst c, j_k +% T1)
    | S.ERec bind ->
      (* [[ fix x.e ]](k) = k (fix x. [[e]](id)) *)
      let ((name_x, _), e) = unBindAnno bind in
      let x = fresh_evar () in
      let e = open_e_e x e in
      let t_e = t in
      let t_x = cps_t t_e in
      assert $ is_value e;
      let (e, i_e) = cps (e, t_e) (Eid t_x, T0) in (* CPS with id is not strictly legal, since id doesn't return unit. It's OK because e should be a value. Values can be CPSed with continuations that return non-unit. *)
      let e = assert_beta e in
      assert $ is_value e;
      let e = ERec $ close_e_e_anno ((x, name_x, t_x), e) in
      (k $$ e, j_k +% T1)
    | S.EAbsT bind ->
      (* [[ \\alpha.e ]](k) = k (\\alpha. \\j. \c. [[e]](c)) *)
      let ((name_alpha, kd_alpha), e) = unBindAnno bind in
      let (_, t_e) = assert_TAbsT t_e in
      let alpha = fresh_tvar () in
      let e = open_t_e alpha e in
      let t_e = open_t_t alpha t_e in
      let j = fresh_ivar () in
      let c = fresh_evar () in
      assert $ is_value e;
      let (e, _) = cps (e, t_e) (EV c, IV j) in
      let e = EAscTime (e, blowup_time_t j) in
      let t_e = cps_t t_e in
      let t_c = cont_type (t_e, j) in
      let e = EAbs $ close_e_e_anno ((c, "c", t_c), e) in
      let e = EAbsTime ((j, "j"), e) in
      let e = EAbsT $ close_t_e_anno ((alpha, name_alpha, kd_alpha), e) in
      (k $$ e, j_k +% T1)
    | S.AppT (e, i) ->
       (* [[ e[t] ]](k) = [[e]](\x. x[t]{k.j}(k)) *)
      let (e, t_e) = assert_EAsc e in
      let (t_e2, i, _) = assert_TArrow t_e1 in
      let x = fresh_evar () in
      let c = EAppI (EAppT (EV x, t), IV j_k) $$ k in
      let t_x = cps_t t_e in
      let c = EAbs $ close_e_e ((x, "x", t_x), c) in
      cps (e, t_e) (c, blowup_time_t j)
    | S.EUnOp (EUFold t_fold, e) ->
       (* [[ fold e ]](k) = [[e]](\x. k (fold x)) *)
      let (e, t_e) = assert_EAsc e in
      let x = fresh_evar () in
      let t_fold = cps_t t_fold in
      let c = EFold (t_fold, EV x) in
      let c = k $$ c in
      let t_x = cps_t t_e in
      let c = EAbs $ close_e_e_anno ((x, "x", t_x), c) in
      cps (e, t_e) (c, j_k +% T1)
    | S.EUnOp (EUUnfold, e) ->
       (* [[ unfold e ]](k) = [[e]](\x. k (unfold x)) *)
      let (e, t_e) = assert_EAsc e in
      let x = fresh_evar () in
      let c = EUnfold (EV x) in
      let c = k && c in
      let t_x = cps_t t_e in
      let c = EAbs $ close_e_e_anno ((x, "x", t_x), c) in
      cps (e, t_e) (c, j_k +% T1)
    | S.EPack (t_pack, t, e) ->
      (* [[ pack <t, e> ]](k) = [[e]](\x. k (pack <t, x>)) *)
      let (e, t_e) = assert_EAsc e in
      let x = fresh_evar () in
      let t_pack = cps_t t_pack in
      let t = cps_t t in
      let c = EPack (t_pack, t, EV x) in
      let c = k $$ c in
      let t_x = cps_t t_e in
      let c = EAbs $ close_e_e_anno ((x, "x", t_x), c) in
      cps (e, t_e) (c, j_k +% T1)
    | S.EUnpack (e1, bind) ->
       (* [[ unpack e1 as <alpha, x> in e2 ]](k) = [[e1]](\x1. unpack x1 as <alpha, x> in [[e2]](k)) *)
      let (e1, t_e1) = assert_EAsc e1 in
      let (name_alpha, e2) = unBind e2 in
      let (name_x, e2) = unBind e2 in
      let alpha = fresh_tvar () in
      let x = fresh_evar () in
      let e2 = open_t_e alpha e2 in
      let e2 = open_e_e x e2 in
      let x1 = fresh_evar () in
      let t_e2 = t_e in
      let (c, i_c) = cps (e2, t_e2) (k, j) in
      let c = EUnpackClose (EV x1, (alpha, name_alpha), (x, name_x), c) in
      let t_x1 = cps_t t_e1 in
      let c = EAbs $ close_e_e_anno ((x1, "x1", t_x1), c) in
      cps (e1, t_e1) (c, i_c)
    | S.EBinOp (EBPair, e1, e2) ->
      (* [[ (e1, e2) ]](k) = [[e1]] (\x1. [[e2]] (\x2. k (x1, x2))) *)
      let (t_e1, t_e2) = assert_TProd t_e in
      let x1 = fresh_evar () in
      let x2 = fresh_evar () in
      let t_x1 = cps_t t_e1 in
      let t_x2 = cps_t t_e2 in
      let e = EAppTuple (k, [EV x1, EV x2]) in
      let e = EAbs $ close_e_e_anno ((x2, "x2", t_x2), e) in
      let (e, i_e) = cps (e2, t_e2) (e, j_k +% T1) in
      let e = EAbs $ close_e_e_anno ((x1, "x1", t_x1), e) in
      cps (e1, t_e1) (e, i_e)
    | S.EUnOp (EUProj proj, e) ->
       (* [[ e.p ]](k) = [[e]](\x. k (x.p)) *)
      let (e, t_e) = assert_EAsc e in
      let x = fresh_evar () in
      let c = EUnOp (EUProj proj, EV x) in
      let c = k && c in
      let t_x = cps_t t_e in
      let c = EAbs $ close_e_e_anno ((x, "x", t_x), c) in
      cps (e, t_e) (c, j_k +% T1)
    | S.EUnOp (EUInj inj, e) ->
       (* [[ l.e ]](k) = [[e]](\x. k (l.x)) *)
      let t1_t2 = assert_TSum t_e in
      let t_e = choose_inj inj t1_t2 in
      let x = fresh_evar () in
      let c = EUnOp (EUInj inj, EV x) in
      let c = k && c in
      let t_x = cps_t t_e in
      let c = EAbs $ close_e_e_anno ((x, "x", t_x), c) in
      cps (e, t_e) (c, j_k +% T1)
    | S.ECase (e, bind1, bind2) ->
      (* [[ case e (x.e1) (x.e2) ]](k) = [[e]](\y. case y (x. [[e1]](k)) (x. [[e2]](k))) *)
      let (name_x_1, e1) = unBind bind1 in
      let (name_x_2, e2) = unBind bind2 in
      let x = fresh_evar () in
      let e1 = open_e_e x e1 in
      let e2 = open_e_e x e2 in
      let t_res = t_e in
      let (e, t_e) = assert_EAsc e in
      let t_res = cps_t t_res in
      let (e1, i_e1) = cps (e1, t_res) (k, j_k) in
      let (e2, i_e2) = cps (e2, t_res) (k, j_k) in
      let y = fresh_evar () in
      let c = ECaseClose (EV y, ((x, name_x_1), e1), ((x, name_x_2), e2)) in
      let t_y = cps_t t_e in
      let c = EAbs $ close_e_e_anno ((y, "y", t_y), c) in
      let i_c = Tmax i_e1 i_e2 in
      cps (e, t_e) (c, i_c)
    | S.ELet (e1, bind) ->
      (* [[ let x = e1 in e2 ]](k) = [[e1]](\x. [[e2]](k)) *)
      let (e1, t_e1) = assert_EAsc e1 in
      let (name_x, e2) = unBind bind in
      let x = fresh_evar () in
      let e2 = open_e_e x e2 in
      let (c, i_c) = cps (e2, t_res) (k, j_k) in
      let t_x = cps_t t_e1 in
      let c = EAbs $ close_e_e_anno ((x, name_x, t_x), c) in
      cps (e1, t_e1) (c, i_c)
    | S.EAscType (e, t) ->
      cps (e, t) (k, j_k)  (* todo: may need to do more *)
    | S.EAscTime (e, i) ->
      cps (e, t_e) (k, j_k) (* todo: may need to do more *)
    | S.EBinOp (EBPrim opr, e1, e2) ->
      (* [[ e1 o e2 ]](k) = [[e1]] (\x1. [[e2]] (\x2. k (x1 o x2))) *)
      let (e1, t_e1) = assert_EAsc e1 in
      let (e2, t_e2) = assert_EAsc e2 in
      let x1 = fresh_evar () in
      let x2 = fresh_evar () in
      let t_x1 = cps_t t_e1 in
      let t_x2 = cps_t t_e2 in
      let e = k $$ EBinOp (EBPrim opr, EV x1, EV x2) in
      let e = EAbs $ close_e_e_anno ((x2, "x2", t_x2), e) in
      let (e, i_e) = cps (e2, t_e2) (e, j_k +% T1) in
      let e = EAbs $ close_e_e_anno ((x1, "x1", t_x1), e) in
      cps (e1, t_e1) (e, i_e)
    | S.EBinOp (EBRead, e1, e2) ->
      (* [[ read e1 e2 ]](k) = [[e1]] (\x1. [[e2]] (\x2. k (read x1 x2))) *)
      let (e1, t_e1) = assert_EAsc e1 in
      let (e2, t_e2) = assert_EAsc e2 in
      let x1 = fresh_evar () in
      let x2 = fresh_evar () in
      let t_x1 = cps_t t_e1 in
      let t_x2 = cps_t t_e2 in
      let e = k $$ EBinOp (EBRead, EV x1, EV x2) in
      let e = EAbs $ close_e_e_anno ((x2, "x2", t_x2), e) in
      let (e, i_e) = cps (e2, t_e2) (e, j_k +% T1) in
      let e = EAbs $ close_e_e_anno ((x1, "x1", t_x1), e) in
      cps (e1, t_e1) (e, i_e)
    | S.EWrite (e1, e2, e3) ->
      (* [[ write e1 e2 e3 ]](k) = [[e1]] (\x1. [[e2]] (\x2. [[e3]] (\x3. k (write x1 x2 x3)))) *)
      let (e1, t_e1) = assert_EAsc e1 in
      let (e2, t_e2) = assert_EAsc e2 in
      let (e3, t_e3) = assert_EAsc e3 in
      let x1 = fresh_evar () in
      let x2 = fresh_evar () in
      let x2 = fresh_evar () in
      let t_x1 = cps_t t_e1 in
      let t_x2 = cps_t t_e2 in
      let t_x3 = cps_t t_e3 in
      let e = k $$ EWrite (EV x1, EV x2, EV x3) in
      let e = EAbs $ close_e_e_anno ((x3, "x3", t_x3), e) in
      let (e, i_e) = cps (e3, t_e3) (e, j_k +% T1) in
      let e = EAbs $ close_e_e_anno ((x2, "x2", t_x2), e) in
      let (e, i_e) = cps (e2, t_e2) (e, i_e) in
      let e = EAbs $ close_e_e_anno ((x1, "x1", t_x1), e) in
      cps (e1, t_e1) (e, i_e)
    | _ -> raise "Unimpl"
      
      
