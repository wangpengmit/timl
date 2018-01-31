(* Conversion to Continuation-Passing-Style (CPS) *)

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
