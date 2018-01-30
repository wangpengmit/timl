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


let rec cps (e, t) (k, j_k) =
  match e with
    | S.EVar x ->
      (EApp k (EVar x), j_k +% T1)
    | S.EAbs bind ->
      (* [[ \x.e ]]_k = k (\\j. \(x, c). [[e]]_c |> blowup_time(i, j))
         where [i] is the time bound of [e], blowup_time(i,j) = b(i+1)+2i+1+j, [b] is blow-up factor *)
      let ((name_x, _), e) = unEBindAnno bind in
      let (t_x, i, t_e) = assert_TArrow t in
      let x = fresh_evar () in
      let e = open_evar e x in
      let c = fresh_evar () in
      let j = fresh_ivar () in
      let (e, _) = cps (e, t_e) (c, j) in
      let e = EAscTime (e, blowup_time (i, j)) in
      let t_e = cps_t t_e in
      let t_c = cont_type (t_e, j) in
      let t_x = cps_t t_x in
      let e = EAbsTuple ([(x, name_x, t_x), (c, "c", t_c)], e) in
      let e = EAbsTime (j, e) in
      (EApp k e, j_k +% T1)
    | S.EBinOp (EBApp, e1, e2) ->
      (* [[ e1 e2 ]]_k = [[e1]] (\x1. [[e2]] (\x2. x1 {k.j} (x2, k))) *)
      let (e1, t_e1) = assert_EAsc e1 in
      let (t_e2, i, _) = assert_TArrow t_e1 in
      let x1 = fresh_evar () in
      let x2 = fresh_evar () in
      let e = EAppTuple (EAppI x1 j_k) [x2, k] in
      let e = CloseEAbs ((x2, "x2", t_e2), e) in
      let t_x2 = cps_t t_e2 in
      let (e, i_e) = cps (e2, t_x2) (e, blowup_time (i, j_k)) in
      let t_x1 = cps_t t_e1 in
      let e = CloseEAbs ((x1, "x1", t_x1), e) in
      cps (e1, t_e1) (e, i_e)
    | S.EConst c ->
      (EApp k (EConst c), j_k +% T1)
    | S.ERec bind ->
      let ((name_x, _), e) = unEBindAnno bind in
      let x = fresh_evar () in
      let e = open_evar e x in
      let t_e = t in
      let t_x = cps_t t_e in
      let (e, i_e) = cps (e, t_e) (Eid t_x, T0) in (* CPS with id is not strictly legal, since id doesn't return unit. It's OK because e should be a value. Values can be CPSed with continuations that return non-unit. *)
      
