(* Closure Conversion *)

let rec cc_t t =
  match t with
    | TArrow _ ->
      cc_t_arrow t
    | TQuan (Forall, _) ->
      cc_t_arrow t
    | TQuanI (Forall, _) ->
      cc_t_arrow t
    | _ -> raise "Unimpl"

and let rec cc_t_arrow t =
      let (binds, t) = open_collect_Forall_ForallI t in
      let (t1, i, t2) = assert_TArrow t in
      let t1 = cc_t t1 in
      let t2 = cc_t t2 in
      let alpha = fresh_tvar () in
      let t = TArrow (TProd (TV alpha, t1), i, t2) in
      let t = close_combine_Forall_ForallI (binds, t) in
      let t = TProd (t, TV alpha) in
      TExists $ close_t_t_anno ((alpha, "'a", KType), t)
