structure CPS = struct

fun cps e k =
  case e of
      S.EVar x => k $$ EVar x
    | S.EAbs bind =
      (* [[ \x.e ]]_k = k (\\j. \(x, c). [[e]]_c |> time(b, i, j)) *)
      (* where [b] is blow-up factor, [i] is the time bound of [e], 
          time(b,i,j) = b(i+1)+2i+1+j *)
      let
        val ((name, t), e) = unEBindAnno bind
        val e = shift01_i_e e
        val e = shift01_e_e e
        val c_t = 
        val e = cps e $ (EV 0, c_t)
      in
        k $$ f
      end

end
