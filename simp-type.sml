functor SimpTypeFn (structure Type : TYPE
                    val simp_i : Type.idx -> Type.idx
                    val simp_s : Type.sort -> Type.sort
                    val subst_i_mt : Type.idx -> Type.mtype -> Type.mtype
                   ) = struct

open Type
open SimpUtil

(* todo: use visitor *)
       
infixr 0 $
         
fun simp_mt t =
  case t of
      TArrow ((st1, t1), (j, i), (st2, t2)) => TArrow ((StMap.map simp_i st1, simp_mt t1), (simp_i j, simp_i i), (StMap.map simp_i st2, simp_mt t2))
    | TNat (i, r) => TNat (simp_i i, r)
    | TiBool (i, r) => TiBool (simp_i i, r)
    | TArray (t, i) => TArray (simp_mt t, simp_i i)
    | TUnit r => TUnit r
    | TProd (t1, t2) => TProd (simp_mt t1, simp_mt t2)
    | TUniI (s, bind, r) => TUniI (simp_s s, simp_bind simp_mt bind, r)
    | TBase a => TBase a
    | TUVar u => TUVar u
    | TVar x => TVar x
    | TAbs (k, bind, r) => TAbs (k, simp_bind simp_mt bind, r)
    | TApp (t1, t2) => TApp (simp_mt t1, simp_mt t2)
    | TAbsI (b, bind, r) => TAbsI (b, simp_bind simp_mt bind, r)
    | TAppI (t, i) =>
      let
        val t = simp_mt t
        val i = simp_i i
      in
        case t of
            TAbsI (_, Bind (_, t), _) => simp_mt (subst_i_mt i t)
          | _ => TAppI (t, i)
      end
    | TDatatype (dt, r) =>
      let
        fun simp_constr c = simp_binds simp_s (mapPair (simp_mt, map simp_i)) c
        fun simp_constr_decl ((name, c, r) : mtype constr_decl) : mtype constr_decl = (name, simp_constr c, r)
        val dt = simp_bind (simp_binds id (mapPair (id, map simp_constr_decl))) dt
      in
        TDatatype (dt, r)
      end
    | TSumbool (s1, s2) => TSumbool (simp_s s1, simp_s s2)
    | TMap t => TMap $ simp_mt t
    | TState _ => t
    | TTuplePtr (ts, n, r) => TTuplePtr (map simp_mt ts, n, r)

fun simp_t t =
  case t of
      PTMono t => PTMono (simp_mt t)
    | PTUni (Bind (name, t), r) => PTUni (Bind (name, simp_t t), r)

end
