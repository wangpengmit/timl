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

fun assert_fail msg = Impossible $ "Assert failed: " ^ msg
                             
fun assert_TArrow t =
  case t of
      TArrow a => a
    | _ => raise assert_fail "assert_TArrow"
                 
fun assert_EAscType e =
  let
    val (e, is) = collect_EAscTime e
  in
    case e of
        EAscType (e, t) => (EAscTimes (e, is), t)
      | _ => raise assert_fail "assert_EAscType"
  end
    
fun assert_EAscTime e =
  let
    val (e, ts) = collect_EAscType e
  in
    case e of
        EAscTime (e, i) => (EAscTypes (e, ts), i)
      | _ => raise assert_fail "assert_EAscTime"
  end
    
fun EV x = EVar $ make_Free_e x
                
fun ELetClose ((x, name, e1), e2) = MakeELet (e1, (name, dummy), close0_e_e x e2)
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
                     
end
