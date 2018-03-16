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
    | _ => raise assert_fail $ "assert_TArrow; got: " ^ (ExportPP.pp_t_to_string NONE $ ExportPP.export_t NONE ([], []) t)
                 
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
    | _ => raise assert_fail $ "assert_TAbsT; got: " ^ (ExportPP.pp_t_to_string NONE $ ExportPP.export_t NONE ([], []) t)
fun assert_TAbsI t =
  case t of
      TAbsI bind => unBindAnno bind
    | _ => raise assert_fail "assert_TAbsI"
fun assert_TForall t =
  case t of
      TQuan (Forall, bind) => unBindAnno bind
    | _ => raise assert_fail $ "assert_TForall; got: " ^ (ExportPP.pp_t_to_string NONE $ ExportPP.export_t NONE ([], []) t)
fun assert_TForallI t =
  case t of
      TQuanI (Forall, bind) => unBindAnno bind
    | _ => raise assert_fail $ "assert_TForallI; got: " ^ (ExportPP.pp_t_to_string NONE $ ExportPP.export_t NONE ([], []) t)

fun assert_TExists t =
  case t of
      TQuan (Exists _, bind) => unBindAnno bind
    | _ => raise assert_fail $ "assert_TExists; got: " ^ (ExportPP.pp_t_to_string NONE $ ExportPP.export_t NONE ([], []) t)
fun assert_TExistsI t =
  case t of
      TQuanI (Exists _, bind) => unBindAnno bind
    | _ => raise assert_fail $ "assert_TExistsI; got: " ^ (ExportPP.pp_t_to_string NONE $ ExportPP.export_t NONE ([], []) t)
fun assert_TRec t =
  case t of
      TRec bind => unBindAnno bind
    | _ => raise assert_fail $ "assert_TRec; got: " ^ (ExportPP.pp_t_to_string NONE $ ExportPP.export_t NONE ([], []) t)

fun assert_TUnit msg t =
  case t of
      TConst TCUnit => ()
    | _ => raise assert_fail msg
                 
fun assert_EAbs e =
  case e of
      EAbs bind => unBindAnnoName bind
    | _ => raise assert_fail "assert_EAbs"
                 
fun assert_EAscType e =
  let
    val (e, is) = collect_EAscTime e
  in
    case e of
        EAscType (e, t) => (EAscTimes (e, is), t)
      | _ => raise assert_fail $ "assert_EAscType; got:\n" ^ (ExportPP.pp_e_to_string (NONE, NONE) $ ExportPP.export (NONE, NONE) ([], [], [], []) e)
  end
    
fun assert_EAscTime e =
  let
    val (e, ts) = collect_EAscType e
  in
    case e of
        EAscTime (e, i) => (EAscTypes (e, ts), i)
      | _ => raise assert_fail $ "assert_EAscTime; got:\n" ^ (ExportPP.pp_e_to_string (NONE, NONE) $ ExportPP.export (NONE, NONE) ([], [], [], []) e)
  end
    
fun EV x = EVar $ make_Free_e x
                
fun ELetClose ((x, name, e1), e2) = MakeELet (e1, (name, dummy), close0_e_e x e2)
fun ELetManyClose (ds, e) = foldr ELetClose e ds

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
                     
fun EAbsIT (bind, e) =
    case bind of
        inl bind => EAbsI $ IBindAnno (bind, e)
      | inr bind => EAbsT $ TBindAnno (bind, e)
fun EAbsITs (binds, e) = foldr EAbsIT e binds
                                      
fun TForallIT (bind, e) =
    case bind of
        inl bind => TForallI $ IBindAnno (bind, e)
      | inr bind => TForall $ TBindAnno (bind, e)
fun TForallITs (binds, e) = foldr TForallIT e binds
                                      
fun EAscTypeTime (e, arg) =
    case arg of
        inr i => EAscTime (e, i)
      | inl t => EAscType (e, t)
fun EAscTypeTimes (f, args) = foldl (swap EAscTypeTime) f args
                     
fun open_collect_TForallIT_whnf whnf t =
  case t of
      TQuanI (Forall, bind) =>
      let
        val (s, (name, t)) = unBindAnnoName bind
        val x = fresh_ivar ()
        val t = open0_i_t x t
        val (binds, t) = open_collect_TForallIT_whnf whnf t
      in
        (inl (x, fst name, s) :: binds, t)
      end
    | TQuan (Forall, bind) =>
      let
        val (k, (name, t)) = unBindAnnoName bind
        val x = fresh_tvar ()
        val t = open0_t_t x t
        val (binds, t) = open_collect_TForallIT_whnf whnf t
      in
        (inr (x, fst name, k) :: binds, t)
      end
    | _ => ([], t)

fun collect_TForallIT_open_with_whnf whnf vars t =
  case t of
      TQuanI (Forall, bind) =>
      let
        val (s, (name, t)) = unBindAnnoName bind
        val (x, vars) = case vars of
                    inl (x, _, _) :: vars => (x, vars)
                  | _ => raise Impossible "collect_TForallIT_open_with_whnf whnf"
        val t = open0_i_t x t
        val (binds, t) = collect_TForallIT_open_with_whnf whnf vars t
      in
        (inl (x, fst name, s) :: binds, t)
      end
    | TQuan (Forall, bind) =>
      let
        val (k, (name, t)) = unBindAnnoName bind
        val (x, vars) = case vars of
                    inr (x, _, _) :: vars => (x, vars)
                  | _ => raise Impossible "collect_TForallIT_open_with_whnf whnf"
        val t = open0_t_t x t
        val (binds, t) = collect_TForallIT_open_with_whnf whnf vars t
      in
        (inr (x, fst name, k) :: binds, t)
      end
    | _ => ([], t)

fun open_collect_TForallIT t = open_collect_TForallIT_whnf id t
fun collect_TForallIT_open_with vars t = collect_TForallIT_open_with_whnf id vars t
    
fun open_collect_EAbsIT e =
  case e of
      EAbsI bind =>
      let
        val (s, (name, e)) = unBindAnnoName bind
        val x = fresh_ivar ()
        val e = open0_i_e x e
        val (binds, e) = open_collect_EAbsIT e
      in
        (inl (x, fst name, s) :: binds, e)
      end
    | EAbsT bind =>
      let
        val (k, (name, e)) = unBindAnnoName bind
        val x = fresh_tvar ()
        val e = open0_t_e x e
        val (binds, e) = open_collect_EAbsIT e
      in
        (inr (x, fst name, k) :: binds, e)
      end
    | _ => ([], e)

fun close_TForallIT (bind, t) =
    case bind of
        inl (x, name, s) => TForallI $ close0_i_t_anno ((x, name, s), t)
      | inr (x, name, k) => TForall $ close0_t_t_anno ((x, name, k), t)
fun close_TForallITs (binds, t) = foldr close_TForallIT t binds
                                      
fun close_EAbsIT (bind, e) =
    case bind of
        inl (x, name, s) => EAbsI $ close0_i_e_anno ((x, name, s), e)
      | inr (x, name, k) => EAbsT $ close0_t_e_anno ((x, name, k), e)
fun close_EAbsITs (binds, t) = foldr close_EAbsIT t binds
                                      
fun reduce_ELets e =
    case fst $ collect_EAscTypeTime e of
        ELet (e1, bind) =>
        let
          val (name_x, e2) = unBindSimpName bind
        in
          reduce_ELets $ subst0_e_e e1 e2
        end
      | _ => e
               
fun collect_TForallIT b =
  case b of
      TQuanI (Forall, bind) =>
      let
        val (s, (name, b)) = unBindAnnoName bind
        val (binds, b) = collect_TForallIT b
      in
        (inl (name, s) :: binds, b)
      end
    | TQuan (Forall, bind) =>
      let
        val (k, (name, b)) = unBindAnnoName bind
        val (binds, b) = collect_TForallIT b
      in
        (inr (name, k) :: binds, b)
      end
    | _ => ([], b)

end
