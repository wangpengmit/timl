functor TypeUtilFn (Type : TYPE where type name = string * Region.region
                                           and type region = Region.region) = struct

open Type
open Bind
       
infixr 0 $

fun TProd (t1, t2) = TTuple [t1, t2]          
         
fun collect_TUniI t =
  case t of
      TUniI (s, Bind (name, (i, t)), _) =>
      let
        val (binds, t) = collect_TUniI t
      in
        ((name, (s, i)) :: binds, t)
      end
    | _ => ([], t)

fun collect_PTUni t =
  case t of
      PTUni (i, Bind (name, t), _) =>
      let val (names, t) = collect_PTUni t
      in
        ((name, i) :: names, t)
      end
    | PTMono t => ([], t)

fun collect_TAppI t =
  case t of
      TAppI (t, i) =>
      let 
        val (f, args) = collect_TAppI t
      in
        (f, args @ [i])
      end
    | _ => (t, [])
             
fun collect_TApp t =
  case t of
      TApp (t1, t2) =>
      let 
        val (f, args) = collect_TApp t1
      in
        (f, args @ [t2])
      end
    | _ => (t, [])
             
(* fun collect_TProd_left t = *)
(*     case t of *)
(*         TProd (t1, t2) => collect_TProd_left t1 @ [t2] *)
(*       | _ => [t] *)
             
fun is_TApp_TUVar t =
  let
    val (t, t_args) = collect_TApp t
    val (t, i_args) = collect_TAppI t
  in
    case t of
        TUVar (x, r) => SOME ((x, r), i_args, t_args)
      | _ => NONE
  end
    
fun is_TAppV t =
  let
    val (t, i_args) = collect_TAppI t
    val (t, t_args) = collect_TApp t
  in
    case t of
        TVar x => SOME (x, t_args, i_args)
      | _ => NONE
  end
    
fun TAppIs f args = foldl (fn (arg, f) => TAppI (f, arg)) f args
fun TApps f args = foldl (fn (arg, f) => TApp (f, arg)) f args
                          
fun TAbs_Many (ctx, t, r) = foldr (fn ((name, k), t) => TAbs (k, Bind ((name, r), t), r)) t ctx
fun TAbsI_Many (ctx, t, r) = foldr (fn ((name, s), t) => TAbsI (s, Bind ((name, r), t), r)) t ctx
                                 
fun TAppVar (x, is) = TAppIs (TVar x) is
fun TAppV (x, ts, is, r) = TAppIs (TApps (TVar x) ts) is

fun get_constr_inames (core : mtype constr_core) =
  let
    val (name_sorts, _) = unfold_binds core
  in
    map fst $ map fst name_sorts
  end
                                 
fun get_constr_names t =
  case t of
      TDatatype (Bind.Bind (name, tbinds), _) =>
      let
        val (_, (_, constr_decls)) = unfold_binds tbinds
        val cnames = map #1 constr_decls
      in
        cnames
      end
    | _ => []

fun PTUni_Many (names, t, r) = foldr (fn ((name, i), t) => (PTUni (i, Bind (name, t), r))) t names

fun MakeTUniI (s, name, t, r) = TUniI (s, Bind.Bind (name, t), r)

fun TPureArrow (t1, i, t2) = TArrow ((StMap.empty, t1), i, (StMap.empty, t2))

(* fun TCell t = TPtr (t, ([], SOME 0)) *)

fun TArray8 (t, i) = TArray (8, t, i)
            
end
