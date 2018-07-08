(* a special version of forget that allows [uvar] in [uvar arg1 ...] to ignore offending arguments *)

structure UVarForget = struct
open Util
open Expr
open Subst
open Normalize
open FreshUVar

structure SU = SetUtilFn (IntBinarySet)
open SU

open IdxShift
open TypeShift
       
infixr 0 $
infix 0 !!

fun try_forget forget (loc, arg) =
  let
    val arg = forget arg
  in
    inl arg
  end
  handle ForgetError _ => inr loc
                              
fun remove_at_locs locs ls = rev $ foldli (fn (n, x, acc) => if member n locs then acc else x :: acc) [] ls
                                 
fun forget_i_i x n b =
  let
    (* val () = println $ sprintf "Start forgetting $ in $" [str_int x, str_i [] [] b] *)
    val b = normalize_i b
    exception AppUVarFailed
    exception AppUVarSucceeded of idx
    fun on_App_UVar () =
      let
        val body = b
        val forget = forget_i_i x n
        val ((uvar, r), args) = is_IBApp_IUVar body !! (fn () => raise AppUVarFailed)
        val (name, ctx, bsort) = get_uvar_info uvar !! (fn () => raise Impossible "should be fresh")
        val bsort = update_bs bsort
        (* val () = println $ sprintf "  for uvar ?$" [str_int name] *)
        val results = mapi (try_forget forget) args
        val args = filter_inl results
        val () =
            if length args = length results then
              raise AppUVarSucceeded $ IApps (IUVar (uvar, r)) args
            else ()
        val locs = filter_inr results
        val () = assert (fn () => not (null locs)) "not (null locs)"
        val max_loc = max_ls 0 locs
        fun extend_ctx n (ctx, bsort) =
          if n < length ctx then (ctx, bsort)
          else
            let
              val len = length ctx
              val more = n + 1 - len
              val (args, bsort) = collect_BSArrow bsort
              val () = assert (fn () => more <= length args) $ sprintf "UVarForget.forget_i_i(): more <= #args, more=$, #args=$" [str_int more, str_int $ length args]
              val (args1, args2) = (take more args, drop more args)
              val bsort = combine_BSArrow (args2, bsort)
              val args1 = rev args1
              fun var_name n = "__x" ^ str_int n
              val ctx = mapi (mapFst var_name) args1 @ ctx
            in
              (ctx, bsort)
            end
        val (ctx, bsort) = extend_ctx max_loc (ctx, bsort)
        val length_ctx = length ctx
        val () = assert (fn () => max_loc < length_ctx) "max_loc < length ctx"
        val locs = map (fn n => length_ctx - 1 - n) locs
        val locs = to_set locs
        val ctx' = remove_at_locs locs ctx
        val new_uvar = IUVar (fresh_uvar_i ctx' bsort, r)
        val ret = IApps new_uvar args
        val inner_args = range length_ctx
        val inner_args = remove_at_locs locs inner_args
        val ins = new_uvar
        val ins = IApps ins (map (V r) $ rev inner_args)
        val ins = IAbs_Many (rev ctx, ins, r)
        val () = refine uvar ins
      in
        ret
      end
    fun structural () =
      let
        open LongIdSubst
        val f = forget_i_i
        val on_v = forget_v
      in
        case b of
	    IVar (y, anno) => IVar (on_v_long_id on_v x n y, [])
          | IConst _ => b
          | IUnOp (opr, i, r) => IUnOp (opr, f x n i, r)
	  | IBinOp (opr, i1, i2) => IBinOp (opr, f x n i1, f x n i2)
          | IIte (i1, i2, i3, r) => IIte (f x n i1, f x n i2, f x n i3, r)
          | IAbs (b, bind, r) => IAbs (b, on_i_ibind f x n bind, r)
          | IState st => IState $ StMap.map (f x n) st
          | IUVar a => b (* uvars are closed, so no need to deal with *)
      end
    val ret =
        on_App_UVar ()
        handle AppUVarFailed => structural ()
             | AppUVarSucceeded i => i
    (* val () = println $ "Finish forgetting" *)
  in
    ret
  end

fun new_on_i_idx_visitor' on_i =
  let
    fun on_var _ _ = raise Impossible "on_i_p'()/on_var"
    val (IdxVisitor vtable) = new_on_i_idx_visitor on_var
    fun visit_idx _ env i = on_i env i
    val vtable = override_visit_idx vtable visit_idx
    val visitor = IdxVisitor vtable
  in
    visitor
  end

fun on_i_p' on_i b =
  let
    val visitor as (IdxVisitor vtable) = new_on_i_idx_visitor' on_i
  in
    #visit_prop vtable visitor 0 b
  end

fun on_i_s' on_i b =
  let
    val visitor as (IdxVisitor vtable) = new_on_i_idx_visitor' on_i
  in
    #visit_sort vtable visitor 0 b
  end
    
fun adapt f x n env = f (x + env) n
fun forget_i_p x n b = on_i_p' (adapt forget_i_i x n) b
fun forget_i_s x n b = on_i_s' (adapt forget_i_i x n) b
                              
(* fun forget_i_mt x n b = on_i_mt forget_i_i forget_i_s forget_i_k x n b *)
fun forget_i_mt x n b =
  let
    (* val () = println $ sprintf "Start forgetting $ in $" [str_int x, str_i [] [] b] *)
    val b = update_mt b
    exception AppUVarFailed
    exception AppUVarSucceeded of mtype
    fun on_App_UVar () =
      let
        val body = b
        val forget = forget_i_mt x n
        val ((uvar, r), i_args, t_args) = is_TApp_TUVar body !! (fn () => raise AppUVarFailed)
        val (uvar_name, ctx as (sctx : (string * basic_sort) list, kctx)) = get_uvar_info uvar !! (fn () => raise Impossible "should be fresh")
        (* val () = println $ sprintf "  for uvar ?$" [str_int uvar_name] *)
        val i_results = mapi (try_forget (forget_i_i x n)) i_args
        val t_results = mapi (try_forget forget) t_args
        val i_args = filter_inl i_results
        val t_args = filter_inl t_results
        val () =
            if length i_args = length i_results andalso length t_args = length t_results then
              raise AppUVarSucceeded $ TApps (TAppIs (TUVar (uvar, r)) i_args) t_args
            else ()
        val i_locs = filter_inr i_results
        val t_locs = filter_inr t_results
        val length_sctx = length sctx
        val length_kctx = length kctx
        val i_locs = map (fn n => length_sctx - 1 - n) i_locs
        val t_locs = map (fn n => length_kctx - 1 - n) t_locs
        val i_locs = to_set i_locs
        val t_locs = to_set t_locs
        (* val () = println $ "sctx=" ^ str_ls fst sctx *)
        val sctx' = remove_at_locs i_locs sctx
        (* val () = println $ "sctx'=" ^ str_ls fst sctx' *)
        val kctx' = remove_at_locs t_locs kctx
        val new_uvar = TUVar (fresh_uvar_mt (sctx', kctx'), r)
        (* val () = println $ "forget_i_mt() created new uvar " ^ str_mt empty ([], []) new_uvar *)
        val ret = TApps (TAppIs new_uvar i_args) t_args
        val inner_i_args = range length_sctx
        val inner_t_args = range length_kctx
        val inner_i_args = remove_at_locs i_locs inner_i_args
        val inner_t_args = remove_at_locs t_locs inner_t_args
        val ins = new_uvar
        val ins = TAppIs ins (map (V r) $ rev inner_i_args)
        val ins = TApps ins (map (TV r) $ rev inner_t_args)
        val ins = TAbs_Many (rev kctx, ins, r)
        val ins = TAbsI_Many (rev sctx, ins, r)
        (* val () = println $ sprintf "forget_i_mt(): refine ?$ to be $" [str_int uvar_name, str_mt empty ([], []) ins] *)
        val () = refine uvar ins
      in
        ret
      end
    fun structural () =
      let
        val f = forget_i_mt
        val on_i_i = forget_i_i
        val on_i_s = forget_i_s
        fun on_pair f1 f2 x n (a1, a2) = (f1 x n a1, f2 x n a2)
      in
        case b of
	    TArrow ((st1, t1), (i, j), (st2, t2)) => TArrow ((StMap.map (on_i_i x n) st1, f x n t1), (on_i_i x n i, on_i_i x n j), (StMap.map (on_i_i x n) st2, f x n t2))
          | TNat (i, r) => TNat (on_i_i x n i, r)
          | TiBool (i, r) => TiBool (on_i_i x n i, r)
          | TArray (t, i) => TArray (f x n t, on_i_i x n i)
          | TUnit r => TUnit r
	  | TProd (t1, t2) => TProd (f x n t1, f x n t2)
	  | TUniI (s, bind, r) => TUniI (on_i_s x n s, on_i_ibind (on_pair (on_pair on_i_i on_i_i) f) x n bind, r)
          (* | TSumbool (s1, s2) => TSumbool (on_i_s x n s1, on_i_s x n s2) *)
          | TVar y => TVar y
          | TApp (t1, t2) => TApp (f x n t1, f x n t2)
          | TAbs (k, bind, r) => TAbs (k, on_i_tbind f x n bind, r)
          | TAppI (t, i) => TAppI (f x n t, on_i_i x n i)
          | TAbsI (b, bind, r) => TAbsI (b, on_i_ibind f x n bind, r)
	  | TBase a => TBase a
          | TUVar a => b
          | TDatatype _ => raise Unimpl "uvar_forget/forget_i_mt()/TDatatype"
          | TMap t => TMap $ f x n t
          | TVector t => TVector $ f x n t
          | TState _ => b
          (* | TTuplePtr (ts, n, r) => TTuplePtr (map (f x n) ts, n, r) *)
          | TPtr t => TPtr (f x n t)
      end
    val ret =
        on_App_UVar ()
        handle AppUVarFailed => structural ()
             | AppUVarSucceeded i => i
    (* val () = println $ "Finish forgetting" *)
  in
    ret
  end
                                
fun new_on_i_type_visitor' visit_mtype =
  let
    fun imposs _ _ = raise Impossible "on_i_t'()/imposs"
    val (TypeVisitor vtable) = new_on_i_type_visitor (imposs, imposs)
    val vtable = override_visit_mtype vtable $ ignore_this visit_mtype
    val visitor = TypeVisitor vtable
  in
    visitor
  end

fun on_i_t' params b =
  let
    val visitor as (TypeVisitor vtable) = new_on_i_type_visitor' params
  in
    #visit_ty vtable visitor 0 b
  end
    
fun forget_i_t x n b = on_i_t' (adapt forget_i_mt x n) b

end
