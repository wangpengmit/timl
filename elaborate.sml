structure Elaborate = struct
structure S = Ast
structure E = NamefulExpr
open S
open E
open Pervasive
open Bind
       
infixr 0 $

infix  9 @!
fun m @! k = StMap.find (m, k)
infix  6 @+
fun m @+ a = StMap.insert' (a, m)
                           
exception Error of region * string

val add_pervasive_flag = ref false
                             
local

  fun runError m _ =
    OK (m ())
    handle
    Error e => Failed e

  val un_ops = [IUToReal (), IULog2, IULog10, IUCeil (), IUFloor (), IUB2n (), IUNeg ()]
  val un_op_names = zip (un_ops, map str_idx_un_op un_ops)
  fun is_un_op (opr, i1) =
    case (opr, i1) of
        (IBApp (), S.IVar (NONE, (x, r1))) => find_by_snd_eq op= x un_op_names
      | _ => NONE

  fun is_ite i =
    case i of
        S.IBinOp (IBApp (), S.IBinOp (IBApp (), S.IBinOp (IBApp (), S.IVar (NONE, (x, _)), i1, _), i2, _), i3, _) =>
        if x = "ite" then SOME (i1, i2, i3)
        else NONE
      | _ => NONE
               
  fun to_long_id (m, x) =
    case m of
        NONE => ID x
      | SOME m => QID (m, x)

  fun elab_int r s = assert_SOME_m (fn () => raise Error (r, "failed when parsing the integer")) $ str2int s
  fun elab_large_int r s = assert_SOME_m (fn () => raise Error (r, "failed when parsing the integer")) $ str2large_int s
                                   
  fun elab_i i =
    case i of
	S.IVar (id as (m, (x, r))) =>
        (case m of
             NONE =>
	     if x = "true" then
	       ITrue r
	     else if x = "false" then
	       IFalse r
             else if x = "admit" then
               IAdmit r
             else if x = "_" then
               IUVar ((), r)
	     else
	       IVar (to_long_id id, [])
           | SOME _ => IVar (to_long_id id, [])
        )
      | S.INat (n, r) =>
	INat (elab_int r n, r)
      | S.ITime (x, r) =>
        let
          infixr 0 !!
          val x = TimeType.fromString x !! (fn () => raise Error (r, sprintf "Wrong time literal: $" [x]))
        in
	  ITime (x, r)
        end
      (* | S.IUnOp (opr, i, r) => IUnOp (opr, elab_i i, r) *)
      | S.IDiv (i1, (n2, r), _) => IDiv (elab_i i1, (elab_int r n2, r))
      | S.IBinOp (opr, i1, i2, r) =>
        (case is_un_op (opr, i1) of
             SOME opr => IUnOp (opr, elab_i i2, r)
           | NONE =>
             case is_ite i of
                 SOME (i1, i2, i3) => IIte (elab_i i1, elab_i i2, elab_i i3, r)
	       | NONE =>IBinOp (opr, elab_i i1, elab_i i2)
        )
      | S.ITT r =>
	ITT r
      | S.IAbs (names, i, r) =>
        foldr (fn (name, i) => IAbs (BSUVar (), Bind (name, i), r)) (elab_i i) names

  fun elab_p p =
    case p of
	PConst (name, r) =>
	if name = "True" then
	  PTrue r
	else if name = "False" then
	  PFalse r
	else raise Error (r, sprintf "Unrecognized proposition: $" [name])
      | S.PNot (p, r) => PNot (elab_p p, r)
      | S.PBinConn (opr, p1, p2, _) => PBinConn (opr, elab_p p1, elab_p p2)
      | S.PBinPred (opr, i1, i2, _) => PBinPred (opr, elab_i i1, elab_i i2)

  fun TimeFun n =
    if n <= 0 then BSTime
    else BSArrow (BSNat, TimeFun (n-1))

  fun elab_b b =
    case b of
        S.BSId (name, r) =>
	if name = "Time" then
	  (BSBase (BSSTime ()), r)
	else if name = "Nat" then
	  (BSBase (BSSNat ()), r)
	else if name = "Bool" then
	  (BSBase (BSSBool ()), r)
	else if name = "Unit" then
	  (BSBase (BSSUnit ()), r)
        else if name = "_" then
          (BSUVar (), r)
	else raise Error (r, sprintf "Unrecognized base sort: $" [name])

  fun elab_s s =
    case s of
	S.SBasic b =>
        (case elab_b b of
             (BSUVar (), r) => SUVar ((), r)
           | b => SBasic b
        )
      | S.SSubset (b, name, p, r) => SSubset (elab_b b, Bind (name, elab_p p), r)
      | S.SBigO (name, b, i, r) =>
        let
          fun SBigO (bs, i, r) =
            let
              val name = "__f"
            in
              SSubset (bs, Bind ((name, r), PBinPred (BPBigO (), IVar (ID (name, r), []), i)), r)
            end
        in
          if name = "BigO" then
            SBigO (elab_b b, elab_i i, r)
          else
            raise Error (r, sprintf "Unrecognized sort: $" [name])
        end

  fun get_is t =
    case t of 
	S.TAppI (t, i, _) =>
	let val (t, is) = get_is t in
	  (t, is @ [i])
	end
      | _ => (t, [])

  fun get_ts t =
    case t of 
	S.TAppT (t, t2, _) =>
	let val (t, ts) = get_ts t in
	  (t, ts @ [t2])
	end
      | _ => (t, [])

  fun is_var_app_ts t = 
    let val (t, ts) = get_ts t in
      case t of
	  S.TVar x => SOME (x, ts)
	| _ => NONE
    end

  fun IUnderscore r = IUVar ((), r)
  fun TUnderscore r = TUVar ((), r)
  fun IUnderscore2 r = (IUnderscore r, IUnderscore r)
                         
  fun elab_state r ls =
    let
      fun check_new_key m k =
        case m @! k of
            SOME _ => raise Error (r, sprintf "state field $ already exists" [k])
          | NONE => ()
    in
      foldl (fn (((k, _), v), m) => (check_new_key m k; m @+ (k, elab_i v))) StMap.empty ls
    end
      
  fun list2map r fields =
    let
      val fields = map (mapFst fst) fields
      val m = SMapU.fromList fields
      val () = if length fields = SMap.numItems m then ()
               else raise Error (r, "duplicate field names")
    in
      m
    end
      
  fun elab_mt t =
    case t of
	S.TVar (id as (m, (x, r))) =>
        let
          fun def () = TAppV (to_long_id id, [], [], r)
        in
          case m of
              NONE =>
              if x = "unit" then
                TUnit r
              else if x = "icell" then
                TNatCell r
              else if x = "address" then
                TInt r
              else if x = "uint" then
                TInt r
              else if x = "uint8" then
                TInt r
              else if x = "uint16" then
                TInt r
              else if x = "uint32" then
                TInt r
              else if x = "uint64" then
                TInt r
              else if x = "uint128" then
                TInt r
              else if x = "uint256" then
                TInt r
              else if x = "int" then
                TInt r
              else if x = "int8" then
                TInt r
              else if x = "int16" then
                TInt r
              else if x = "int32" then
                TInt r
              else if x = "int64" then
                TInt r
              else if x = "int128" then
                TInt r
              else if x = "int256" then
                TInt r
              else if x = "bytes4" then
                TInt r
              else if x = "bytes8" then
                TInt r
              else if x = "bytes16" then
                TInt r
              else if x = "bytes32" then
                TInt r
                     (* else if x = "bytes" then *)
                     (*   TInt r *)
              else if x = "bool" then
                TBool r
              else if x = "byte" then
                TByte r
              else if x = "char" then
                TByte r
                      (* else if x = "string" then *)
                      (*   BaseType (String, r) *)
              else if x = "_" then
                TUVar ((), r)
              else
                def ()
            | SOME _ => def ()
        end
      | S.TArrow ((st1, t1), (j, i), (st2, t2), r) => TArrow ((elab_state r st1, elab_mt t1), (elab_i j, elab_i i), (elab_state r st2, elab_mt t2))
      (* | S.TProd (t1, t2, _) => TProd (elab_mt t1, elab_mt t2) *)
      | S.TTuple (ts, r) =>
	(case ts of
	     [] => raise Error (r, "TTuple must have components")
           (* | [t] => elab_mt t *)
           | [t] => raise Error (r, "TTuple must have at least two components")
	   | _ :: _ => TTuple $ map elab_mt ts
        )
      | S.TQuan (quan, binds, t, r) =>
	let
          fun f (((x, s, r1), (i, j)), t) =
	    case quan of
		S.Forall () =>
                TUniI (elab_s s, Bind (x, ((elab_i i, elab_i j), t)), r)
	in
	  foldr f (elab_mt t) binds
	end
      | S.TAppT (t1, t2, r) =>
	(case is_var_app_ts t1 of
	     SOME (x, ts) => TAppV (to_long_id x, map elab_mt (ts @ [t2]), [], r)
	   | NONE => raise Error (r, "Head of type-type application must be a variable"))
      | S.TAppI (t, i, r) =>
	let val (t, is) = get_is t 
	    val is = is @ [i]
	in
	  case is_var_app_ts t of
	      SOME (x, ts) => TAppV (to_long_id x, map elab_mt ts, map elab_i is, r)
	    | NONE => raise Error (r, "The form of type-index application can only be [Variable Types Indices]")
	end
      | S.TAbs (binds, t, r) =>
	let fun f (bind, t) =
              case bind of
                  inr (x, b, _) => TAbsI (fst $ elab_b b, Bind (x, t), r)
                | inl x => TAbs (Type, Bind (x, t), r)
	in
	  foldr f (elab_mt t) binds
	end
      | S.TRecord (fields, r) =>
        TRecord (list2map r $ map (mapSnd elab_mt) fields, r)
      | S.TPtr t => TPtr $ elab_mt t

  fun elab_return (t, i, j) = (Option.map elab_mt t, Option.map elab_i i, Option.map elab_i j)
                                
  fun elab_pn pn =
    case pn of
        S.PnConstr ((name, eia), inames, pn, r) =>
        if isNone (fst name) andalso not eia andalso null inames andalso isNone pn then
          PnVar $ Binder $ EName (snd name)
        else
          PnConstr (Outer ((to_long_id name, ()), eia), map str2ibinder inames, default (PnTT r) $ Option.map elab_pn pn, r)
      | S.PnTuple (pns, r) =>
        (case pns of
             [] => PnTT r
           | [pn] => elab_pn pn
           | _ :: _ => PnTuple $ map elab_pn pns
        )
      | S.PnAlias (name, pn, r) =>
        PnAlias (Binder $ EName name, elab_pn pn, r)
      | S.PnAnno (pn, t, r) =>
        PnAnno (elab_pn pn, Outer $ elab_mt t)
  (*                                                              
    and copy_anno (t, d) =
        let
          fun loop e =
              case e of
                  S.Case (e, (t', d'), es, r) =>
                  let
                    fun copy a b = case a of
                                       NONE => b
                                     | SOME _ => a
                  in
                    S.Case (e, (copy t' t, copy d' d), es, r)
                  end
                | S.Let (decls, e, r) => S.Let (decls, loop e, r)
                | _ => e
        in
          loop
        end
    *)

  fun partitionSum f ls = mapPair (rev, rev) $ foldl (fn (x, (acc1, acc2)) => case f x of
                                                                                  inl a => (a :: acc1, acc2) |
                                                                                  inr b => (acc1, b :: acc2)) ([], []) ls
                                  
  fun elab_datatype ((name, tnames, top_sortings, sorts, constrs, r) : S.datatype_def) : mtype datatype_def * region =
    let
      val sorts = map (fst o elab_b) (map (fn (_, s, _) => s) top_sortings @ sorts)
      fun default_t2 r = foldl (fn (arg, f) => S.TAppT (f, S.TVar (NONE, (arg, r)), r)) (S.TVar (NONE, (name, r))) tnames
      fun elab_constr ((cname, binds, core, r) : S.constr_decl) : mtype constr_decl =
        let
          (* val (t1, t2) = default (S.TVar ("unit", r), SOME (default_t2 r)) core *)
          (* val t2 = default (default_t2 r) t2 *)
          val (t1, t2) =
              case core of
                  NONE => (S.TVar (NONE, ("unit", r)), default_t2 r)
                | SOME (t1, NONE) => (S.TVar (NONE, ("unit", r)), t1)
                | SOME (t1, SOME t2) => (t1, t2)
          fun f (name, sort, r) = (name, elab_s sort)
          val binds = map f (map (fn (name, b, r) => (name, S.SBasic b, r)) top_sortings @ binds)
          val t2_orig = t2
          val (t2, is) = get_is t2
          val (t2, ts) = get_ts t2
          val () = if case t2 of S.TVar (NONE, (x, _)) => x = name | _ => false then
                     ()
                   else
                     raise Error (S.get_region_t t2, sprintf "Result type of constructor must be $ (did you use -> when you should you --> ?)" [name])
          val () = if length ts = length tnames then () else raise Error (S.get_region_t t2_orig, "Must have type arguments " ^ join " " tnames)
          fun f (t, tname) =
            let
              val targ_mismatch = "This type argument must be " ^ tname
            in
              case t of
                  S.TVar (NONE, (x, r)) => if x = tname then () else raise Error (r, targ_mismatch)
                | _ => raise Error (S.get_region_t t, targ_mismatch)
            end
          val () = app f (zip (ts, tnames))
        in
          (cname, fold_binds (binds, (elab_mt t1, map elab_i is)), r)
        end
      val dt = Bind ((name, dummy), fold_binds (map (attach_snd ()) $ map (attach_snd dummy) tnames, (sorts, map elab_constr constrs)))
    in
      (dt, r)
    end

  val empty_return = (NONE, NONE, NONE)

  val state_decls_ref = ref ([] : (name * S.ty * exp option) list)
  (* val state_inits_ref = ref ([] : (name * init) list) *)
                            
  fun process_mods ls =
    let
      val (pre, post, return, time, space) =
          (ref $ NONE, ref $ NONE, ref $ NONE, ref $ NONE, ref $ NONE)
      val guards = ref []
      fun f m =
        case m of
            FmPre v => pre := SOME v
          | FmPost v => post := SOME v
          | FmReturn v => return := SOME v
          | FmTime v => time := SOME v
          | FmSpace v => space := SOME v
          | FmGuards es => unop_ref (fn acc => rev es @ acc) guards
          | FmView () => ()
          | FmPure () => ()
          | FmPayable () => ()
          | FmConst () => ()
          | FmVisi _ => ()
      val () = app f ls
    in
      (!pre, !post, !return, !time, !space, rev (!guards))
    end

  fun elab_path ls = map (fn (p, r) => (map_inl_inr (elab_int r) id p, r)) ls
      
  fun elab e =
    case e of
	S.EVar (id as (m, (x, r)), (eia, has_insert)) =>
        let
          fun def () = EVar (to_long_id id, (eia, has_insert))
          val no_decorate = not eia andalso not has_insert
        in
          case m of
              NONE =>
              if no_decorate andalso x = "__&true" then
                EConst (ECBool true, r)
              else if no_decorate andalso x = "true" then
                EConst (ECBool true, r)
              else if no_decorate andalso x = "__&false" then
                EConst (ECBool false, r)
              else if no_decorate andalso x = "false" then
                EConst (ECBool false, r)
              else if no_decorate andalso x = "__&itrue" then
                EConst (ECiBool true, r)
              else if no_decorate andalso x = "__&ifalse" then
                EConst (ECiBool false, r)
                       (* else if no_decorate andalso x = "never" then *)
                       (*   ENever (elab_mt (S.TVar (NONE, ("_", r))), r) *)
              else if no_decorate andalso (x = "__&empty_array" orelse x = "empty_array") then
                EEmptyArray (elab_mt (S.TVar (NONE, ("_", r))), r)
              else if x = "__&builtin" then raise Error (r, "should be '__&builtin \"name\"'")
              else
                def ()
            | SOME _ => def ()
        end
      | S.ETuple (es, r) =>
	(case es of
	     [] => ETT r
           | [e] => elab e
	   | _ :: _ => ETuple $ map elab es
        )
      | S.EAbs (binds, mods, e, r) =>
	let 
          val (pre, post, t, d, j, guards) = process_mods mods
          val pre = default empty_state pre
          val is_first = ref true
          fun get_pre () =
            if !is_first then
              (is_first := false;
               elab_state r pre)
            else
              StMap.empty
          fun f (b, e) =
	    case b of
		BindTyping pn => EAbs (get_pre (), Unbound.Bind (elab_pn pn, e), NONE)
	      | BindSorting (name, s, _) => EAbsI (BindAnno ((IName name, elab_s s), e), r)
          val e = elab e
          val e = case d of SOME d => EAscTime (e, elab_i d) | _ => e
          val e = case j of SOME j => EAscSpace (e, elab_i j) | _ => e
          val e = case t of SOME t => EAsc (e, elab_mt t) | _ => e
	in
	  foldr f e binds
	end
      | S.EAppI (e, i, _) =>
	EAppI (elab e, elab_i i)
      | S.ECase (e, return, rules, r) =>
	let
          (* val rules = map (mapSnd (copy_anno return)) rules *)
	in
	  ECase (elab e, elab_return return, map (fn (pn, e) => Unbound.Bind (elab_pn pn, elab e)) rules, r)
	end
      | S.EAsc (e, t, _) =>
	EAsc (elab e, elab_mt t)
      | S.EAscTime (e, i, _) =>
	EAscTime (elab e, elab_i i)
      | S.EAscSpace (e, i, _) =>
	EAscSpace (elab e, elab_i i)
      | S.EAscState (e, st, r) =>
	EAscState (elab e, elab_state r st)
      | S.ELet (return, decs, e, r) =>
        ELet (elab_return return, Unbound.Bind (Teles $ concatMap elab_decl decs, elab e), r)
      | S.EConst (c, r) =>
        (case c of
             S.ECInt n => EConstInt (elab_large_int r n, r)
	   | S.ECNat n => EConstNat (elab_int r n, r)
	   | S.ECChar n => EConstByte (n, r)
	   | S.ECString s =>
             let
               fun unescape s =
                 let
                   val ls = String.explode s
                   fun loop (ls, acc) =
                     case ls of
                         #"\\" :: #"n" :: ls => loop (ls, #"\n" :: acc)
                       | c :: ls => loop (ls, c :: acc)
                       | [] => acc
                 in
                   String.implode $ rev $ loop (ls, [])
                 end
               val s = unescape s
               val e = ENewArrayValues (TByte r, map (fn c => EByte (c, r)) $ String.explode s, r)
                                       (* val e = EApp (EVar (QID $ qid_add_r r $ CSTR_STRING_NAMEFUL, false), e) *)
             in
               e
             end
           | S.ECZero () => raise Error (r, "elaborate/ECZero")
           | S.ECNow () => EEnv (EnvNow (), r)
           | S.ECThis () => EEnv (EnvThis (), r)
           | S.ECBalance () => EEnv (EnvBalance (), r)
           | S.ECState x => EState (x, r)
        )
      | S.EBinOp (EBTiML (EBApp ()), e1, e2, r) =>
	let 
	  fun default () = EApp (elab e1, elab e2)
	in
	  case e1 of
	      S.EVar ((m, (x, _)), (false, false)) =>
              (case m of
                   NONE =>
		   if x = "__&fst" then EFst (elab e2, r)
		   else if x = "__&snd" then ESnd (elab e2, r)
		   else if x = "ref" then ENewArrayValues (TUVar ((), r), [elab e2], r)
		   else if x = "__&not" then EUnOp (EUPrim (EUPBoolNeg ()), elab e2, r)
		                                   (* else if x = "__&int2str" then EUnOp (EUInt2Str, elab e2, r) *)
		   else if x = "__&nat2int" then EUnOp (EUNat2Int (), elab e2, r)
		   else if x = "nat2int" then EUnOp (EUNat2Int (), elab e2, r)
		   else if x = "__&int2nat" then EUnOp (EUInt2Nat (), elab e2, r)
		   else if x = "int2nat" then EUnOp (EUInt2Nat (), elab e2, r)
		   else if x = "__&byte2int" then EUnOp (EUPrim (EUPByte2Int ()), elab e2, r)
		   else if x = "__&int2byte" then EUnOp (EUPrim (EUPInt2Byte ()), elab e2, r)
		   else if x = "int2byte" then EUnOp (EUPrim (EUPInt2Byte ()), elab e2, r)
		   else if x = "__&array_length" then EUnOp (EUArrayLen (), elab e2, r)
		   else if x = "array_len" then EUnOp (EUArrayLen (), elab e2, r)
		   else if x = "vector_len" then EUnOp (EUVectorLen (), elab e2, r)
		   else if x = "vector_clear" then EUnOp (EUVectorClear (), elab e2, r)
		                                         (* else if x = "__&print" then EUnOp (EUPrint, elab e2, r) *)
		   else if x = "__&printc" then EUnOp (EUPrintc (), elab e2, r)
		   else if x = "__&halt" then EET (EETHalt (), elab e2, elab_mt (S.TVar (NONE, ("_", r))))
		   else if x = "halt" then EET (EETHalt (), elab e2, elab_mt (S.TVar (NONE, ("_", r))))
                   else if x = "__&builtin" then
                     (case e2 of
                          S.EConst (S.ECString s, _) =>
                          EBuiltin (s, elab_mt (S.TVar (NONE, ("_", r))), r)
                        | _ => raise Error (r, "should be '__&builtin \"name\"'"))
		   else if x = "__&array" orelse x = "new_array" then
                     (case e2 of
                          S.ETuple ([e1, e2], _) =>
                          ENew (elab e1, elab e2)
                        | _ => raise Error (r, "should be '__&array (_, _)'")
                     )
		   else if x = "__&sub" orelse x = "array_get" then
                     (case e2 of
                          S.ETuple ([e1, e2], _) =>
                          ERead (elab e1, elab e2)
                        | _ => raise Error (r, "should be '__&sub (_, _)'")
                     )
		   else if x = "push_back" then
                     (case e2 of
                          S.ETuple ([e1, e2], _) =>
                          EVectorPushBack (elab e1, elab e2)
                        | _ => raise Error (r, "should be 'push_back (_, _)'")
                     )
		   else if x = "__&update" orelse x = "array_set" then
                     (case e2 of
                          S.ETuple ([e1, e2, e3], _) =>
                          EWrite (elab e1, elab e2, elab e3)
                        | _ => raise Error (r, "should be '__&update (_, _, _)'")
                     )
		   else default ()
                 | SOME _ => default ()
              )
	    | _ => default ()
	end
      | S.EBinOp (EBTiML opr, e1, e2, _) => EBinOp (opr, elab e1, elab e2)
      | S.EBinOp (EBStrConcat (), e1, e2, r) =>
        EApp (EVar (QID $ qid_add_r r $ STR_CONCAT_NAMEFUL, (false, false)), EPair (elab e1, elab e2))
      | S.EBinOp (EBSetRef true, e1, e2, r) => EStorageSet (elab e1, elab e2)
      | S.EBinOp (EBSetRef false, e1, e2, r) => EWrite (elab e1, ENat (0, r), elab e2)
      | S.EUnOp (opr, e, r) =>
        (case opr of
             S.EUTiML opr =>
             (case (opr, e) of
                  (S.EUField (name, _), S.EVar ((NONE, ("msg", _)), (false, false))) =>
                  let
                    val name = 
                        case name of
                            "sender" => EnvSender ()
                          | "value" => EnvValue ()
                          | _ => raise Error (r, sprintf "unknown field '$' for msg" [name])
                  in
                    EEnv (name, r)
                  end
                | (S.EUField (name, _), S.EVar ((NONE, ("block", _)), (false, false))) =>
                  let
                    val name = 
                        case name of
                            "number" => EnvBlockNumber ()
                          | _ => raise Error (r, sprintf "unknown field '$' for block" [name])
                  in
                    EEnv (name, r)
                  end
                | _ => EUnOp (opr, elab e, r)
             )
           | S.EUThrow () => EHalt (elab e, TUVar ((), r))
           | S.EUDeref true => EStorageGet (elab e, r)
           | S.EUDeref false => ERead (elab e, ENat (0, r))
           | S.EUAsm _ => raise Error (r, "elaborate/EAsm")
           | S.EUReturn _ => raise Error (r, "elaborate/EReturn")
           | S.EUCall () => elab e
           | S.EUCallValue () => elab e
           | S.EUSend () => ETrue r
           | S.EUFire () => ETT r
           | S.EUAttach () => ETT r
           | S.EUSuicide () => ETT r
           | S.EUSHA3 () => EInt (elab_large_int r "0", r)
           | S.EUSHA256 () => EInt (elab_large_int r "0", r)
           | S.EUECREC () => EInt (elab_large_int r "0", r)
        )
      | S.ETriOp (S.ETIte (), e1, e2, e3, _) =>
        ETriOp (ETIte (), elab e1, elab e2, elab e3)
      (* | S.ETriOp (S.ETIfDec (), e, e1, e2, r) => *)
      (*   ECaseSumbool (elab e, IBind (("__p", r), elab e1), IBind (("__p", r), elab e2), r) *)
      | S.ETriOp (ETIfi (), e, e1, e2, r) =>
        EIfi (elab e, IBind (("__p", r), elab e1), IBind (("__p", r), elab e2), r)
      | S.ENever r => ENever (elab_mt (S.TVar (NONE, ("_", r))), r)
      | S.EGet (x, offsets, r) =>
        EGet (fst x, map (mapPair' elab elab_path) offsets, r)
      | S.ESetModify (is_modify, x, offsets, e, r) =>
        let
          val x = fst x
          val offsets = map (mapPair' elab elab_path) offsets
          val e = elab e
        in
          if is_modify then
            ESet (x, offsets, EApp (e, EGet (x, offsets, r)), r)
          else
            ESet (x, offsets, e, r)
        end
      | S.ENewArrayValues (es, r) => ENewArrayValues (TUVar ((), r), map elab es, r)
      | S.ERecord (fields, r) =>
        ERecord (list2map r $ map (mapSnd elab) fields, r)
      | S.EFor (_, _, _, _, _, _, r) => raise Error (r, "elaborate/EFor")
      | S.EBinOp (EBWhile (), e1, e2, r) => raise Error (r, "elaborate/EWhile")
      | S.ELet2 (_, pn, e, r) => raise Error (r, "let-binding are not allowed here ")
      | S.ESemis (es, r) =>
        let
          val es = rev es
          val (e, es) = case es of
                            [] => raise Impossible "elaborate/ESemis/es=[]"
                          | e :: es => (e, es)
          fun f (e, body) =
            case e of
                S.ELet2 (_, pn, e, r1) =>
                let
                  val e = default (S.EZero r1) e
                in
                  S.ELet (empty_return, [S.DVal ([], pn, e, r1)], body, r)
                end
              | _ => S.ESemiColon (e, body, r)
          val e = foldl f e es
                        (* val () = println "elab/ESemis:" *)
                        (* val () = println $ AstPP.pp_e_to_string e *)
        in
          elab e
        end
      | S.EIfs (ifs, r) =>
        let
          fun check_no_if i =
            case i of
                If (_, _, r) => raise Error (r, "'if' can't appear except for the first branch")
              | _ => ()
          val () = case ifs of
                       If _ :: ifs => app check_no_if ifs
                     | _ => raise Error (r, "first branch must start with 'if'")
          val ifs = rev ifs
          val (e, ifs) = case ifs of
                             Else (e, r) :: ifs => (e, ifs)
                           | _ => (S.ETT r, ifs)
          fun f (i, e2) =
            case i of
                Elseif (e, e1, r) => S.EIte (e, e1, e2, r)
              | If (e, e1, r) => S.EIte (e, e1, e2, r)
              | Else (e, r) => raise Error (r, "'else' can't appear except for the last branch")
          val e = foldl f e ifs
        in
          elab e
        end
      | S.EOffsetProjs (e, projs) =>
        foldl (fn (p, acc) =>
                  case p of
                      inl e => EMapPtr (acc, elab e)
                    | inr (p, r) => EPtrProj (acc, (map_inl_inr (elab_int r) id p, NONE), r)
              ) (elab e) projs
      (* | S.ETruncate (n, e, _) => EIntAnd (elab e, mask n) *)

  and elab_decl decl =
      case decl of
	  S.DVal (tnames, pn, e, r) =>
          let
            val pn = elab_pn pn
          in
            case pn of
                PnVar name =>
                [DVal (name, Outer $ Unbound.Bind (map (fn nm => (Binder $ TName nm, Outer $ IUnderscore2 r)) tnames, elab e), r)]
              | _ =>
                if null tnames then
                  [DValPtrn (pn, Outer $ elab e, r)]
                else
                  raise Error (r, "compound pattern can't be generalized, so can't have explicit type variables")
          end
	| S.DRec (tnames, name, binds, mods, e, r) =>
          let
            val (pre, post, t, d, j, guards) = process_mods mods
            val pre = default empty_state pre
            val post = default pre post
            fun f bind =
              case bind of
		  BindTyping pn => TypingST (elab_pn pn)
		| BindSorting (nm, s, _) => SortingST (Binder $ IName nm, Outer $ elab_s s)
            val binds = map f binds
            (* if the function body is a [case] without annotations, copy the return clause from the function signature to the [case] *)
            (* val e = copy_anno (t, d) e *)
            val t = default (TUVar ((), r)) (Option.map elab_mt t)
            val d = default (IUVar ((), r)) (Option.map elab_i d)
            val j = default (IUVar ((), r)) (Option.map elab_i j)
            val guards = map (fn e => S.EApp (e, S.ETT r, r)) guards
            val e = S.ESemis (guards @ [e], r)
            val e = elab e
          in
	    [DRec (Binder $ EName name, Inner $ Unbound.Bind ((map (fn nm => (Binder $ TName nm, Outer $ IUnderscore2 r)) tnames, Rebind $ Teles binds), ((elab_state r pre, elab_state r post), (t, (d, j)), e)), r)]
          end
        | S.DIdxDef ((name, r), s, i) =>
          let
            val s = default (SUVar ((), r)) $ Option.map elab_s s
          in
            [DIdxDef (Binder $ IName (name, r), Outer $ SOME s, Outer $ elab_i i)]
          end
        | S.DAbsIdx2 ((name, r), s, i) =>
          let
            val s = default (SUVar ((), r)) $ Option.map elab_s s
          in
            [DAbsIdx2 (Binder $ IName (name, r), Outer s, Outer $ elab_i i)]
          end
        | S.DAbsIdx ((name, r1), s, i, decls, r) =>
          let
            val s = default (SUVar ((), r1)) $ Option.map elab_s s
            val i = case i of
                        SOME i => elab_i i
                      | NONE => IUVar ((), r1)
          in
            [DAbsIdx ((Binder $ IName (name, r1), Outer s, Outer i), Rebind $ Teles $ concatMap elab_decl decls, r)]
          end
        | S.DDatatype a =>
          let
            val (dt, r) = elab_datatype a
          in
            [DTypeDef (Binder $ TName $ fst $ unBind dt, Outer $ TDatatype (dt, r))]
          end
        | S.DTypeDef (name, t) => [DTypeDef (Binder $ TName name, Outer $ elab_mt t)]
        | S.DOpen name => [DOpen (Inner name, NONE)]
        | S.DState (name, t, init) =>
          let
            val () = push_ref state_decls_ref (name, t, init)
                              (* val () = Option.app (fn init => push_ref state_inits_ref $ (name, init)) init *)
          in
            []
          end
        | S.DEvent (name, ts) => []

  fun elab_spec spec =
    case spec of
        S.SpecVal (name, tnames, t, r) => SpecVal (name, foldr (fn (tname, t) => PTUni (IUnderscore2 r, Bind (tname, t), combine_region (snd tname) r)) (PTMono $ elab_mt t) tnames)
      | S.SpecIdx (name, sort) => SpecIdx (name, elab_s sort)
      | S.SpecType (tnames, sorts, r) =>
        (case tnames of
             [] => raise Error (r, "Type declaration must have a name")
           | name :: tnames => SpecType (name, (length tnames, map (fst o elab_b) sorts))
        )
      | S.SpecTypeDef (name, ty) => SpecTypeDef (name, elab_mt ty)
      | S.SpecDatatype a =>
        let
          val (dt, r) = elab_datatype a
        in
          SpecTypeDef (fst $ unBind dt, TDatatype (dt, r))
        end
      | S.SpecFun (name, ts, mods) => raise Error (snd name, "elaborate/SpecFun")
      | S.SpecEvent (name, ts) => raise Error (snd name, "elaborate/SpecEvent")

  fun elab_sig sg =
    case sg of
        S.SigComponents (specs, r) => (map elab_spec specs, r)

  fun make_state_init r decls =
    let
      fun f (name, _, init) =
        let
          val x = EShortVar name
        in
          case init of
              NONE => []
            | SOME e =>
              case e of
                  S.ENewArrayValues (es, r) => map (fn e => S.EPushBack (x, e, r)) es
                | _ => [S.ESet (name, [], e, r)]
        end
      val es = concatMap f decls
      val e = case es of [] => S.ETT r | _ => ESemis (es, r)
      (* val e = S.EAbs ([S.BindTyping (S.PnTuple ([], r))], empty_return, e, r) *)
    in
      S.DVal ([], S.PnConstr (((NONE, ("__state_init", r)), false), [], NONE, r), e, r)
    end

  val pervasive = "Pervasive"
                    
  fun elab_mod addPervasive m =
    let
      val elab_mod = elab_mod addPervasive 
    in
      case m of
          S.ModComponents (inherits, comps, r) =>
          let
            val inheritPervasive = if addPervasive andalso (!add_pervasive_flag) then [(pervasive, r)] else []
            val inherits = concatMap elab_decl $ map S.DOpen $ inheritPervasive @ inherits
            val () = state_decls_ref := []
            val decls = concatMap elab_decl comps
            val state_decls = !state_decls_ref
            val state_init = elab_decl $ make_state_init r $ rev state_decls
          in
            (ModComponents (inherits @ state_init @ decls, r), state_decls)
          end
        | S.ModSeal (m, sg) =>
          let
            val (m, state_decls) = elab_mod m
          in
            (ModSeal (m, elab_sig sg), state_decls)
          end
        | S.ModTransparentAsc (m, sg) =>
          let
            val (m, state_decls) = elab_mod m
          in
            (ModTransparentAsc (m, elab_sig sg), state_decls)
          end
    end

  (* fun is_vector t = *)
  (*   case t of *)
  (*       S.TAppT (S.TVar (NONE, (x, _)), t2, _) => *)
  (*       if x = "vector" then SOME $ elab_mt t2 *)
  (*       else NONE *)
  (*     | _ => NONE *)

  (* fun is_map t = *)
  (*   case t of *)
  (*       S.TAppT (S.TAppT (S.TVar (NONE, (x, _)), t1, _), t2, _) => *)
  (*       if x = "map" then *)
  (*         case is_map t2 of *)
  (*             SOME t => SOME $ TCell $ TMap t *)
  (*           | NONE => SOME $ TCell $ elab_mt t2 *)
  (*       else NONE *)
  (*     | _ => NONE *)

  (* fun elab_state_decl (name, t) = *)
  (*     case is_vector t of *)
  (*         SOME t => (name, TBState (false, t)) *)
  (*       | NONE => *)
  (*         case is_map t of *)
  (*             SOME t => (name, TBState (true, t)) *)
  (*           | NONE => raise Error (S.get_region_t t, "wrong state declaration form") *)

  fun elab_top_bind bind =
    case bind of
        S.TBMod (name, m) =>
        let
          val (m, state_decls) = elab_mod (fst name <> pervasive) m
        in
          (map (fn (name, t, _) => (name, TBState $ elab_mt t)) $ rev state_decls) @ [(name, TBMod m)]
        end
      | S.TBFunctor (name, (arg_name, arg), body) =>
        let
          val (body, state_decls) = elab_mod true body
        in
          (map (fn (name, t, _) => (name, TBState $ elab_mt t)) $ rev state_decls) @
          [(name, TBFunctor ((arg_name, elab_sig arg), body))]
        end
      | S.TBFunctorApp (name, f, arg) => [(name, TBFunctorApp (f, arg))]
      | S.TBState (name, t) => [(name, TBState $ elab_mt t)]
      | S.TBPragma (name, version) => [(name, TBPragma version)]
      | S.TBInterface (name, sgn) => []

  fun elab_prog prog = concatMap elab_top_bind prog
                                 
in
val elaborate = elab
fun elaborate_opt e = runError (fn () => elab e) ()
val elaborate_decl = elab_decl
fun elaborate_decl_opt d = runError (fn () => elab_decl d) ()
val elaborate_prog = elab_prog
                       
end

end
