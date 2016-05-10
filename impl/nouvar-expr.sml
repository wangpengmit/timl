structure NoUVar = struct
open Util
         
type 'bsort uvar_bs = empty
type ('bsort, 'idx) uvar_i = empty
type 'sort uvar_s = empty
type 'mtype uvar_mt = empty
fun str_uvar_bs (_ : 'a -> string) (u : 'a uvar_bs) = exfalso u
fun str_uvar_mt (_ : string list * string list -> 'mtype -> string) (_ : string list * string list) (u : 'mtype uvar_mt) = exfalso u
fun str_uvar_i (_ : string list -> 'idx -> string) (_ : string list) (u : ('bsort, 'idx) uvar_i) = exfalso u
fun eq_uvar_i (u : ('bsort, 'idx) uvar_i, u' : ('bsort, 'idx) uvar_i) = exfalso u
end

structure NoUVarExpr = ExprFun (structure Var = IntVar structure UVar = NoUVar)

structure NoUVarSubst = struct
open Util
open NoUVarExpr
infixr 0 $
infixr 1 -->
         
fun on_i_i on_v x n b =
  let
      fun f x n b =
	case b of
	    VarI (y, r) => VarI (on_v x n y, r)
	  | ConstIN n => ConstIN n
	  | ConstIT x => ConstIT x
          | UnOpI (opr, i, r) => UnOpI (opr, f x n i, r)
          | DivI (i1, n2) => DivI (f x n i1, n2)
          | ExpI (i1, n2) => ExpI (f x n i1, n2)
	  | BinOpI (opr, i1, i2) => BinOpI (opr, f x n i1, f x n i2)
	  | TTI r => TTI r
	  | TrueI r => TrueI r
	  | FalseI r => FalseI r
          | TimeAbs (name, i, r) => TimeAbs (name, f (x + 1) n i, r)
          | UVarI (u, _) => exfalso u
  in
      f x n b
  end

fun on_i_p on_i_i x n b =
  let
      fun f x n b =
        case b of
	    True r => True r
	  | False r => False r
          | Not (p, r) => Not (f x n p, r)
	  | BinConn (opr, p1, p2) => BinConn (opr, f x n p1, f x n p2)
	  | BinPred (opr, d1, d2) => BinPred (opr, on_i_i x n d1, on_i_i x n d2)
          | Quan (q, bs, name, p) => Quan (q, bs, name, f (x + 1) n p)
  in
      f x n b
  end

fun shiftx_v x n y = 
    if y >= x then
	y + n
    else
	y

and shiftx_i_i x n b = on_i_i shiftx_v x n b
fun shift_i_i b = shiftx_i_i 0 1 b

fun shiftx_i_p x n b = on_i_p shiftx_i_i x n b
fun shift_i_p b = shiftx_i_p 0 1 b

local
    fun f x v b =
	case b of
	    VarI (y, r) =>
	    if y = x then
		v
	    else if y > x then
		VarI (y - 1, r)
	    else
		VarI (y, r)
	  | ConstIN n => ConstIN n
	  | ConstIT x => ConstIT x
          | UnOpI (opr, i, r) => UnOpI (opr, f x v i, r)
          | DivI (i1, n2) => DivI (f x v i1, n2)
          | ExpI (i1, n2) => ExpI (f x v i1, n2)
	  | BinOpI (opr, d1, d2) => BinOpI (opr, f x v d1, f x v d2)
	  | TrueI r => TrueI r
	  | FalseI r => FalseI r
	  | TTI r => TTI r
          | TimeAbs (name, i, r) => TimeAbs (name, f (x + 1) (shiftx_i_i 0 1 v) i, r)
          | UVarI (u, _) => exfalso u
in
fun substx_i_i x (v : idx) (b : idx) : idx = f x v b
fun subst_i_i v b = substx_i_i 0 v b
end

local
    fun f x v b =
	case b of
	    True r => True r
	  | False r => False r
          | Not (p, r) => Not (f x v p, r)
	  | BinConn (opr,p1, p2) => BinConn (opr, f x v p1, f x v p2)
	  | BinPred (opr, d1, d2) => BinPred (opr, substx_i_i x v d1, substx_i_i x v d2)
          | Quan (q, bs, name, p) => Quan (q, bs, name, f (x + 1) (shiftx_i_i 0 1 v) p)
in
fun substx_i_p x (v : idx) b = f x v b
fun subst_i_p (v : idx) (b : prop) : prop = substx_i_p 0 v b
end

exception ForgetError of var
(* exception Unimpl *)

fun forget_v x n y = 
    if y >= x + n then
	y - n
    else if y < x then
	y
    else
        raise ForgetError y

fun forget_i_i x n b = on_i_i forget_v x n b
fun forget_i_p x n b = on_i_p forget_i_i x n b
                              
fun try_forget f a =
    SOME (f a) handle ForgetError _ => NONE

local
    val changed = ref false
    fun unset () = changed := false
    fun set () = changed := true
    fun mark a = (set (); a)
    fun passi i =
	case i of
            DivI (i1, n2) => DivI (passi i1, n2)
          | ExpI (i1, n2) => ExpI (passi i1, n2)
	  | BinOpI (opr, i1, i2) =>
            (case opr of
	         MaxI =>
	         if eq_i i1 i2 then
		     (set ();
                      i1)
	         else
                   let
                     fun default () = BinOpI (opr, passi i1, passi i2)
                   in
                     case (i1, i2) of
                         (BinOpI (opr, i1, i2), BinOpI (opr', i1', i2')) =>
                         if opr = opr' then
                           if opr = AddI orelse opr = MultI then
                             if eq_i i1 i1' then
                               mark $ BinOpI (opr, i1, BinOpI (MaxI, i2, i2'))
                             else if eq_i i2 i2' then
                               mark $ BinOpI (opr, BinOpI (MaxI, i1, i1'), i2)
                             else default ()
                           else if opr = TimeApp then
                             if eq_i i1 i1' then
                               mark $ BinOpI (opr, i1, BinOpI (MaxI, i2, i2'))
                             else default ()
                           else default ()
                         else default ()
                       | _ => default ()
                   end
	       | MinI =>
	         if eq_i i1 i2 then
		     (set ();
                      i1)
	         else
		     BinOpI (opr, passi i1, passi i2)
	       | AddI => 
	         if eq_i i1 (T0 dummy) orelse eq_i i1 (ConstIN (0, dummy)) then
                     (set ();
                      i2)
	         else if eq_i i2 (T0 dummy) orelse eq_i i2 (ConstIN (0, dummy)) then
                     (set ();
                      i1)
	         else
                     let
                         val i' = combine_AddI $ collect_AddI i
                     in
		         if eq_i i' i then
                             BinOpI (opr, passi i1, passi i2)
                         else
                             (set ();
                              i')
                     end
	       | MultI => 
	         if eq_i i1 (T0 dummy) then
                     (set ();
                      (T0 dummy))
	         else if eq_i i2 (T0 dummy) then
                     (set ();
                      (T0 dummy))
	         else if eq_i i1 (T1 dummy) then
                     (set ();
                      i2)
	         else if eq_i i2 (T1 dummy) then
                     (set ();
                      i1)
	         else
		     BinOpI (opr, passi i1, passi i2)
               | TimeApp =>
                 (case i1 of
                      TimeAbs (_, body, _) =>
                      (set ();
                       subst_i_i (passi i2) body)
		    | _ => BinOpI (opr, passi i1, passi i2)
                 )
            )
          | UnOpI (ToReal, BinOpI (AddI, i1, i2), r) =>
            (set ();
             BinOpI (AddI, UnOpI (ToReal, i1, r), UnOpI (ToReal, i2, r)))
          | UnOpI (ToReal, BinOpI (MultI, i1, i2), r) =>
            (set ();
             BinOpI (MultI, UnOpI (ToReal, i1, r), UnOpI (ToReal, i2, r)))
          | UnOpI (Neg, TrueI _, r) =>
            (set ();
             FalseI r)
          | UnOpI (Neg, FalseI _, r) =>
            (set ();
             TrueI r)
          | UnOpI (B2n, TrueI _, r) =>
            (set ();
             ConstIN (1, r))
          | UnOpI (B2n, FalseI _, r) =>
            (set ();
             ConstIN (0, r))
          | UnOpI (opr, i, r) =>
            UnOpI (opr, passi i, r)
          | TimeAbs ((name, r1), i, r) =>
            TimeAbs ((name, r1), passi i, r)
	  | TrueI _ => i
	  | FalseI _ => i
	  | TTI _ => i
          | ConstIN _ => i
          | ConstIT _ => i
          | VarI _ => i
          | UVarI _ => i

    fun passp p = 
	case p of
	    BinConn (opr, p1, p2) =>
            let
              fun def () = BinConn (opr, passp p1, passp p2)
            in
              case opr of
                  And =>
	          if eq_p p1 (True dummy) then
                    (set ();
                     p2)
	          else if eq_p p2 (True dummy) then
                    (set ();
                     p1)
	          else
	            def ()
                | Or =>
	          if eq_p p1 (False dummy) then
                    (set ();
                     p2)
	          else if eq_p p2 (False dummy) then
                    (set ();
                     p1)
	          else
	            def ()
                | Imply =>
                  if eq_p p2 (True dummy) then
                    (set (); True (get_region_p p))
                  else if eq_p p1 (True dummy) then
                    (set (); p2)
                  else
                    (case p1 of
                         BinConn (And, p1a, p1b) =>
                         mark $ (p1a --> p1b --> p2)
                       | _ =>
                         (* try subst if there is a equality premise *)
                         (* if false then *)
                         (* let *)
                         (*   val (hyps, conclu) = collect_Imply p *)
                         (*   (* test whether [p] is [VarI x = _] or [_ = VarI x] *) *)
                         (*   fun is_x_equals p = *)
                         (*       let *)
                         (*         fun forget x i = *)
                         (*             SOME (x, forget_i_i x 1 i) handle ForgetError _ => NONE *)
                         (*         fun f i1 i2 = *)
                         (*             case (i1, i2) of *)
                         (*                 (VarI (x, _), _) => forget x i2 *)
                         (*               | (_, VarI (x, _)) => forget x i1 *)
                         (*               | _ => NONE *)
                         (*       in *)
                         (*         case p of *)
                         (*             BinPred (EqP, i1, i2) => Option.map (fn a => (a, p)) $ f i1 i2 *)
                         (*           | _ => NONE *)
                         (*       end *)
                         (* in *)
                         (*   case partitionOptionFirst is_x_equals hyps of *)
                         (*       SOME (((x, i), pred), rest) => *)
                         (*       let *)
                         (*         val old = p *)
                         (*         val new = pred --> (shiftx_i_p x 1 $ substx_i_p x i $ combine_Imply rest conclu) *)
                         (*         (* val () = println $ sprintf "Simp: $, $" [str_p [] old, str_p [] new] *) *)
                         (*         val new = if eq_p old new then def () else mark new *)
                         (*       in *)
                         (*         new  *)
                         (*       end *)
                         (*     | NONE => def () *)
                         (* end *)
                         (* else *)
                         let
                           fun forget x i =
                               SOME (x, forget_i_i x 1 i) handle ForgetError _ => NONE
                           fun f i1 i2 =
                               case (i1, i2) of
                                   (VarI (x, _), _) => forget x i2
                                 | (_, VarI (x, _)) => forget x i1
                                 | _ => NONE
                           val s = case p1 of
                                       BinPred (EqP, i1, i2) => f i1 i2
                                     | _ => NONE
                         in

                           case s of
                               SOME (x, i) =>
                               shiftx_i_p x 1 (substx_i_p x i p2)
                               (* ((mark $ shiftx_i_p x 1 (substx_i_p x i p2)) handle _ => def ()) *)
                             | _ => def ()
                         end
                    )
                | _ =>
	          def ()
            end
	  | BinPred (opr, i1, i2) => 
            (case opr of 
                 EqP => if eq_i i1 i2 then (set (); True (get_region_p p))
                        else BinPred (opr, passi i1, passi i2)
               | LeP => if eq_i i1 i2 orelse eq_i i1 (T0 dummy) then (set (); True (get_region_p p))
                        else BinPred (opr, passi i1, passi i2)
               | _ => BinPred (opr, passi i1, passi i2)
            )
          | Not (p, r) => Not (passp p, r)
          | Quan (q, bs, name, p) => 
            (case q of
                 Forall =>
                 (case try_forget (forget_i_p 0 1) p of
                      SOME p => (set (); p)
                    | _ =>
                      (* Quan (q, bs, name, passp p)                       *)
                      (* try subst if there is a equality premise *)
                      let
                        val (hyps, conclu) = collect_Imply p
                        (* test whether [p] is [VarI 0 = _] or [_ = VarI 0] *)
                        fun is_v0_equals p =
                            let
                              fun forget i = try_forget (forget_i_i 0 1) i
                              fun f i1 i2 =
                                  if eq_i i1 (VarI (0, dummy)) then forget i2
                                  else if eq_i i2 (VarI (0, dummy)) then forget i1
                                  else NONE
                            in
                              case p of
                                  BinPred (EqP, i1, i2) => f i1 i2
                                | _ => NONE
                            end
                      in
                        case partitionOptionFirst is_v0_equals hyps of
                            SOME (i, rest) => (set (); subst_i_p i (combine_Imply rest conclu))
                          | NONE => Quan (q, bs, name, passp p)
                      end
                           
                          (*
                      (case p of
                           BinConn (Imply, p1, p2) =>
                           let
                               fun forget i = try_forget (forget_i_i 0 1) i
                               fun f i1 i2 =
                                   if eq_i i1 (VarI (0, dummy)) then forget i2
                                   else if eq_i i2 (VarI (0, dummy)) then forget i1
                                   else NONE
                               val i = case p1 of
                                           BinPred (EqP, i1, i2) => f i1 i2
                                         | _ => NONE
                           in
                               case i of
                                   SOME i => (set (); subst_i_p i p2)
                                 | _ => Quan (q, bs, name, passp p)
                           end
                         | _ =>
                           Quan (q, bs, name, passp p)
                      )
                          *)
                 )
               | Exists ins =>
                 let
                   val p = passp p
                 in
                   case (eq_bs bs (Base Time), try_forget (forget_i_p 0 1) p) of
                       (true, SOME p) =>
                       (set ();
                        (case ins of SOME f => f (T0 dummy) | NONE => ());
                        p)
                      | _ => Quan (q, bs, name, p)
                 end
            )
	  | True _ => p
	  | False _ => p
                           
    fun until_unchanged f a = 
	let fun loop a =
	        let
                    val _ = unset ()
                    val a = f a
                in
		    if !changed then loop a
		    else a
	        end
        in
	    loop a
	end
in
val simp_i = until_unchanged passi
val simp_p = until_unchanged passp
end

end

