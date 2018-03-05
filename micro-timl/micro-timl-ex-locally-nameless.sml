structure MicroTiMLExLocallyNameless = struct

open MicroTiMLVisitor
open MicroTiMLEx
       
infixr 0 $

(* (* locally nameless variable *) *)
(* datatype ('bound, 'free) lnl_var = *)
(*          Bound of 'bound *)
(*          | Free of 'free *)

(* hijack [long_id] to be used as locally nameless variable *)
open LongId
(* fun Free x = QID (("__Free", dummy), (x, dummy)) *)
fun Free name x = QID ((name, dummy), (x, dummy))
fun Bound x = ID (x, dummy)
                 
fun open_var make_Free x free var = 
  case var of
      ID (y, _) => 
      if y = x then
        make_Free free
      else
        var
    | QID _ => var

fun close_var unFree x free var = 
  case var of
      QID (_, (id, _)) => 
      if id = unFree free then
        Bound x
      else
        var
    | ID _ => var

datatype free_i = Free_i of int
datatype free_t = Free_t of int
datatype free_c = Free_c of int
datatype free_e = Free_e of int
                              
fun make_Free_i (Free_i x) = Free "__Free_i" x
fun make_Free_t (Free_t x) = Free "__Free_t" x
fun make_Free_c (Free_c x) = Free "__Free_c" x
fun make_Free_e (Free_e x) = Free "__Free_e" x
                        
fun unFree_i (Free_i x) = x
fun unFree_t (Free_t x) = x
fun unFree_c (Free_c x) = x
fun unFree_e (Free_e x) = x
                        
fun adapt f x n env = f (x + env) n

fun adapted_open_var make_Free m = adapt (open_var make_Free) m
                            
fun open_i_i x free = Subst.IdxShiftVisitor.on_i_i $ (adapted_open_var make_Free_i) x free
fun open_i_p x free = Subst.IdxShiftVisitor.on_i_p $ (adapted_open_var make_Free_i) x free
fun open_i_s x free = Subst.IdxShiftVisitor.on_i_s $ (adapted_open_var make_Free_i) x free

fun open_i_t a = shift_i_t_fn (open_i_i, open_i_s) a
fun open_t_t a = shift_t_t_fn (open_var make_Free_t) a
                                           
fun open_i_e a = shift_i_e_fn (open_i_i, open_i_s, open_i_t) a
fun open_t_e a = shift_t_e_fn open_t_t a

fun open_c_e a = shift_c_e_fn (open_var make_Free_c) a
fun open_e_e a = shift_e_e_fn (open_var make_Free_e) a

fun open0_i_i a = open_i_i 0 a
fun open0_i_p a = open_i_p 0 a
fun open0_i_s a = open_i_s 0 a

fun open0_i_t a = open_i_t 0 a
fun open0_t_t a = open_t_t 0 a
                                           
fun open0_i_e a = open_i_e 0 a
fun open0_t_e a = open_t_e 0 a

fun open0_c_e a = open_c_e 0 a
fun open0_e_e a = open_e_e 0 a
                           
fun adapted_close_var unFree m = adapt (close_var unFree) m
                            
fun close_i_i x free = Subst.IdxShiftVisitor.on_i_i $ (adapted_close_var unFree_i) x free
fun close_i_p x free = Subst.IdxShiftVisitor.on_i_p $ (adapted_close_var unFree_i) x free
fun close_i_s x free = Subst.IdxShiftVisitor.on_i_s $ (adapted_close_var unFree_i) x free

fun close_i_t a = shift_i_t_fn (close_i_i, close_i_s) a
fun close_t_t a = shift_t_t_fn (close_var unFree_t) a
                                           
fun close_i_e a = shift_i_e_fn (close_i_i, close_i_s, close_i_t) a
fun close_t_e a = shift_t_e_fn close_t_t a

fun close_c_e a = shift_c_e_fn (close_var unFree_c) a
fun close_e_e a = shift_e_e_fn (close_var unFree_e) a

fun close0_i_i a = close_i_i 0 a
fun close0_i_p a = close_i_p 0 a
fun close0_i_s a = close_i_s 0 a

fun close0_i_t a = close_i_t 0 a
fun close0_t_t a = close_t_t 0 a
                                           
fun close0_i_e a = close_i_e 0 a
fun close0_t_e a = close_t_e 0 a

fun close0_c_e a = close_c_e 0 a
fun close0_e_e a = close_e_e 0 a

val ivar_counter = ref $ Free_i 0
val tvar_counter = ref $ Free_t 0
val cvar_counter = ref $ Free_c 0
val evar_counter = ref $ Free_e 0

fun map_ivar f (Free_i x) = Free_i $ f x
fun map_tvar f (Free_t x) = Free_t $ f x
fun map_cvar f (Free_c x) = Free_c $ f x
fun map_evar f (Free_e x) = Free_e $ f x
                       
fun fresh_var map counter =
  let
    val v = !counter
    val () = unop_ref (map (curry op+ 1)) counter
  in
    v
  end
    
fun fresh_ivar () = fresh_var map_ivar ivar_counter 
fun fresh_tvar () = fresh_var map_tvar tvar_counter 
fun fresh_cvar () = fresh_var map_cvar cvar_counter 
fun fresh_evar () = fresh_var map_evar evar_counter 

structure UnitTest = struct

structure ExportPP = struct

open LongId
open Util
open MicroTiML
open MicroTiMLVisitor
open MicroTiMLExLongId
open MicroTiMLEx
       
infixr 0 $
infixr 0 !!
         
fun short_to_long_id x = ID (x, dummy)
fun export_var sel ctx id =
  let
    fun unbound s = "__unbound_" ^ s
    (* fun unbound s = raise Impossible $ "Unbound identifier: " ^ s *)
  in
    case id of
        ID (x, _) =>
        short_to_long_id $ nth_error (sel ctx) x !! (fn () => unbound $ str_int x)
      | QID _ => short_to_long_id $ unbound $ CanToString.str_raw_var id
  end
(* val export_i = return2 *)
fun export_i a = ToString.export_i Gctx.empty a
fun export_s a = ToString.export_s Gctx.empty a
fun export_t a = export_t_fn (export_var snd, export_i, export_s) a
fun export a = export_e_fn (export_var #4, export_var #3, export_i, export_s, export_t) a
val str = PP.string
fun str_var x = LongId.str_raw_long_id id(*str_int*) x
fun str_i a =
  (* ToStringRaw.str_raw_i a *)
  ToString.SN.strn_i a
(* const_fun "<idx>" a *)
fun str_bs a =
  ToStringRaw.str_raw_bs a
fun str_s a =
  (* ToStringRaw.str_raw_s a *)
  ToString.SN.strn_s a
  (* const_fun "<sort>" a *)
fun pp_t_to s b =
  MicroTiMLPP.pp_t_to_fn (str_var, str_bs, str_i, str_s, const_fun "<kind>") s b
  (* str s "<ty>" *)
fun pp_t b = MicroTiMLPP.pp_t_fn (str_var, str_bs, str_i, str_s, const_fun "<kind>") b
fun pp_t_to_string b = MicroTiMLPP.pp_t_to_string_fn (str_var, str_bs, str_i, str_s, const_fun "<kind>") b
fun pp_e_to_string a = MicroTiMLExPP.pp_e_to_string_fn (
    str_var,
    str_i,
    str_s,
    const_fun "<kind>",
    pp_t_to
  ) a

end

infix 4 %=
        
fun test1 dirname =
    let
      open Expr
      open MicroTiMLExUtil
      val t = TNat $ VarI (ID (1, dummy), [])
      val s = Subset ((Base Nat, dummy), Bind.Bind (("_VC", dummy), ConstIN (0, dummy) %= VarI (ID (1, dummy), [])), dummy)
      val t = MakeTForallI (s, ("_VC", dummy), t)
      val t = MakeTForallI (SNat, ("_i0", dummy), t)
      (* val t0 = t *)
      val s_expected = s
      (* val () = println $ "before open_i_s(): " ^ (ExportPP.str_s $ ExportPP.export_s [] s) *)
      val s = open_i_s 1 (Free_i 999) s
      (* val () = println $ "after open_i_s(): " ^ (ExportPP.str_s $ ExportPP.export_s [] s) *)
      val () = assert_b "" $ Equal.eq_s s s_expected
                        
      val t_expected = t
      (* val () = println $ "before open0_i_t(): " ^ (ExportPP.pp_t_to_string $ ExportPP.export_t ([], []) t) *)
      val t = open0_i_t (Free_i 999) t
      (* val () = println $ "after open0_i_t(): " ^ (ExportPP.pp_t_to_string $ ExportPP.export_t ([], []) t) *)
      val () = assert_b "" $ eq_t t t_expected
                        
      (* val t = t0 *)
      (* val t = MicroTiMLExLongId.shift_i_t 0 999 t *)
      (* val () = println $ "after shift0_i_t(): " ^ (ExportPP.pp_t_to_string $ ExportPP.export_t ([], []) t) *)
    in
      ()
    end

val test_suites = [
      test1
]

end
                       
end
