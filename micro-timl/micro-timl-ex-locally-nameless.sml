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
fun Free x = QID (("", dummy), (x, dummy))
fun Bound x = ID (x, dummy)
                 
fun open_var x free var = 
  case var of
      ID (y, _) => 
      if y = x then
        Free free
      else
        var
    | QID _ => var

fun close_var x free var = 
  case var of
      QID (_, (id, _)) => 
      if id = free then
        Bound x
      else
        var
    | ID _ => var

fun open_c_e a = shift_c_e_fn open_var a
fun open_e_e a = shift_e_e_fn open_var a

fun close_c_e a = shift_c_e_fn close_var a
fun close_e_e a = shift_e_e_fn close_var a

fun adapt f x env = f (x + env)

fun adapted_open_var m = adapt $ open_var m
                            
fun open_i_i m x = Subst.IdxShiftVisitor.on_i_i $ adapted_open_var m x
fun open_i_p m x = Subst.IdxShiftVisitor.on_i_p $ adapted_open_var m x
fun open_i_s m x = Subst.IdxShiftVisitor.on_i_s $ adapted_open_var m x

fun open_i_t a = shift_i_t_fn (open_i_i, open_i_s) a
fun open_t_t a = shift_t_t_fn open_var a
                                           
fun open_i_e a = shift_i_e_fn (open_i_i, open_i_s, open_i_t) a
fun open_t_e a = shift_t_e_fn open_t_t a

fun adapted_close_var m = adapt $ close_var m
                            
fun close_i_i m x = Subst.IdxShiftVisitor.on_i_i $ adapted_close_var m x
fun close_i_p m x = Subst.IdxShiftVisitor.on_i_p $ adapted_close_var m x
fun close_i_s m x = Subst.IdxShiftVisitor.on_i_s $ adapted_close_var m x

fun close_i_t a = shift_i_t_fn (close_i_i, close_i_s) a
fun close_t_t a = shift_t_t_fn close_var a
                                           
fun close_i_e a = shift_i_e_fn (close_i_i, close_i_s, close_i_t) a
fun close_t_e a = shift_t_e_fn close_t_t a

fun open0_i_i a = open_i_i 0 a
fun open0_i_p a = open_i_p 0 a
fun open0_i_s a = open_i_s 0 a

fun open0_i_t a = open_i_t 0 a
fun open0_t_t a = open_t_t 0 a
                                           
fun open0_i_e a = open_i_e 0 a
fun open0_t_e a = open_t_e 0 a

fun close0_i_i a = close_i_i 0 a
fun close0_i_p a = close_i_p 0 a
fun close0_i_s a = close_i_s 0 a

fun close0_i_t a = close_i_t 0 a
fun close0_t_t a = close_t_t 0 a
                                           
fun close0_i_e a = close_i_e 0 a
fun close0_t_e a = close_t_e 0 a

fun open0_c_e a = open_c_e 0 a
fun open0_e_e a = open_e_e 0 a
fun close0_c_e a = close_c_e 0 a
fun close0_e_e a = close_e_e 0 a

val ivar_counter = ref 0
val tvar_counter = ref 0
val cvar_counter = ref 0
val evar_counter = ref 0
                       
fun fresh_var counter =
  let
    val v = !counter
    val () = inc counter
  in
    v
  end
    
fun fresh_ivar () = fresh_var ivar_counter 
fun fresh_tvar () = fresh_var tvar_counter 
fun fresh_cvar () = fresh_var cvar_counter 
fun fresh_evar () = fresh_var evar_counter 

end
