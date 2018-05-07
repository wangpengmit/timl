structure EVM1Util = struct

open MicroTiMLUtilTiML
open Expr

infix 6 %-
fun a %- b = BinOpI (BoundedMinusI, a, b)
        
val N = INat
val T = ITime
val N32 = INat 32

fun TProd (a, b) = TMemTuplePtr ([a, b], N 0)

infix  9 @!!
fun m @!! k = StMapU.must_find m k
                               
fun idx_st_must_find i k =
  let
    val (_, _, m) = decompose_state i
  in
    m @!! k
  end
fun idx_st_add i p = IUnion_simp (i, IState (StMapU.single p))
                                 
infix  9 @%!!
fun a @%!! b = idx_st_must_find a b

infix  6 @%+
fun a @%+ b = idx_st_add a b
                                
end
