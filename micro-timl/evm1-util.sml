structure EVM1Util = struct

open Expr

infix 6 %-
fun a %- b = BinOpI (BoundedMinusI, a, b)
        
fun INat c = ConstIN (c, dummy)
fun ITime c = ConstIT (c, dummy)
val N = INat
val T = ITime
val N32 = INat 32
               
end
