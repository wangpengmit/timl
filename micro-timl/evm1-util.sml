structure EVM1Util = struct

open MicroTiMLUtilTiML
open Expr

infix 6 %-
fun a %- b = BinOpI (BoundedMinusI, a, b)
        
val N = INat
val T = ITime
val N32 = INat 32
               
end
