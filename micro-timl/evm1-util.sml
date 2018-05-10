structure EVM1Util = struct

open MicroTiMLUtilTiML
open Expr

infix 6 %-
fun a %- b = IBinOp (IBBoundedMinus, a, b)
        
fun N a = INat (a, dummy)
fun T a = ITime (a, dummy)
val N32 = N 32

end
