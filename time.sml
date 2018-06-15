structure TimeType = struct

(* type time = string *)
(* val zero = "0.0" *)
(* val one = "1.0" *)
       
open Real
       
type time = real
val zero = fromInt 0
val one = fromInt 1

fun str_time x =
  let
    val s = toString x
  in
    if String.isSubstring "E" s then
      fmt (StringCvt.FIX NONE) x
    else
      s
  end
                   
val toString = str_time
                 
val time_eq = op==
val add = op+
val minus = op-
val mult = op*

end
