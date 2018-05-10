structure BaseSorts = struct
open Util
(* basic index sort *)
datatype base_sort =
         BSSNat
         | BSSTime
	 | BSSBool
	 | BSSUnit
         | BSSState

fun str_b (s : base_sort) : string = 
  case s of
      BSSNat => "Nat"
    | BSSTime => "Time"
    | BSSBool => "Bool"
    | BSSUnit => "Unit"
    | BSSState => "State"
                  
end

