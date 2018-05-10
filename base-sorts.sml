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
      Nat => "Nat"
    | Time => "Time"
    | BoolSort => "Bool"
    | UnitSort => "Unit"
    | BSSState => "State"
                  
end

