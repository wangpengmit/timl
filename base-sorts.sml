structure BaseSorts = struct
open Util
(* basic index sort *)
datatype base_sort =
         Nat
         | Time
	 | BoolSort
	 | UnitSort
         | BSState

fun str_b (s : base_sort) : string = 
  case s of
      Nat => "Nat"
    | Time => "Time"
    | BoolSort => "Bool"
    | UnitSort => "Unit"
    | BSState => "State"
                  
end

