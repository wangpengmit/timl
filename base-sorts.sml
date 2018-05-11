structure BaseSorts = struct
open Util
       
(* basic index sort *)
(* a uesless payload to prevent the constructor name being used as wildcard in patterns  *)       
datatype base_sort =
         BSSNat of unit
         | BSSTime of unit
	 | BSSBool of unit
	 | BSSUnit of unit
         | BSSState of unit

fun str_b (s : base_sort) : string = 
  case s of
      BSSNat () => "Nat"
    | BSSTime () => "Time"
    | BSSBool () => "Bool"
    | BSSUnit () => "Unit"
    | BSSState () => "State"
                  
end

