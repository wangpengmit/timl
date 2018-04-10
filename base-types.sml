structure BaseTypes = struct
datatype base_type =
         Int
         | Bool
         | Byte
         (* | String *)
           
fun eq_base_type (t : base_type, t') = t = t'
        
fun str_bt bt =
  case bt of
      Int => "int"
    | Bool => "bool"
    | Byte => "byte"
    (* | String => "string" *)

end

