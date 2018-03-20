structure BaseTypes = struct
datatype base_type =
         Int
         | String
         | Bool
           
fun eq_base_type (t : base_type, t') = t = t'
        
fun str_bt bt =
  case bt of
      Int => "int"
    | String => "string"
    | Bool => "bool"

end

