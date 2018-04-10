structure Pervasive = struct

val SOME_NAT_ID = ("Pervasive", 0)
                    
val STR_CONCAT_NAMEFUL = ("String", "concat")

fun qid_add_r r (name, x) = ((name, r), (x, r))
                             
end
