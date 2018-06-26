structure ParserFactory = struct

open ParserUtil

val r = ref Parser.parse_file

fun set v = r := v
                     
fun parse_file a = (!r) a

end
