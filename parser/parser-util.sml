structure ParserUtil = struct

exception Error
	      
open Region

fun parse_file_gen (parse, reset_line) filename =
  let
      val inStream = TextIO.openIn filename
      fun input n =
	if TextIO.endOfStream inStream
	then ""
	else TextIO.inputN (inStream,n);

      fun on_error (msg, left, right) = print (str_error "Error" filename (left, right) [msg])
      val () = reset_line ()
      val s = parse (input, on_error, on_error)
      val _ = TextIO.closeIn inStream
  in
      s
  end

end
