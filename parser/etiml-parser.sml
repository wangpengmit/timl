structure ETiMLLrVals = ETiMLLrValsFun(structure Token = LrParser.Token)

structure ETiMLLex = ETiMLLexFun (structure Tokens = ETiMLLrVals.Tokens)

structure ETiMLParser = JoinWithArg (
    structure ParserData = ETiMLLrVals.ParserData
    structure Lex = ETiMLLex
    structure LrParser = LrParser)

structure ETiMLParser = struct
open Ast
	 
val lookahead = 15
		    
type input_stream = int -> string
			       
exception Error
	      
fun parse (input : input_stream, on_lex_error : reporter, on_parse_error : reporter) =
  #1 (ETiMLParser.parse 
	  (lookahead,
	   ETiMLParser.makeLexer input on_lex_error,
	   on_parse_error,
	   on_lex_error))
  handle ETiMLParser.ParseError => raise Error
					
open Util
	 
fun parse_opt (input : input_stream, on_lex_error : reporter, on_parse_error : reporter) =
    OK (parse (input, on_parse_error, on_lex_error)) handle Error => Failed "Parse error"
									    
open Region

fun parse_file filename =
  let
      val inStream =  TextIO.openIn filename
      fun input n =
	if TextIO.endOfStream inStream
	then ""
	else TextIO.inputN (inStream,n);

      fun on_error (msg, left, right) = print (str_error "Error" filename (left, right) [msg])
      val () = ETiMLLex.UserDeclarations.reset_line ()
      val s = parse (input, on_error, on_error)
      val _ = TextIO.closeIn inStream
  in
      s
  end

end
