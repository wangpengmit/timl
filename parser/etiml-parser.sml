structure ETiMLLrVals = ETiMLLrValsFun(structure Token = LrParser.Token)

structure ETiMLLex = ETiMLLexFun (structure Tokens = ETiMLLrVals.Tokens)

structure ETiMLParser = JoinWithArg (
    structure ParserData = ETiMLLrVals.ParserData
    structure Lex = ETiMLLex
    structure LrParser = LrParser)

structure ETiMLParser = struct
open Ast
open ParserUtil
	 
val lookahead = 15
		    
type input_stream = int -> string
			       
fun parse (input : input_stream, on_lex_error : reporter, on_parse_error : reporter) =
  let
    val () = println "Using ETiML syntax"
  in
  #1 (ETiMLParser.parse 
	  (lookahead,
	   ETiMLParser.makeLexer input on_lex_error,
	   on_parse_error,
	   on_lex_error))
  handle ETiMLParser.ParseError => raise Error
  end
					
open Util
	 
fun parse_opt (input : input_stream, on_lex_error : reporter, on_parse_error : reporter) =
    OK (parse (input, on_parse_error, on_lex_error)) handle Error => Failed "Parse error"
									    
fun parse_file a = parse_file_gen (parse, ETiMLLex.UserDeclarations.reset_line) a
    
end
