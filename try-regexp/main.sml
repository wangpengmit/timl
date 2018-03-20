structure Main =
struct
(**
 * RE is a module created by calling the module-level function (functor)
 * RegExpFn (Fn comes from functor), with two module arguments.
 *
 * The first argument, called P, is the syntax used to write regular
 * expressions in. In this particular case, it's the Awk syntax, which
 * is the only syntax provided by SML/NJ right now.
 *
 * The second argument, called E, is the RegExp engine used behind the
 * scenes to compile and execute the syntax. In this particular case
 * I've opted from ThompsonEngine, which implements Ken Thompson's
 * matching algorithm. Other options are BackTrackEngine and DfaEngine.
 *)
structure RE = RegExpFn(
  structure P = AwkSyntax
  structure E = ThompsonEngine
(* structure E = BackTrackEngine *)
(* structure E = DfaEngine *)
)

fun main () =
  let
    (**
     * A list of (regexp, match function) pairs. The function called by
     * RE.match is the one associated with the regexp that matched.
     *
     * The match parameter is described here:
     *   http://www.smlnj.org/doc/smlnj-lib/Manual/match-tree.html
     *)
    val regexes = [
      ("[a-zA-Z]*",   fn match => ("1st", match)),
      ("[0-9]*",      fn match => ("2nd", match)),
      ("1tom|2jerry", fn match => ("3rd", match))
    ]
    val input = "7569ab1tom"
    (**
     * StringCvt.scanString will traverse the `input` string and apply
     * the result of `RE.match regexes` to each character in the string.
     *
     * It's sort of a streaming matching process. The end result, however,
     * depends on your implementation above, in the match functions.
     *)
    val () =
        case StringCvt.scanString (RE.match regexes) input of
            SOME (s, _) => print s
          | NONE => print "NONE"
  in
    ()
  end
end
