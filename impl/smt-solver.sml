structure SMTSolver = struct
open Unix

open TextIO
open SMT2Printer
open OS.Process
open SExp

infixr 0 $

fun dowhile cond body st =
    if cond st then
        dowhile cond body (body st)
    else
        st

exception SMTError of string
                          
fun smt_solver filename vcs = 
    let
        val smt2 = to_smt2 vcs
        val smt2_filename = filename ^ ".smt2"
        val resp_filename = filename ^ ".lisp"
        val () = write_file (smt2_filename, smt2)
        val _ = system (sprintf "z3 $ > $" [smt2_filename, resp_filename])
        (* val resp = read_file resp_filename *)
        (* val () = println resp *)
        val resps = SExpParserString.parse_file resp_filename
        (* val () = println $ str_int $ length resps *)
        fun on_resp vc (is_sat, model) =
            case is_sat of
                Atom is_sat =>
                if is_sat = "sat" then
                    (vc, false)
                else
                    (vc, true)
              | _ => raise SMTError "wrong response format"
        fun on_resps vcs resps =
            case (vcs, resps) of
                (vc :: vcs, is_sat :: model :: resps) =>
                on_resp vc (is_sat, model) :: on_resps vcs resps
              | _ => []
        val vcs = on_resps vcs resps
        val vcs = List.filter (fn (_, valid) => not valid) vcs
        val vcs = map fst vcs

                      
        (* val proc = execute ("z3", ["-in"]) *)
        (* val (ins, outs) = (textInstreamOf proc, textOutstreamOf proc) *)
        (* val () = output (outs, smt2) *)
        (* val () = println $ str_bool $ endOfStream ins *)
        (* val s = input ins *)
        (* (* val s = inputN (ins, 30) *) *)
        (* val () = println $ str_int $ size s *)
        (* val () = println s *)
        (* val () = case inputLine ins of SOME str => println str | _ => ()  *)
        (* val resp = rev $ dowhile (fn _ => not (endOfStream ins)) (fn acc => case inputLine ins of SOME line => line :: acc | _ => acc) [] *)
        (* val () = println "hello?" *)
        (* val () = List.app println resp *)
        (* val _ = reap proc *)
    in
        vcs
    end
    (* handle OS.SysErr (msg, _) => *)
    (*        (println ("SysErr: " ^ msg); *)
    (*         vcs) *)
        
end
