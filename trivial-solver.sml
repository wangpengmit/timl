structure TrivialSolver = struct
open Equal
open UVar
open Expr
open VC
open Normalize
         
fun solve (hyps, p) =
  List.exists (fn h => case h of PropH p' => eq_p p p' | _ => false) hyps orelse
  case p of
      PBinConn (BCImply (), p1, p2) => solve (PropH p1 :: hyps, p2)
    | PBinConn (BCIff (), p1, p2) => solve (hyps, PBinConn (BCImply (), p1, p2)) andalso solve (hyps, PBinConn (BCImply (), p2, p1))
    | PBinConn (BCAnd (), p1, p2) => solve (hyps, p1) andalso solve (hyps, p1)
    | PBinConn (BCOr (), p1, p2) => solve (hyps, p1) orelse solve (hyps, p1)
    | PTrueFalse (true, _) => true
    | PBinPred (BPEq (), i1, i2) => eq_i i1 i2
    | PBinPred (BPLe (), i1, i2) => eq_i i1 i2
    | _ => false

fun filter_solve vcs = List.filter (fn vc => solve vc = false) vcs

fun simp_and_solve_vcs (vcs : vc list) : vc list =
    let 
	(* val () = print "Simplifying and applying trivial solver ...\n" *)
	val vcs = filter_solve vcs
	val vcs = map normalize_vc vcs
	val vcs = map simp_vc vcs
	val vcs = filter_solve vcs
    in
        vcs
    end

end
