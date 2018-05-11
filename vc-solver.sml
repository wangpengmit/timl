structure VCSolver = struct

open Util
open SMT2Printer
open SMTSolver

infixr 0 $
         
fun print_unsat show_region filename (vc, counter) =
  VC.str_vc show_region filename vc @
  (* [""] @ *)
  (case counter of
       SOME assigns =>
       if length assigns > 0 then
         indent ["Counter-example:"] @
         (self_compose 2 indent) (map (fn (name, value) => sprintf "$ = $" [name, value]) assigns) @
         []        
       else []
     (* | NONE => ["SMT solver reported 'unknown': can't prove and can't find counter example\n"] *)
     | NONE => []
  ) @
  [""]
fun print_unsats show_region filename unsats =
  if length unsats > 0 then
    app println $ concatMap (print_unsat show_region filename) unsats
  else
    println "All conditions proved."
fun bigO_solver vcs =
  if length vcs = 0 then vcs
  else
    let
      val () = println "-------------------------------------------"
      val () = println "Applying BigO solver ..."
      val vcs = BigOSolver.solve_vcs vcs
      val () = println (sprintf "BigO solver generated or left $ proof obligations unproved." [str_int $ length vcs])
      val () = println ""
                       (* val () = print_unsats false filename $ map (fn vc => (vc, SOME [])) vcs *)
    in
      vcs
    end
fun smt_solver filename use_batch vcs =
  if length vcs = 0 then
    (* vcs *)
    map (fn vc => (vc, NONE)) vcs
  else
    let
      val () = println "-------------------------------------------"
      val () = println "Applying SMT solver ..."
      val unsats = map (fn vc => (vc, NONE)) vcs
      val unsats =
          if use_batch then
            List.mapPartial id $ SMTSolver.smt_solver filename true (SOME Z3) $ map fst unsats
          else unsats
      (* re-check individually to get counter-example *)
      (* ToDo: don't need this when SMT batch response parser is made smarter *)
      val unsats = List.mapPartial id $ map (SMTSolver.smt_solver_single filename true (SOME Z3)) $ map fst $ unsats
                                   
      (* val unsats = List.mapPartial id $ SMTSolver.smt_solver filename false (SOME CVC4) vcs *)
      (* re-check individually to get counter-example *)
      (* val unsats = List.mapPartial id $ map (SMTSolver.smt_solver_single filename true (SOME CVC4)) $ map fst $ unsats *)
      (* val unsats = List.mapPartial id $ map (SMTSolver.smt_solver_single filename true (SOME Z3)) $ map fst $ unsats *)
                                   
      val () = println (sprintf "SMT solver generated or left $ proof obligations unproved." [str_int $ length unsats])
      val () = println ""
      (* val () = print_unsats false filename unsats *)
    in
      (* map fst unsats *)
      unsats
    end
fun vc_solver filename vcs =
  let
    val vcs = map Normalize.normalize_vc vcs
    val vcs = concatMap VC.simp_vc_vcs vcs
    val vcs = map fst $ smt_solver filename false(*true*) vcs
    val vcs = bigO_solver vcs
    val vcs = map Normalize.normalize_vc vcs
    val vcs = concatMap VC.simp_vc_vcs vcs
    val vcs = smt_solver filename true vcs
    val vcs = map (mapFst Normalize.normalize_vc) vcs
    val vcs = map (mapFst VC.simp_vc) vcs
                  (* val vcs = BigOSolver.infer_numbers vcs *)
  in
    vcs
  end
    
end
