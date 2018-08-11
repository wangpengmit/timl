structure TiML = struct
structure E = NamefulExpr
open Expr
open Util
open Elaborate
structure NR = NameResolve
open NR
structure TC = TypeCheck
open TC
structure SU = SetUtilFn (StringBinarySet)
structure MU = MapUtilFn (Gctx.Map)
open VCSolver

infixr 0 $
infix 0 !!

exception Error of string
                     
structure UnderscoredCollectMod = CollectModFn (structure Expr = UnderscoredExpr
                                     val on_var = collect_mod_long_id
                                     val on_mod_id = collect_mod_mod_id
                                    )
                                    
fun process_prog show_result filename gctx prog =
    let
      fun print_result show_region filename old_gctxn gctx =
          let 
            val header =
                (* sprintf "Typechecked $" [filename] :: *)
                sprintf "Typechecking results (as module signatures) for $:" [filename] ::
                [""]
            val typing_lines = str_gctx old_gctxn gctx
            val lines = 
                header @
                (* ["Types: ", ""] @ *)
                typing_lines @
                [""]
          in
            lines
          end
      (* typechecking context to name-resolving context *)      
      fun TCctx2NRctx (ctx : TC.context) : NR.context =
          let
            val (sctx, kctx, cctx, tctx) = ctx
            fun on_constr (name, (_, tbinds)) =
              let
                val (_, core) = unfold_binds tbinds
              in
                (name, TC.get_constr_inames core)
              end
            val cctx = map on_constr cctx
          in
            (sctx_names sctx, names kctx, cctx, names tctx)
          end
      (* typechecking signature to name-resolving signature *)      
      fun TCsgntr2NRsgntr (sg : TC.sgntr) : NR.sgntr =
          case sg of
              Sig ctx => NR.Sig $ TCctx2NRctx ctx
            | FunctorBind ((name, arg), body) => NR.FunctorBind ((name, TCctx2NRctx arg), TCctx2NRctx body)
      (* typechecking global context to name-resolving global context *)      
      fun TCgctx2NRgctx gctx = Gctx.map TCsgntr2NRsgntr gctx
      (* trim [gctx] to retain only those that are relevant in typechecking [prog] *)
      fun trim_gctx prog gctx =
        let
          open SU.Set
          open SU
          open List
          fun trans_closure graph nodes =
            let
              fun loop (working, done) =
                case pop working of
                    NONE => done
                  | SOME (node, working) =>
                    if member node done then
                      loop (working, done)
                    else
                      let
                        val outs = default empty $ Gctx.find (graph, node)
                        val working = union (working, outs)
                        val done = SU.Set.add (done, node)
                      in
                        loop (working, done)
                      end
              val nodes = loop (nodes, empty)
            in
              nodes
            end
              
          val ms = dedup $ UnderscoredCollectMod.collect_mod_prog prog
          val ms = to_list $ trans_closure (get_dependency_graph gctx) $ to_set ms
          val gctx = MU.restrict ms gctx
        in
          gctx
        end
      val old_gctx = gctx
      (* val prog = [bind] *)
      val (prog, _, _) = resolve_prog (TCgctx2NRgctx gctx) prog
      val result as ((_, gctxd, (* gctx *)_), (vcs, admits)) = typecheck_prog (trim_gctx prog gctx) prog
      (* val () = write_file (filename ^ ".smt2", to_smt2 vcs) *)
      (* val () = app println $ print_result false filename (gctx_names old_gctx) gctxd *)
      val () = println $ sprintf "Typechecker generated $ proof obligations." [str_int $ length vcs]
      (* val () = app println $ concatMap (fn vc => VC.str_vc false filename vc @ [""]) vcs *)
      val vcs = vc_solver filename vcs
      val () = if null vcs then
                 if show_result then println $ sprintf "Typechecking $ succeeded.\n" [filename] else ()
               else
                 raise Error $ (* str_error "Error" filename dummy *) join_lines $ [sprintf "Typecheck Error: $ Unproved obligations:" [str_int $ length vcs], ""] @ (
                 (* concatMap (fn vc => str_vc true filename vc @ [""]) $ map fst vcs *)
                 concatMap (print_unsat true filename) vcs
               )
      val gctxd = normalize_sgntr_list true old_gctx gctxd
      val gctxd = update_sgntr_list gctxd
      (* val gctxd = SimpCtx.simp_sgntr_list gctxd *)
      val () = if show_result then
                 app println $ print_result false filename (gctx_names old_gctx) gctxd
               else ()
      val admits = map (attach_fst filename) admits
                              (* val gctx = gctxd @ old_gctx *)
    in
      (prog, gctxd, (* gctx,  *)admits)
    end

fun do_process_file is_library gctx (pos_or_neg, filename) =
  let
    val show_result = not is_library
    val () = if show_result then println $ sprintf "Typechecking file $ ..." [filename] else ()
    val () = if is_library then
               TypeCheck.turn_on_builtin ()
             else ()
    val (succeeded, prog, gctx, admits) =
        let
          val prog = ParserFactory.parse_file filename
          val () = curry write_file (filename ^ ".parsed.tmp") $ AstPP.pp_prog_to_string prog
          val () = TypeCheck.debug_dir_name := (SOME $ fst $ split_dir_file filename)
          val prog = elaborate_prog prog
          val () = curry write_file (filename ^ ".elabed.tmp") $ NamefulPrettyPrint.pp_prog_to_string prog
          (* val () = (app println o map (suffix "\n") o fst o E.str_decls ctxn) decls *)
          (* val () = (app println o map (suffix "\n") o fst o UnderscoredExpr.str_decls ctxn) decls *)
          (* apply solvers after each top bind *)
          (* fun iter (bind, (prog, gctx, admits_acc)) = *)
          (*     let *)
          (*       (* val mod_names = mod_names_top_bind bind *) *)
          (*       (* val (gctx', mapping) = select_modules gctx mod_names *) *)
          (*       val gctx' = gctx *)
          (*       val (progd, gctxd, admits) = process_prog show_result filename gctx' [bind] *)
          (*       (* val gctxd = remap_modules gctxd mapping *) *)
          (*       val gctx = addList (gctx, gctxd) *)
          (*     in *)
          (*       (progd @ prog, gctx, admits_acc @ admits) *)
          (*     end *)
          (* val (prog, gctx, admits) = foldl iter ([], gctx, []) prog *)
          val (prog, gctxd, admits) = process_prog show_result filename gctx prog
        in
          (true, prog, addList (gctx, gctxd), admits)
        end
        handle e =>
               if pos_or_neg then raise e
               else
                 (println $ sprintf "Negative example $ properly triggered an error." [filename];
                  (false, [], gctx, []))
    val () = if succeeded andalso not pos_or_neg then
               raise Error $ "Error: This is a negative example but the typechecking succeeded: " ^ filename
             else ()
    val () = TypeCheck.turn_off_builtin ()
  in
    (prog, gctx, admits)
  end
  handle
  Elaborate.Error (r, msg) => raise Error $ str_error "Error" filename r ["Elaborate error: " ^ msg]
  | NameResolve.Error (r, msg) => raise Error $ str_error "Error" filename r ["Resolve error: " ^ msg]
  | TypeCheck.Error (r, msg) => raise Error $ str_error "Error" filename r ((* "Type error: " :: *) msg)
  | BigOSolver.MasterTheoremCheckFail (r, msg) => raise Error $ str_error "Error" filename r ((* "Type error: " :: *) msg)
  | ParserFactory.Error => raise Error "Unknown parse error"
  | SMTError msg => raise Error $ "SMT error: " ^ msg
  | IO.Io e => raise Error $ sprintf "IO error in function $ on file $" [#function e, #name e]
  | OS.SysErr (msg, err) => raise Error $ sprintf "System error$: $" [(default "" o Option.map (prefix " " o OS.errorName)) err, msg]
  | Gctx.KeyAlreadyExists (name, gctx) => raise Error $ sprintf "module name '$' already exists in module context $" [name, str_ls id gctx]

(* fun process_file is_library filename gctx = *)
(*     let *)
(*       val (dir, base, ext) = split_dir_file_ext filename *)
(*       val gctx = *)
(*           if ext = SOME "pkg" then *)
(*             let *)
(*               (* val split_lines = String.tokens (fn c => c = #"\n") *) *)
(*               (* val read_lines = split_lines o read_file *) *)
(*               val filenames = read_lines filename *)
(*               val filenames = map trim filenames *)
(*               (* val () = app println filenames *) *)
(*               val filenames = List.filter (fn s => not (String.isPrefix "(*" s andalso String.isSuffix "*)" s)) filenames *)
(*               (* val () = app println filenames *) *)
(*               val filenames = List.filter (fn s => s <> "") filenames *)
(*               val filenames = map (curry join_dir_file dir) filenames *)
(*               val gctx = process_files is_library gctx filenames *)
(*             in *)
(*               gctx *)
(*             end *)
(*           else if ext = SOME "timl" then *)
(*             do_process_file is_library gctx filename *)
(*           else raise Error $ sprintf "Unknown filename extension $ of $" [default "<EMPTY>" ext, filename] *)
(*     in *)
(*       gctx *)
(*     end *)
      
(* and process_files is_library gctx filenames = *)
(*     let *)
(*       fun iter (filename, (prog, gctx, acc)) = *)
(*           let *)
(*             val (progd, gctx, admits) = process_file is_library filename gctx *)
(*           in *)
(*             (progd @ prog, gctx, acc @ admits) *)
(*           end *)
(*     in *)
(*       foldl iter ([], gctx, []) filenames *)
(*     end *)

fun process_file_and_accumulate is_library r filename =
  let
    val (prog, gctx, acc) = !r
    val (progd, gctx, admits) = do_process_file is_library gctx filename
  in
    r := (progd @ prog, gctx, acc @ admits)                                            
  end
                                                
fun process_files_and_accumulate is_library gctx filenames =
  let
    val r = ref ([], gctx, [])
    val () = ParseFilename.parse_filenames (process_file_and_accumulate is_library r, fn msg => raise Error msg) filenames
  in
    !r
  end
    
fun main libraries filenames =
    let
      (* val () = app println $ ["Input file(s):"] @ indent filenames *)
      val (_, gctx, _) = process_files_and_accumulate true empty libraries
      val (prog, gctx, admits) = process_files_and_accumulate false gctx filenames
      fun str_admit show_region (filename, p) =
          let
            open Expr
            fun prop2vc p =
              let
              in
                case p of
                    PQuan (Forall (), bs, Bind ((name, r), p), r_all) =>
                    let
                      val vc = prop2vc p
                      val vc = add_hyp_vc (VarH (name, (bs, r_all))) vc
                    in
                      vc
                    end
                  | PBinConn (Imply, p1, p) =>
                    let
                      val vc = prop2vc p
                      val vc = add_hyp_vc (PropH p1) vc
                    in
                      vc
                    end
                  | _ => ([], p)
              end
            val vc = prop2vc p
            (* val r = get_region_p p *)
            val r = get_region_p $ snd vc
            val region_lines = if show_region then
                                 [str_region "" filename r]
                               else []
          in
            region_lines @ 
            [str_p empty [] p] @ [""]
          end
      val () =
          if null admits then
            ()
          else
            (* app println $ "Admitted axioms: \n" :: concatMap (str_admit true) admits *)
            app println $ "Admitted axioms: \n" :: (concatMap (str_admit false) $ dedup (fn ((_, p), (_, p')) => Equal.eq_p p p') admits)
    in
      (prog, gctx, admits)
    end
      
end

structure Main = struct
open Util
open OS.Process
open List

infixr 0 $
infix 0 !!
        
exception ParseArgsError of string
            
fun usage () =
    let
      val () = println "Usage: THIS [--help] [-l <library1:library2:...>] [--annoless] <file-name1> <file-name2> ..."
      val () = println "  --help: print this message"
      val () = println "  -l <library1:library2:...>: paths to libraries, separated by ':'"
      val () = println "  --annoless: less annotations on case-of"
      val () = println "  --repeat n: repeat the whole thing for [n] times (for profiling purpose)"
      val () = println "  --unit-test <dir-name>: do unit test under directory dir-name"
      val () = println "  -n <file-name>: typecheck a negative file (succeeds only when there are errors)"
      val () = println "  --etiml: use ETiML syntax"
      val () = println "  --pervasive: add 'open Pervasive' to each module"
      val () = println "  --debug-cost: generate useless instructions to help debug costs"
      val () = println "  --prelude: generate a prelude to dispatch based on EVM input"
      val () = println "  --vc-check-off: turn off VC checking in --unit-test mode"
      val () = println "  --debug-log: turn on the 'log' command for debugging"
    in
      ()
    end

type options =
     {
       AnnoLess : bool ref,
       Repeat : int ref,
       Libraries : (bool * string) list ref,
       UnitTest : string option ref
     }

fun create_default_options () : options =
  {
    AnnoLess = ref false,
    Repeat = ref 1,
    Libraries = ref [],
    UnitTest = ref NONE
  }
    
fun parse_arguments (opts : options, args) =
    let
      val positionals = ref []
      fun parse_libraries arg =
        String.tokens (curry op= #":") arg
      (* fun do_A arg = print ("Argument of -A is " ^ arg ^ "\n") *)
      (* fun do_B ()  = if !switch then print "switch is on\n" else print "switch is off\n" *)
      fun parse_repeat s =
        let
          val n = Int.fromString s !! (fn () => raise ParseArgsError $ sprintf "$ is not a number" [s])
          val () = if n < 0 then raise ParseArgsError $ sprintf "$ is negative" [str_int n]
                   else ()
        in
          n
        end
      fun parseArgs args =
          case args of
              [] => ()
	    | "--help" :: ts => (usage (); parseArgs ts)
	    | "--annoless" :: ts => (#AnnoLess opts := true; parseArgs ts)
	    | "--repeat" :: arg :: ts => (#Repeat opts := parse_repeat arg; parseArgs ts)
	    | "-l" :: arg :: ts => (app (push_ref (#Libraries opts) o attach_fst true) $ parse_libraries arg; parseArgs ts)
	    | "--unit-test" :: arg :: ts => (#UnitTest opts := SOME arg; parseArgs ts)
	    (* | parseArgs ("-A" :: arg :: ts) = (do_A arg;       parseArgs ts) *)
	    (* | parseArgs ("-B"        :: ts) = (do_B();         parseArgs ts) *)
	    | "-n" :: arg :: ts => (push_ref positionals (false, arg); parseArgs ts)
	    | "--etiml" :: ts => (ParserFactory.set ETiMLParser.parse_file; parseArgs ts)
	    | "--pervasive" :: ts => (Elaborate.add_pervasive_flag := true; parseArgs ts)
	    | "--debug-cost" :: ts => (CostDebug.debug_cost_flag := true; parseArgs ts)
	    | "--prelude" :: ts => (EVMPrelude.add_prelude_flag := true; parseArgs ts)
	    | "--vc-check-off" :: ts => (ToEVM1.UnitTest.vc_check_off_flag := true; parseArgs ts)
	    (* | "--debug-log" :: ts => (EVMDebugLog.add_debug_log_flag := true; parseArgs ts) *)
	    | "--debug-log" :: ts => (TypeCheck.debug_log_flag := true; parseArgs ts)
	    | arg :: ts =>
              if String.isPrefix "-" arg then
	        raise ParseArgsError ("Unrecognized option: " ^ arg)
              else
                (push_ref positionals (true, arg); parseArgs ts)
      val () = parseArgs args
    in
      (!positionals)
    end

val success = OS.Process.success
val failure = OS.Process.failure

fun usage_and_fail () = (usage (); exit failure)
                          
fun main (prog_name, args : string list) = 
  let
    val () = println "TiML 0.1.0"
    val opts = create_default_options ()
    val filenames = rev $ parse_arguments (opts, args)
    val () = case !(#UnitTest opts) of
                 NONE => ()
               | SOME dirname => (app (fn f => ignore $ f dirname) UnitTest.test_suites; exit success)
    val libraries = rev $ !(#Libraries opts)
    (* val () = if null filenames then *)
    (*            usage_and_fail () *)
    (*          else () *)
    val () = TypeCheck.anno_less := !(#AnnoLess opts)
    val _ = repeat_app (fn () => TiML.main libraries filenames) (!(#Repeat opts))
  in	
    success
  end
  handle
  TiML.Error msg => (println $ (* "Error: " ^  *)msg; failure)
  | IO.Io e => (println (sprintf "IO Error doing $ on $" [#function e, #name e]); failure)
  | Impossible msg => (println ("Impossible: " ^ msg); failure)
  | Unimpl msg => (println ("Unimpl: " ^ msg); failure)
  | ParseArgsError msg => (println msg; usage_and_fail ())
                            (* | _ => (println ("Internal error"); failure) *)

end
