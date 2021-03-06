structure SMT2Printer = struct
open Util
open Expr
open UVar
open Normalize
open VC

infixr 0 $

infixr 1 -->

exception SMTError of string

fun escape s = if s = "_" then "__!escaped_from_underscore_for_smt" else String.map (fn c => if c = #"'" then #"!" else c) s
fun evar_name n = "!!" ^ str_int n

fun print_idx_bin_op opr =
    let
      fun err () = raise Impossible $ "print_idx_bin_op () on " ^ str_idx_bin_op opr
    in
    case opr of
        IBAdd () => "+"
      | IBMinus () => "-"
      | IBMult () => "*"
      | IBMod () => "mod"
      | IBEq () => "="
      | IBAnd () => "and"
      | IBOr () => "or"
      | IBXor () => "xor"
      | IBExpN () => "exp_i_i"
      (* | ExpNI () => "^" *)
      | IBLt () => "<"
      | IBGt () => ">"
      | IBLe () => "<="
      | IBGe () => ">="
      | IBBoundedMinus () => err ()
      | IBMax () => err ()
      | IBMin () => err ()
      | IBApp () => err ()
      | IBUnion () => err ()
    end
        
fun print_i ctx i =
  case i of
      IVar (id, _) =>
      (case id of
           ID (n, _) =>
           (List.nth (ctx, n) handle Subscript => raise SMTError $ "Unbound variable: " ^ str_int n)
         | QID _ =>
           raise SMTError $ "Unbound variable: " ^ LongId.str_raw_long_id str_int id
      )
    | IConst (c, _) =>
      (case c of
           ICNat n => str_int n
         | ICTime x => TimeType.toString x
         | ICBool b => str_bool b
         | ICTT () => "TT"
         | ICAdmit () => "TT"
      )
    | IUnOp (opr, i, _) => 
      (case opr of
           IUToReal () => sprintf "(to_real $)" [print_i ctx i]
         | IULog base =>
           sprintf "(log $ $)" [base, print_i ctx i]
           (* raise SMTError "can't handle log2" *)
         | IUCeil () => sprintf "(ceil $)" [print_i ctx i]
         | IUFloor () => sprintf "(floor $)" [print_i ctx i]
         | IUB2n () => sprintf "(b2i $)" [print_i ctx i]
         | IUNeg () => sprintf "(not $)" [print_i ctx i]
         | IUDiv n => sprintf "(/ $ $)" [print_i ctx i, str_int n]
         (* | IUExp s () => sprintf "(^ $ $)" [print_i ctx i, s] *)
      )
    | IBinOp (opr, i1, i2) => 
      (case opr of
           IBMax () =>
           let
               fun max a b =
                   sprintf "(ite (>= $ $) $ $)" [a, b, a, b]
           in
               max (print_i ctx i1) (print_i ctx i2)
           end
         | IBMin () =>
           let
               fun min a b =
                   sprintf "(ite (<= $ $) $ $)" [a, b, a, b]
           in
               min (print_i ctx i1) (print_i ctx i2)
           end
         | IBBoundedMinus () =>
           let
             fun bounded_minus a b =
                 sprintf "(ite (< $ $) 0 (- $ $))" [a, b, a, b]
           in
             bounded_minus (print_i ctx i1) (print_i ctx i2)
           end
         | IBApp () =>
           let
             val (f, is) = collect_IBApp i1 
             val is = f :: is
             val is = is @ [i2]
           in
               (* sprintf "(app_$$)" [str_int (length is - 1), join_prefix " " $ map (print_i ctx) is] *)
               sprintf "($)" [join " " $ map (print_i ctx) is]
           end
         (* | ExpNI () => sprintf "($ $)" [print_idx_bin_op opr, print_i ctx i2] *)
         | _ => 
           sprintf "($ $ $)" [print_idx_bin_op opr, print_i ctx i1, print_i ctx i2]
      )
    | IIte (i1, i2, i3, _) => sprintf "(ite $ $ $)" [print_i ctx i1, print_i ctx i2, print_i ctx i3]
    | IAbs _ => raise SMTError "can't handle abstraction"
    | IState _ => raise SMTError "can't handle IState"
    | IUVar (x, _) =>
      case !x of
          Refined i => print_i ctx i
        | Fresh _ => raise SMTError "index contains uvar"

fun negate s = sprintf "(not $)" [s]

fun print_base_sort b =
  case b of
      BSSUnit () => "Unit"
    | BSSBool () => "Bool"
    | BSSNat () => "Int"
    | BSSTime () => "Real"
    | BSSState () => "Unit"

fun print_bsort bsort =
  case bsort of
      BSBase b => print_base_sort b
    | BSArrow _ => raise SMTError "can't handle higher-order sorts"
    | BSUVar x =>
      case !x of
          Refined b => print_bsort b
        | Fresh _ => raise SMTError "bsort contains uvar"

fun print_p ctx p =
  let
      fun str_conn opr =
        case opr of
            BCAnd () => "and"
          | BCOr () => "or"
          | BCImply () => "=>"
          | BCIff () => "="
      fun str_pred opr =
        case opr of
            BPEq () => "="
          | BPLe () => "<="
          | BPLt () => "<"
          | BPGe () => ">="
          | BPGt () => ">"
          | BPBigO () => raise SMTError "can't handle big-O"
      fun f p =
        case p of
            PTrueFalse (b, _) => str_bool b
          | PNot (p, _) => negate (f p)
          | PBinConn (opr, p1, p2) => sprintf "($ $ $)" [str_conn opr, f p1, f p2]
          (* | BinPred (BigO, i1, i2) => sprintf "(bigO $ $)" [print_i ctx i1, print_i ctx i2] *)
          (* | BinPred (BigO, i1, i2) => "true" *)
          | PBinPred (opr, i1, i2) => sprintf "($ $ $)" [str_pred opr, print_i ctx i1, print_i ctx i2]
          | PQuan (Exists _, bs, Bind ((name, _), p), _) => raise SMTError "Don't trust SMT solver to solve existentials"
          | PQuan (q, bs, Bind ((name, _), p), _) => sprintf "($ (($ $)) $)" [str_quan q, name, print_bsort bs, print_p (name :: ctx) p]
  in
      f p
  end

fun declare_const x sort = 
    (* sprintf "(declare-const $ $)" [x, sort] *)
    sprintf "(declare-fun $ () $)" [x, sort]

fun assert s = 
    sprintf "(assert $)" [s] 

fun assert_p ctx p =
  assert (print_p ctx p)

fun print_hyp ctx h =
    case h of
        VarH (name, bs) =>
        (case update_bs bs of
             BSBase b =>
             (declare_const name (print_base_sort b), name :: ctx)
           | BSArrow _ =>
             let
               val (args, ret) = collect_BSArrow bs
             in
               (sprintf "(declare-fun $ ($) $)" [name, join " " $ map print_bsort args, print_bsort ret], name :: ctx)
             end
           | BSUVar x => raise SMTError "hypothesis contains uvar"
        )
      | PropH p =>
        let
          val p = assert (print_p ctx p)
                  handle SMTError _ => "" (* always sound to discard hypothesis *)
        in
          (p, ctx)
        end

fun prelude get_ce = [
    (* "(set-logic ALL_SUPPORTED)", *)
    if get_ce then "(set-option :produce-models true)" else "",
    (* "(set-option :produce-proofs true)", *)

    "(declare-datatypes () ((Unit TT)))",

    "(declare-fun exp_i_i (Int Int) Int)",
    (* "(assert (forall ((x Real) (y Real))", *)
    (* "  (! (=> (<= 1 y) (= (exp_i_i x y) ( * x (exp_i_i x (- y 1)))))", *)
    (* "  :pattern ((exp_i_i x y)))))", *)
    (* "(assert (forall ((x Real) (y Real))", *)
    (* "  (! (=> (= 0 y) (= (exp_i_i x y) 1))", *)
    (* "  :pattern ((exp_i_i x y)))))", *)
    
    "(declare-fun log (Real Real) Real)",
    (* "(assert (forall ((x Real) (y Real))", *)
    (* "  (! (=> (and (< 0 x) (< 0 y)) (= (log2 ( * x y)) (+ (log2 x) (log2 y))))", *)
    (* "    :pattern ((log2 ( * x y))))))", *)
    (* "(assert (forall ((x Real) (y Real))", *)
    (* "  (! (=> (and (< 0 x) (< 0 y)) (= (log2 (/ x y)) (- (log2 x) (log2 y))))", *)
    (* "    :pattern ((log2 (/ x y))))))", *)
    (* "(assert (= (log2 1) 0))", *)
    (* "(assert (= (log2 2) 1))", *)
    (* "(assert (forall ((x Real) (y Real)) (=> (and (< 0 x) (< 0 y)) (=> (< x y) (< (log2 x) (log2 y))))))", *)
    
    "(define-fun floor ((x Real)) Int",
    "(to_int x))",
    "(define-fun ceil ((x Real)) Int",
    "(to_int (+ x 0.5)))",
    "(define-fun b2i ((b Bool)) Int",
    "(ite b 1 0))",

    
    (* "(declare-datatypes () ((Fun_1 fn1)))", *)
    (* "(declare-datatypes () ((Fun_2 fn2)))", *)
    (* "(declare-fun app_1 (Fun_1 Int) Real)", *)
    (* "(declare-fun app_2 (Fun_2 Int Int) Real)", *)
    (* "(declare-fun bigO (Fun_2 Fun_2) Bool)", *)
    
    ""
]

val push = [
    "(push 1)"
]

val pop = [
    "(pop 1)"
]

fun check get_ce = [
    "(check-sat)",
    if get_ce then "(get-model)" else ""
    (* "(get-proof)" *)
    (* "(get-value (n))", *)
]

(* convert to Z3's types and naming conventions *)
fun conv_base_sort b =
      case b of
          BSSUnit () => (BSSUnit (), NONE)
        | BSSBool () => (BSSBool (), NONE)
        | BSSNat () => (BSSNat (), SOME (PBinPred (BPLe (), INat (0, dummy), IVar (ID (0, dummy), []))))
        | BSSTime () => (BSSTime (), SOME (PBinPred (BPLe (), ITime (TimeType.zero, dummy), IVar (ID (0, dummy), []))))
        | BSSState () => (BSSUnit (), NONE)

fun conv_bsort bsort =
  case bsort of
      BSBase b =>
      let
        val (b, p) = conv_base_sort b
      in
        (BSBase b, p)
      end
    | BSArrow _ => (bsort, NONE)
    | BSUVar x =>
      case !x of
          Refined b => conv_bsort b
        | Fresh _ => raise SMTError "bsort contains uvar"

fun conv_p p =
    case p of
        PQuan (q, bs, Bind ((name, r), p), r_all) => 
        let 
            val (bs, p1) = conv_bsort bs
            val p = conv_p p
            val p = case p1 of
                        NONE => p
                      | SOME p1 => (p1 --> p)
        in
            PQuan (q, bs, Bind ((escape name, r), p), r_all)
        end
      | PNot (p, r) => PNot (conv_p p, r)
      | PBinConn (opr, p1, p2) => PBinConn (opr, conv_p p1, conv_p p2)
      | PBinPred _ => p
      | PTrueFalse _ => p

fun conv_hyp h =
    case h of
        PropH _ => [h]
      | VarH (name, bs) =>
        let
            val (bs, p) = conv_bsort bs
            val hs = [VarH (escape name, bs)]
            val hs = hs @ (case p of SOME p => [PropH p] | _ => [])
        in
            hs
        end

fun print_vc get_ce ((hyps, goal) : vc) =
  let
      val hyps = rev hyps
      val hyps = concatMap conv_hyp hyps
      val goal = conv_p goal
      val lines = push
      val (hyps, ctx) = foldl (fn (h, (hs, ctx)) => let val (h, ctx) = print_hyp ctx h in (h :: hs, ctx) end) ([], []) hyps
      val hyps = rev hyps
      val lines = lines @ hyps
      val lines = lines @ [assert (negate (print_p ctx goal))]
      val lines = lines @ check get_ce
      val lines = lines @ pop
      val lines = lines @ [""]
  in
      lines
  end

fun to_smt2 get_ce vcs = 
  let
      val lines =
	  concatMap (print_vc get_ce) vcs
      val lines = prelude get_ce @ lines
      val s = join_lines lines
  in
      s
  end

end

(* open CheckNoUVar *)
(* val vcs = map no_uvar_vc vcs *)
(*           handle NoUVarError _ => raise SMTError "VC contains uvar" *)
                          
