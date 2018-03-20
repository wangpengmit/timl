structure Operators = struct

open Util

datatype idx_const =
         ICBool of bool
	 | ICTT
         | ICAdmit
         | ICNat of int
         | ICTime of TimeType.time

datatype idx_un_op =
         ToReal
         | Log2
         | Ceil
         | Floor
         | B2n
         | Neg
         | IUDiv of int
         | IUExp of string
               
datatype idx_bin_op =
	 AddI
	 | MultI
	 | MaxI
	 | MinI
         | IApp 
         | EqI
         | AndI
         | ExpNI
         | LtI
         | GeI
         | BoundedMinusI
         | MinusI (* only used internally for annotation propagation *)

(* binary logical connectives *)
datatype bin_conn =
	 And
	 | Or
	 | Imply
	 | Iff

(* binary predicates on indices *)
datatype bin_pred =
         EqP
         | LeP
         | LtP
         | GeP
         | GtP
         | BigO
               
(* existential quantifier might carry other information such as a unification variable to update when this existential quantifier gets instantiated *)
datatype 'a quan =
         Forall
         | Exists of 'a

type nat = int

datatype expr_const =
         ECTT
         | ECNat of nat
         | ECInt of int
         | ECString of string

(* projector for product type *)
datatype projector =
         ProjFst
         | ProjSnd

(* primitive unary term operators *)
datatype prim_expr_un_op =
         EUPIntNeg
         | EUPBoolNeg
         | EUPInt2Str
         | EUPStrLen
                         
datatype expr_un_op =
         EUProj of projector
         | EUPrim of prim_expr_un_op
         | EUPrint
         | EUArrayLen

(* primitive binary term operators *)
datatype prim_expr_bin_op =
         EBPIntAdd
         | EBPIntMinus
         | EBPIntMult
         | EBPIntDiv
         | EBPIntLt
         | EBPIntGt
         | EBPIntLe
         | EBPIntGe
         | EBPIntEq
         | EBPIntNEq
         | EBPBoolAnd
         | EBPBoolOr
         | EBPStrConcat

(* binary nat operators *)
datatype nat_expr_bin_op =
         EBNAdd
         | EBNBoundedMinus
         | EBNMult
         | EBNDiv
         
datatype expr_bin_op =
         EBApp
         | EBPair
         | EBNew
         | EBRead
         | EBPrim of prim_expr_bin_op
         | EBNat of nat_expr_bin_op

datatype expr_tri_op =
         ETWrite
         | ETIte

datatype expr_EI =
         EEIAppI
         | EEIAscTime

datatype expr_ET =
         EETAppT
         | EETAsc

datatype expr_T =
         ETNever
         | ETBuiltin of string
             
fun str_idx_const c =
  case c of
      ICBool b => str_bool b
    | ICTT => "()"
    | ICAdmit => "admit"
    | ICNat n => str_int n
    | ICTime x => TimeType.str_time x

fun str_idx_un_op opr =
  case opr of
      ToReal => "$"
    | Log2 => "log2"
    | Ceil => "ceil"
    | Floor => "floor"
    | B2n => "b2n"
    | Neg => "not"
    | IUDiv d => sprintf "(/ $)" [str_int d]
    | IUExp s => sprintf "(^ $)" [s]

fun str_idx_bin_op opr =
  case opr of
      AddI => "+"
    | MultI => " *"
    | MaxI => "max"
    | MinI => "min"
    | IApp => "app"
    | EqI => "=="
    | AndI => "&&"
    | ExpNI => "^"
    | LtI => "<"
    | GeI => ">="
    | BoundedMinusI => "-"
    | MinusI => "MinusI"

fun str_bin_conn opr =
  case opr of
      And => "/\\"
    | Or => "\\/"
    | Imply => "->"
    | Iff => "<->"

fun str_bin_pred opr =
  case opr of
      EqP => "="
    | LeP => "<="
    | LtP => "<"
    | GeP => ">="
    | GtP => ">"
    | BigO => "<=="

fun strip_quan q =
  case q of
      Forall => Forall
    | Exists _ => Exists ()
                         
fun str_quan q =
    case q of
        Forall => "forall"
      | Exists _ => "exists"

fun str_bin_op opr =
  case opr of
      EBApp => "$"
    | EBPair => "pair"
    | EBAdd => "+"
    | EBNew => "new"
    | EBRead => "read"
    | EBNatAdd => "#+"
    | EBStrConcat => "^"

fun str_expr_EI opr =
  case opr of
      EEIAppI => "EEIAppI"
    | EEIAscTime => "EEIAscTime"

fun str_expr_ET opr =
  case opr of
      EETAppT => "EETAppT"
    | EETAsc => "EETAsc"

fun str_expr_T opr =
  case opr of
      ETNever => "ETNever"
    | ETBuiltin name => sprintf "ETBuiltin($)" [name]
                  
fun str_expr_const c =
  case c of
      ECTT => "()"
    | ECInt n => str_int n
    | ECNat n => sprintf "#$" [str_int n]
    | ECString s => surround "\"" "\"" s
                                
fun str_proj opr =
  case opr of
      ProjFst => "fst"
    | ProjSnd => "snd"

fun str_expr_un_op opr = 
  case opr of
      EUFst => "fst"
    | EUSnd => "snd"
    | EUPrint => "print"
    | EUInt2Str => "int2str"

fun str_prim_expr_bin_op opr =
  case opr of
      PEBIntAdd => "add"
    | PEBIntMult => "mult"

fun str_expr_bin_op opr =
  case opr of
      EBApp => "app"
    | EBPair => "pair"
    | EBNew => "new"
    | EBRead => "read"
    | EBPrim opr => str_prim_expr_bin_op opr
    | EBNatAdd => "nat_add"

end
