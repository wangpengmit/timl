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
         | Ceil
         | Floor
         | B2n
         | Neg
         | IUDiv of int
         | Log of string
         (* | IUExp of string *)

val Log2 = Log "2"
val Log10 = Log "10"
               
datatype idx_bin_op =
	 AddI
	 | MultI
         | ModI
	 | MaxI
	 | MinI
         | IApp 
         | EqI
         | AndI
         | OrI
         | ExpNI
         | LtI
         | GtI
         | LeI
         | GeI
         | BoundedMinusI
         | MinusI (* only used internally for annotation propagation *)
         | IBUnion

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
         | ECBool of bool
         | ECiBool of bool
         | ECByte of Char.char
         (* | ECString of string *)

(* projector for product type *)
datatype projector =
         ProjFst
         | ProjSnd

(* primitive unary term operators *)
datatype prim_expr_un_op =
         EUPIntNeg
         | EUPBoolNeg
         | EUPInt2Byte
         | EUPByte2Int
         (* | EUPInt2Str *)
         (* | EUPStrLen *)
                         
datatype expr_un_op =
         EUProj of projector
         | EUPrim of prim_expr_un_op
         | EUArrayLen
         | EUNat2Int
         | EUInt2Nat
         | EUPrintc
(* | EUPrint *)
         | EUStorageGet

fun str_expr_const c =
  case c of
      ECTT => "()"
    | ECInt n => str_int n
    | ECNat n => sprintf "#$" [str_int n]
    | ECiBool b => sprintf "#$" [str_bool b]
    | ECBool b => str_bool b
    | ECByte c => Char.toCString c
    (* | ECString s => surround "\"" "\"" s *)
                                
fun str_proj opr =
  case opr of
      ProjFst => "fst"
    | ProjSnd => "snd"

fun str_prim_expr_un_op opr =
  case opr of
      EUPIntNeg => "int_neg"
    | EUPBoolNeg => "not"
    | EUPInt2Byte => "int2byte"
    | EUPByte2Int => "byte2int"
    (* | EUPInt2Str => "int2str" *)
    (* | EUPStrLen => "str_len" *)
                   
fun str_expr_un_op opr = 
  case opr of
      EUProj opr => str_proj opr
    | EUPrim opr => str_prim_expr_un_op opr
    | EUArrayLen => "array_len"
    | EUNat2Int => "nat2int"
    | EUInt2Nat => "int2nat"
    | EUPrintc => "printc"
(* | EUPrint => "print" *)
    | EUStorageGet => "storage_get"

(* primitive binary term operators *)
datatype prim_expr_bin_op =
         EBPIntAdd
         | EBPIntMinus
         | EBPIntMult
         | EBPIntDiv
         | EBPIntMod
         | EBPIntLt
         | EBPIntGt
         | EBPIntLe
         | EBPIntGe
         | EBPIntEq
         | EBPIntNEq
         | EBPBoolAnd
         | EBPBoolOr
(* | EBPStrConcat *)

(* binary nat operators *)
datatype nat_expr_bin_op =
         EBNAdd
         | EBNBoundedMinus
         | EBNMult
         | EBNDiv

datatype nat_cmp =
         NCLt
         | NCGt
         | NCLe
         | NCGe
         | NCEq
         | NCNEq
         
datatype expr_bin_op =
         EBApp
         | EBPair
         | EBNew
         | EBRead
         | EBPrim of prim_expr_bin_op
         | EBNat of nat_expr_bin_op
         | EBNatCmp of nat_cmp
         | EBVectorGet
         | EBVectorPushBack
         | EBMapPtr
         | EBStorageSet

fun str_prim_expr_bin_op opr =
  case opr of
      EBPIntAdd => "add"
    | EBPIntMult => "mult"
    | EBPIntMinus => "minus"
    | EBPIntDiv => "div"
    | EBPIntMod => "mod"
    | EBPIntLt => "lt"
    | EBPIntGt => "gt"
    | EBPIntLe => "le"
    | EBPIntGe => "ge"
    | EBPIntEq => "eq"
    | EBPIntNEq => "neq"
    | EBPBoolAnd => "and"
    | EBPBoolOr => "or"
    (* | EBPStrConcat => "str_concat" *)

fun str_nat_expr_bin_op opr =
  case opr of
      EBNAdd => "nat_add"
    | EBNBoundedMinus => "nat_bounded_minus"
    | EBNMult => "mult"
    | EBNDiv => "div"

fun str_nat_cmp opr =
  case opr of
      NCLt => "nat_lt"
    | NCGt => "nat_gt"
    | NCLe => "nat_le"
    | NCGe => "nat_ge"
    | NCEq => "nat_eq"
    | NCNEq => "nat_neq"
                    
fun str_expr_bin_op opr =
  case opr of
      EBApp => "app"
    | EBPair => "pair"
    | EBNew => "new"
    | EBRead => "read"
    | EBPrim opr => str_prim_expr_bin_op opr
    | EBNat opr => str_nat_expr_bin_op opr
    | EBNatCmp opr => str_nat_cmp opr
    | EBVectorGet => "vector_get"
    | EBVectorPushBack => "vector_push_back"
    | EBMapPtr => "map_ptr"
    | EStorageSet => "storage_set"

fun pretty_str_prim_expr_bin_op opr =
  case opr of
      EBPIntAdd => "+"
    | EBPIntMult => "*"
    | EBPIntMinus => "-"
    | EBPIntDiv => "/"
    | EBPIntMod => "mod"
    | EBPIntLt => "<"
    | EBPIntGt => ">"
    | EBPIntLe => "<="
    | EBPIntGe => ">="
    | EBPIntEq => "="
    | EBPIntNEq => "<>"
    | EBPBoolAnd => "$$"
    | EBPBoolOr => "||"
    (* | EBPStrConcat => "^" *)

fun pretty_str_nat_expr_bin_op opr =
  case opr of
      EBNAdd => "#+"
    | EBNBoundedMinus => "#-"
    | EBNMult => "#*"
    | EBNDiv => "#/"
                    
fun pretty_str_nat_cmp opr =
  case opr of
      NCLt => "#<"
    | NCGt => "#>"
    | NCLe => "#<="
    | NCGe => "#>="
    | NCEq => "#="
    | NCNEq => "#<>"
                    
fun pretty_str_expr_bin_op opr =
  case opr of
      EBApp => "$"
    | EBPair => "pair"
    | EBNew => "new"
    | EBRead => "read"
    | EBPrim opr => pretty_str_prim_expr_bin_op opr
    | EBNat opr => pretty_str_nat_expr_bin_op opr
    | EBNatCmp opr => pretty_str_nat_cmp opr
    | EBVectorGet => "vector_get"
    | EBVectorPushBack => "vector_push_back"
    | EBMapPtr => "map_ptr"
    | EStorageSet => "storage_set"

datatype expr_tri_op =
         ETWrite
         | ETIte
         | ETVectorSet

fun str_expr_tri_op opr =
  case opr of
      ETWrite => "write"
    | ETIte => "ite"
    | ETVectorSet => "vector_set"
                  
datatype expr_EI =
         EEIAppI
         | EEIAscTime

datatype expr_ET =
         EETAppT
         | EETAsc
         | EETHalt

datatype expr_T =
         ETNever
         | ETBuiltin of string
         (* | ETEmptyArray *)
             
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
    | Log base => sprintf "log$" [base]
    | Ceil => "ceil"
    | Floor => "floor"
    | B2n => "b2n"
    | Neg => "not"
    | IUDiv d => sprintf "(/ $)" [str_int d]
    (* | IUExp s => sprintf "( ** $)" [s] *)

fun str_idx_bin_op opr =
  case opr of
      AddI => "+"
    | MultI => " *"
    | ModI => "mod"
    | MaxI => "max"
    | MinI => "min"
    | IApp => "app"
    | AndI => "&&"
    | OrI => "||"
    | ExpNI => "**"
    | EqI => "=?"
    | LtI => "<?"
    | GtI => ">?"
    | LeI => "<=?"
    | GeI => ">=?"
    | BoundedMinusI => "-"
    | MinusI => "MinusI"
    | IBUnion => "IBUnion"

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

fun str_expr_EI opr =
  case opr of
      EEIAppI => "EEIAppI"
    | EEIAscTime => "EEIAscTime"

fun str_expr_ET opr =
  case opr of
      EETAppT => "EETAppT"
    | EETAsc => "EETAsc"
    | EETHalt => "EETHalt"

fun str_expr_T opr =
  case opr of
      ETNever => "ETNever"
    | ETBuiltin name => sprintf "ETBuiltin($)" [name]
                  
end
