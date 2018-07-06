structure Operators = struct

open Util

datatype idx_const =
         ICBool of bool
	 | ICTT of unit
         | ICAdmit of unit
         | ICNat of int
         | ICTime of TimeType.time

datatype idx_un_op =
         IUToReal of unit
         | IUCeil of unit
         | IUFloor of unit
         | IUB2n of unit
         | IUNeg of unit
         | IUDiv of int
         | IULog of string
         (* | IUExp of string *)

val IULog2 = IULog "2"
val IULog10 = IULog "10"
               
datatype idx_bin_op =
	 IBAdd of unit
	 | IBMult of unit
         | IBMod of unit
	 | IBMax of unit
	 | IBMin of unit
         | IBApp of unit 
         | IBEq of unit
         | IBAnd of unit
         | IBOr of unit
         | IBExpN of unit
         | IBLt of unit
         | IBGt of unit
         | IBLe of unit
         | IBGe of unit
         | IBBoundedMinus of unit
         | IBMinus of unit (* only used internally for annotation propagation *)
         | IBUnion of unit

(* binary logical connectives *)
datatype bin_conn =
	 BCAnd of unit
	 | BCOr of unit
	 | BCImply of unit
	 | BCIff of unit

(* binary predicates on indices *)
datatype bin_pred =
         BPEq of unit
         | BPLe of unit
         | BPLt of unit
         | BPGe of unit
         | BPGt of unit
         | BPBigO of unit
               
(* existential quantifier might carry other information such as a unification variable to update when this existential quantifier gets instantiated *)
datatype 'a quan =
         Forall of unit
         | Exists of 'a

type nat = int

datatype env_info =
         EnvSender of unit
         | EnvValue of unit
         | EnvNow of unit
         | EnvThis of unit
         | EnvBlockNumber of unit
             
datatype expr_const =
         ECTT of unit
         | ECNat of nat
         | ECInt of string
         | ECBool of bool
         | ECiBool of bool
         | ECByte of Char.char
(* | ECString of string *)

(* projector for product type *)
datatype projector =
         ProjFst of unit
         | ProjSnd of unit

fun choose (t1, t2) proj =
  case proj of
      ProjFst () => t1
    | ProjSnd () => t2
                                 
datatype expr_anno =
         EALiveVars of int(* num of live vars afterwards *) * bool(*does it have continuation?*)
         | EABodyOfRecur of unit (* this is the body of a recursive function *)
         | EAFreeEVars of int (* num of free expression vars (excluding argument and recursive self-reference) *)
         | EAConstr of unit
                         
(* primitive unary term operators *)
datatype prim_expr_un_op =
         EUPIntNeg of unit
         | EUPBoolNeg of unit
         | EUPInt2Byte of unit
         | EUPByte2Int of unit
         (* | EUPInt2Str of unit *)
(* | EUPStrLen of unit *)

datatype expr_un_op =
         EUProj of projector
         | EUPrim of prim_expr_un_op
         | EUArrayLen of unit
         | EUNat2Int of unit
         | EUInt2Nat of unit
         | EUPrintc of unit
(* | EUPrint of unit *)
         | EUStorageGet of unit
         | EUVectorClear of unit
         | EUVectorLen of unit
         | EUAnno of expr_anno
         | EUField of string * int option

fun str_env_info name =
    case name of
        EnvSender () => "sender"
      | EnvValue () => "value"
      | EnvNow () => "now"
      | EnvThis () => "this"
      | EnvBlockNumber () => "block.number"
                        
fun str_expr_const c =
  case c of
      ECTT () => "()"
    | ECInt n => n
    | ECNat n => sprintf "#$" [str_int n]
    | ECiBool b => sprintf "#$" [str_bool b]
    | ECBool b => str_bool b
    | ECByte c => str_char c
(* | ECString s => surround "\"" "\"" s *)
                                
fun str_proj opr =
  case opr of
      ProjFst () => "fst"
    | ProjSnd () => "snd"

fun str_prim_expr_un_op opr =
  case opr of
      EUPIntNeg () => "int_neg"
    | EUPBoolNeg () => "not"
    | EUPInt2Byte () => "int2byte"
    | EUPByte2Int () => "byte2int"
    (* | EUPInt2Str => "int2str" *)
    (* | EUPStrLen => "str_len" *)
                   
fun str_expr_anno a =
  case a of
      EALiveVars (n, b) => sprintf "live_vars ($, $)" [str_int n, str_bool b]
    | EABodyOfRecur () => "body_of_recur"
    | EAFreeEVars n => "free_evars " ^ str_int n
    | EAConstr () => "constr"
                            
fun str_expr_un_op opr = 
  case opr of
      EUProj opr => str_proj opr
    | EUPrim opr => str_prim_expr_un_op opr
    | EUArrayLen () => "array_len"
    | EUNat2Int () => "nat2int"
    | EUInt2Nat () => "int2nat"
    | EUPrintc () => "printc"
(* | EUPrint => "print" *)
    | EUStorageGet () => "storage_get"
    | EUVectorClear () => "vector_clear"
    | EUVectorLen () => "vector_len"
    | EUAnno a => str_expr_anno a
    | EUField name => "field " ^ name

(* primitive binary term operators *)
datatype prim_expr_bin_op =
         EBPIntAdd of unit
         | EBPIntMinus of unit
         | EBPIntMult of unit
         | EBPIntDiv of unit
         | EBPIntMod of unit
         | EBPIntExp of unit
         | EBPIntLt of unit
         | EBPIntGt of unit
         | EBPIntLe of unit
         | EBPIntGe of unit
         | EBPIntEq of unit
         | EBPIntNEq of unit
         | EBPBoolAnd of unit
         | EBPBoolOr of unit
(* | EBPStrConcat *)

(* binary nat operators *)
datatype nat_expr_bin_op =
         EBNAdd of unit
         | EBNBoundedMinus of unit
         | EBNMult of unit
         | EBNDiv of unit

datatype nat_cmp =
         NCLt of unit
         | NCGt of unit
         | NCLe of unit
         | NCGe of unit
         | NCEq of unit
         | NCNEq of unit
                      
datatype expr_bin_op =
         EBApp of unit
         | EBPair of unit
         | EBNew of unit
         | EBRead of unit
         | EBVectorGet of unit
         | EBVectorPushBack of unit
         | EBMapPtr of unit
         | EBStorageSet of unit
         | EBPrim of prim_expr_bin_op
         | EBNat of nat_expr_bin_op
         | EBNatCmp of nat_cmp

fun str_prim_expr_bin_op opr =
  case opr of
      EBPIntAdd () => "add"
    | EBPIntMult () => "mult"
    | EBPIntMinus () => "minus"
    | EBPIntDiv () => "div"
    | EBPIntMod () => "mod"
    | EBPIntExp () => "exp"
    | EBPIntLt () => "lt"
    | EBPIntGt () => "gt"
    | EBPIntLe () => "le"
    | EBPIntGe () => "ge"
    | EBPIntEq () => "eq"
    | EBPIntNEq () => "neq"
    | EBPBoolAnd () => "and"
    | EBPBoolOr () => "or"
    (* | EBPStrConcat () => "str_concat" *)

fun str_nat_expr_bin_op opr =
  case opr of
      EBNAdd () => "nat_add"
    | EBNBoundedMinus () => "nat_bounded_minus"
    | EBNMult () => "mult"
    | EBNDiv () => "div"

fun str_nat_cmp opr =
  case opr of
      NCLt () => "nat_lt"
    | NCGt () => "nat_gt"
    | NCLe () => "nat_le"
    | NCGe () => "nat_ge"
    | NCEq () => "nat_eq"
    | NCNEq () => "nat_neq"
                    
fun str_expr_bin_op opr =
  case opr of
      EBApp _ => "app"
    | EBPair () => "pair"
    | EBNew () => "new"
    | EBRead () => "read"
    | EBPrim opr => str_prim_expr_bin_op opr
    | EBNat opr => str_nat_expr_bin_op opr
    | EBNatCmp opr => str_nat_cmp opr
    | EBVectorGet () => "vector_get"
    | EBVectorPushBack () => "vector_push_back"
    | EBMapPtr () => "map_ptr"
    | EBStorageSet () => "storage_set"

fun pretty_str_prim_expr_bin_op opr =
  case opr of
      EBPIntAdd () => "+"
    | EBPIntMult () => "*"
    | EBPIntMinus () => "-"
    | EBPIntDiv () => "/"
    | EBPIntMod () => "mod"
    | EBPIntExp () => "exp"
    | EBPIntLt () => "<"
    | EBPIntGt () => ">"
    | EBPIntLe () => "<="
    | EBPIntGe () => ">="
    | EBPIntEq () => "="
    | EBPIntNEq () => "<>"
    | EBPBoolAnd () => "$$"
    | EBPBoolOr () => "||"
    (* | EBPStrConcat () => "^" *)

fun pretty_str_nat_expr_bin_op opr =
  case opr of
      EBNAdd () => "#+"
    | EBNBoundedMinus () => "#-"
    | EBNMult () => "#*"
    | EBNDiv () => "#/"
                    
fun pretty_str_nat_cmp opr =
  case opr of
      NCLt () => "#<"
    | NCGt () => "#>"
    | NCLe () => "#<="
    | NCGe () => "#>="
    | NCEq () => "#="
    | NCNEq () => "#<>"
                    
fun pretty_str_expr_bin_op opr =
  case opr of
      EBApp _ => "$"
    | EBPair () => "pair"
    | EBNew () => "new"
    | EBRead () => "read"
    | EBPrim opr => pretty_str_prim_expr_bin_op opr
    | EBNat opr => pretty_str_nat_expr_bin_op opr
    | EBNatCmp opr => pretty_str_nat_cmp opr
    | EBVectorGet () => "vector_get"
    | EBVectorPushBack () => "vector_push_back"
    | EBMapPtr () => "map_ptr"
    | EBStorageSet () => "storage_set"

datatype expr_tri_op =
         ETWrite of unit
         | ETIte of unit
         | ETVectorSet of unit

fun str_expr_tri_op opr =
  case opr of
      ETWrite () => "write"
    | ETIte _ => "ite"
    | ETVectorSet () => "vector_set"
                  
datatype expr_EI =
         EEIAppI of unit
         | EEIAscTime of unit
         | EEIAscSpace of unit

datatype expr_ET =
         EETAppT of unit
         | EETAsc of unit
         | EETHalt of unit

datatype expr_T =
         ETNever of unit
         | ETBuiltin of string
         (* | ETEmptyArray *)
             
fun str_idx_const c =
  case c of
      ICBool b => str_bool b
    | ICTT () => "()"
    | ICAdmit () => "admit"
    | ICNat n => str_int n
    | ICTime x => TimeType.str_time x

fun str_idx_un_op opr =
  case opr of
      IUToReal () => "$"
    | IULog base => sprintf "log$" [base]
    | IUCeil () => "ceil"
    | IUFloor () => "floor"
    | IUB2n () => "b2n"
    | IUNeg () => "not"
    | IUDiv d => sprintf "(/ $)" [str_int d]
    (* | IUExp s => sprintf "( ** $)" [s] *)

fun str_idx_bin_op opr =
  case opr of
      IBAdd () => "+"
    | IBMult () => " *"
    | IBMod () => "mod"
    | IBMax () => "max"
    | IBMin () => "min"
    | IBApp () => "app"
    | IBAnd () => "&&"
    | IBOr () => "||"
    | IBExpN () => "**"
    | IBEq () => "=?"
    | IBLt () => "<?"
    | IBGt () => ">?"
    | IBLe () => "<=?"
    | IBGe () => ">=?"
    | IBBoundedMinus () => "-"
    | IBMinus () => "MinusI"
    | IBUnion () => "++"

fun str_bin_conn opr =
  case opr of
      BCAnd () => "/\\"
    | BCOr () => "\\/"
    | BCImply () => "->"
    | BCIff () => "<->"

fun str_bin_pred opr =
  case opr of
      BPEq () => "="
    | BPLe () => "<="
    | BPLt () => "<"
    | BPGe () => ">="
    | BPGt () => ">"
    | BPBigO () => "<=="

fun strip_quan q =
  case q of
      Forall () => Forall ()
    | Exists _ => Exists ()
                         
fun str_quan q =
    case q of
        Forall () => "forall"
      | Exists _ => "exists"

fun str_expr_EI opr =
  case opr of
      EEIAppI () => "EEIAppI"
    | EEIAscTime () => "EEIAscTime"
    | EEIAscSpace () => "EEIAscSpace"

fun str_expr_ET opr =
  case opr of
      EETAppT () => "EETAppT"
    | EETAsc () => "EETAsc"
    | EETHalt () => "EETHalt"

fun str_expr_T opr =
  case opr of
      ETNever () => "ETNever"
    | ETBuiltin name => sprintf "ETBuiltin($)" [name]
                  
end
