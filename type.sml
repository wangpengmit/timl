signature TYPE_PARAMS = sig
  structure Idx : IDX
  structure UVarT : UVAR_T
  type base_type
end         

functor TypeFn (Params : TYPE_PARAMS) =
struct

open Params
open UVarT
open Idx
open Bind
                        
type kind = int (*number of type arguments*) * basic_sort list

type 'mtype constr_core = (sort, name, 'mtype * idx list) ibinds
type 'mtype constr_decl = name * 'mtype constr_core * region
(* to be used in typing context *)                                                          
type 'mtype constr_info = var(*family*) * (unit, name, 'mtype constr_core) tbinds

type 'mtype datatype_def = (name(*for datatype self-reference*) * (unit, name, Idx.basic_sort list * 'mtype constr_decl list) Bind.tbinds) Bind.tbind

(* monotypes *)
datatype mtype = 
	 TArrow of (idx StMap.map * mtype) * (idx * idx) * (idx StMap.map * mtype)
         | TNat of idx * region
         | TiBool of idx * region
         | TArray of mtype * idx
	 | TBase of base_type * region
         | TUnit of region
	 | TProd of mtype * mtype
	 | TUniI of sort * (name * ((idx * idx) * mtype)) ibind * region
         | TVar of var
         | TAbs of kind * (name * mtype) tbind * region
         | TApp of mtype * mtype
         | TAbsI of basic_sort * (name * mtype) ibind  * region
         | TAppI of mtype * idx
         | TUVar of (basic_sort, kind, mtype) uvar_mt * region
         | TDatatype of mtype datatype_def * region
         | TSumbool of sort * sort
         | TMap of mtype
         | TVector of mtype
         | TState of string * region
         | TRecord of mtype SMap.map * region
         | TTuplePtr of mtype list * int * region

datatype ty = 
	 PTMono of mtype
	 | PTUni of (idx * idx) * (name * ty) tbind * region

end

functor TestTypeFnSignatures (Params : TYPE_PARAMS) = struct
structure M : TYPE = TypeFn (Params)
end
