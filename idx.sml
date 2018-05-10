signature IDX_PARAMS = sig
  structure UVarI : UVAR_I
  type base_sort
  type var
  type name
  type region
  type 'idx exists_anno
end         

functor IdxFn (Params : IDX_PARAMS) =
struct

open Params
open UVarI
open Bind
open Operators
                        
(* base sorts with arrow and uvar *)
datatype basic_sort = 
         BSBase of base_sort 
         | BSArrow of basic_sort * basic_sort
         | BSUVar of basic_sort uvar_bs
                                 
datatype idx =
	 IVar of var * sort list
         | IConst of idx_const * region
         | IUnOp of idx_un_op * idx * region
         | IBinOp of idx_bin_op * idx * idx
         | IIte of idx * idx * idx * region
         | IAbs of basic_sort * (name * idx) ibind * region
         | IState of idx StMap.map
         | IUVar of (basic_sort, idx) uvar_i * region

and prop =
	 PTrueFalse of bool * region
         | PBinConn of bin_conn * prop * prop
         | PNot of prop * region
	 | PBinPred of bin_pred * idx * idx
         | PQuan of idx exists_anno (*for linking idx inferer with types*) quan * basic_sort * (name * prop) ibind * region

and sort =
	 SBasic of basic_sort * region
	 | SSubset of (basic_sort * region) * (name * prop) ibind * region
         | SUVar of (basic_sort, sort) uvar_s * region
         (* [SAbs] and [SApp] are just for higher-order unification *)
         | SAbs of basic_sort * (name * sort) ibind * region
         | SApp of sort * idx
                            
end

functor TestIdxFnSignatures (Params : IDX_PARAMS) = struct
structure M : IDX = IdxFn (Params)
end

