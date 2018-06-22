structure StMap = SMap
structure StMapU = SMapU
                             
signature IDX = sig

  type base_sort
  type var
  type name
  type region
  include UVAR_I
  type 'idx exists_anno
         
  datatype basic_sort = 
           BSBase of base_sort 
           | BSArrow of basic_sort * basic_sort
           | BSUVar of basic_sort uvar_bs
                             
  datatype idx =
	   IVar of var * sort list(*annotation*)(*todo: no longer needed by CC*)
           | IConst of Operators.idx_const * region
           | IUnOp of Operators.idx_un_op * idx * region
           | IBinOp of Operators.idx_bin_op * idx * idx
           | IIte of idx * idx * idx * region
           | IAbs of basic_sort * (name * idx) Bind.ibind * region
           | IState of idx StMap.map
           | IUVar of (basic_sort, idx) uvar_i * region

  and prop =
	   PTrueFalse of bool * region
           | PBinConn of Operators.bin_conn * prop * prop
           | PNot of prop * region
	   | PBinPred of Operators.bin_pred * idx * idx
           | PQuan of idx exists_anno (*for linking idx inferer with types*) Operators.quan * basic_sort * (name * prop) Bind.ibind * region

  and sort =
	   SBasic of basic_sort * region
	   | SSubset of (basic_sort * region) * (name * prop) Bind.ibind * region
           | SUVar of (basic_sort, sort) uvar_s * region
           (* [SAbs] and [SApp] are just for higher-order unification *)
           | SAbs of basic_sort * (name * sort) Bind.ibind * region
           | SApp of sort * idx
                              
end
