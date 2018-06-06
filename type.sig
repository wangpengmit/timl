signature TYPE = sig

  type basic_sort
  type idx
  type sort
  type base_type
  type var
  (* type kind *)
  type kind = int (*number of type arguments*) * basic_sort list
  type name
  type region
  include UVAR_T
         
  type 'mtype constr_core = (sort, name, 'mtype * idx list) Bind.ibinds
  type 'mtype constr_decl = name * 'mtype constr_core * region
  (* to be used in typing context *)                                                          
  type 'mtype constr_info = var(*family*) * (unit, name, 'mtype constr_core) Bind.tbinds

  type 'mtype datatype_def = (name(*for datatype self-reference*) * (unit, name, basic_sort list * 'mtype constr_decl list) Bind.tbinds) Bind.tbind

  (* monotypes *)
  datatype mtype = 
	   TArrow of (idx StMap.map * mtype) * (idx * idx) * (idx StMap.map * mtype)
           | TNat of idx * region
           | TiBool of idx * region
           | TArray of mtype * idx
	   | TBase of base_type * region
           | TUnit of region
	   | TProd of mtype * mtype
	   | TUniI of sort * (name * ((idx * idx) * mtype)) Bind.ibind * region
           | TVar of var
           | TAbs of kind * (name * mtype) Bind.tbind * region
           | TApp of mtype * mtype
           | TAbsI of basic_sort * (name * mtype) Bind.ibind  * region
           | TAppI of mtype * idx
           | TUVar of (basic_sort, kind, mtype) uvar_mt * region
           | TDatatype of mtype datatype_def * region
           | TSumbool of sort * sort
           | TMap of mtype
           | TState of string * region
           | TTuplePtr of mtype list * int * region

  datatype ty = 
	   PTMono of mtype
	   | PTUni of (name * ty) Bind.tbind * region

end
