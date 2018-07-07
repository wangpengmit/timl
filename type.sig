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
           | TRecord of mtype SMap.map * region
           | TState of string * region
           | TMap of mtype
           | TVector of mtype (* the purpose of vector is that elements stored in vector are guaranteed to be well-formed and may not be nullable (such as (ex {n | n>5}, nat {n})) (while elements stored in maps must be nullable) *)
           | TRef of mtype
           | TNatCell of unit
           | TPtr of mtype list * int

  datatype ty = 
	   PTMono of mtype
	   | PTUni of (idx * idx) * (name * ty) Bind.tbind * region

end
