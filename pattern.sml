structure Pattern = struct

open Namespaces
open Binders
open Unbound
open Region
       
datatype ('cvar, 'mtype) ptrn =
	 PnConstr of ('cvar * bool(*eia*)) outer * iname binder list * ('cvar, 'mtype) ptrn * region (* eia : is explicit index arguments? *)                                         
         | PnVar of ename binder
         | PnPair of ('cvar, 'mtype) ptrn * ('cvar, 'mtype) ptrn
         | PnTT of region
         | PnAlias of ename binder * ('cvar, 'mtype) ptrn * region
         | PnAnno of ('cvar, 'mtype) ptrn * 'mtype outer

end
