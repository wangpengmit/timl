structure Pattern = struct

open Namespaces
open Binders
open Unbound
open Region
       
datatype ('cvar, 'mtype) ptrn =
	 ConstrP of ('cvar * bool(*eia*)) outer * iname binder list * ('cvar, 'mtype) ptrn * region (* eia : is explicit index arguments? *)                                         
         | VarP of ename binder
         | PairP of ('cvar, 'mtype) ptrn * ('cvar, 'mtype) ptrn
         | TTP of region
         | AliasP of ename binder * ('cvar, 'mtype) ptrn * region
         | AnnoP of ('cvar, 'mtype) ptrn * 'mtype outer

end
