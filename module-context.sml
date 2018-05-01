structure Gctx = struct
open Util
structure Map = UniqueMapFn (StringBinaryMap)
(* structure Map = StringListMap *)
(* structure Map = StringListPairMap *)
structure MapUtil = MapUtilFn (Map)
open MapUtil
open Map
       
fun nth_error2 m k = Option.map (fn v => (k, v)) (curry find m k)
val length = numItems
fun add kv m = curry insert' kv m
               
end

