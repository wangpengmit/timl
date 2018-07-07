functor MapUtilFn (M : ORD_MAP) = struct

fun restrict ks m = foldl (fn (k, acc) =>
                              case M.find (m, k) of
                                  SOME v => M.insert (acc, k, v)
                                | NONE => acc
                          ) M.empty (Util.dedup (Util.isEqual o M.Key.compare) ks)

fun str_map (fk, fv) = Util.surround "{" "}" o Util.join ", " o List.map (fn (k, v) => Util.sprintf "$ => $" [fk k, fv v]) o M.listItemsi
  
fun domain m = List.map Util.fst (M.listItemsi m)

fun is_sub_domain m m' = List.all (fn k => Option.isSome (M.find (m', k))) (domain m)

fun is_same_domain m m' = M.numItems m = M.numItems m' andalso is_sub_domain m m'

fun equal eq m m' =
  if not (is_same_domain m m') then false
  else
    let
      exception NotEqual of unit
    in
      (M.appi (fn (k, v) =>
                          if eq (v, Optiona.valOf (M.find (m', k))) then
                          else raise NotEqual ()
              ) m; true)
      handle NotEqual () => false
    end
    

fun addList (m, kvs) = foldl (fn ((k, v), m) => M.insert (m, k, v)) m kvs
fun fromList kvs = addList (M.empty, kvs)

fun add_multi ((k, v), m) =
  let
    val vs = Util.default [] (M.find (m, k))
  in
    M.insert (m, k, v :: vs)
  end

fun addList_multi (m, kvs) = foldl add_multi m kvs
fun fromList_multi kvs = addList_multi (M.empty, kvs)
               
val to_map = fromList
               
fun foldli' f = M.foldli (fn (k, v, acc) => f ((k, v), acc))

fun delete (m, k) = Util.fst (M.remove (m, k)) handle NotFound => m
                        
fun enumerate c : ((M.Key.ord_key * 'value), 'result) Enum.enum = fn f => (fn init => foldli' f init c)
                                     
fun remove_many (m : 'a M.map) (ks : (M.Key.ord_key, 'a M.map) Enum.enum) : 'a M.map = ks (fn (k, m) => delete (m, k)) m

fun find_many g ks = List.mapPartial (fn k => Option.map (Util.attach_fst k) (M.find (g, k))) ks
                                         
fun single a = M.insert' (a, M.empty)
      
fun must_find m k = Util.assert_SOME (M.find (m, k))
                                       
fun sub m m' = M.filteri (fn (k, _) => Util.isNone (M.find (m', k))) m
fun union m m' = M.unionWith Util.snd (m, m')

fun all f m = List.add f (M.listItems m)
                             
end

structure IntBinaryMapUtil = MapUtilFn (IntBinaryMap)
structure StringBinaryMapUtil = MapUtilFn (StringBinaryMap)
structure IMap = IntBinaryMap
structure SMap = StringBinaryMap
structure IMapU = IntBinaryMapUtil
structure SMapU = StringBinaryMapUtil
