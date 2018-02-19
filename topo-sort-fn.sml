functor TopoSortFn (structure M : ORD_MAP
                    structure S : ORD_SET
                                    sharing type M.Key.ord_key = S.item
                   ) =
struct

structure SU = SetUtilFn (S)
structure MU = MapUtilFn (M)

open Util

infixr 0 $

exception TopoSortFailed
            
fun topo_sort in_graph =
  let
    fun find_empty_nodes g = M.foldli (fn (k, v, acc) => if S.isEmpty v then S.add (acc, k) else acc) S.empty g
    fun loop (in_graph, done) =
      if M.numItems in_graph <= 0 then
        done
      else
        let
          val nodes = find_empty_nodes in_graph
          val () = if S.isEmpty nodes then raise TopoSortFailed else ()
          val in_graph : S.set M.map = MU.remove_many in_graph $ SU.enumerate nodes
          val in_graph = M.map (fn s => S.difference (s, nodes)) in_graph
        in
          loop (in_graph, SU.to_list nodes @ done)
        end
    val ret = rev $ loop (in_graph, [])
    val () = assert (fn () => length ret = M.numItems in_graph) "length ret = M.length in_graph"
  in
    ret
  end

end
