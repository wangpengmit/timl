structure ContUtil = struct

fun callret (f : ('a -> unit) -> 'a) : 'a = Cont.callcc (fn k => f (fn v => Cont.throw k v))
                                
end
