structure IntOrdKey = struct
type ord_key = int
val compare = Int.compare
end

structure StringOrdKey = struct
type ord_key = string
val compare = String.compare
end
                           
structure StringBinaryMap = BinaryMapFn (StringOrdKey)
structure StringListMap = ListMapFn (StringOrdKey)
structure StringBinarySet = BinarySetFn (StringOrdKey)
structure StringListSet = ListSetFn (StringOrdKey)

functor PairOrdKeyFn (structure Fst : ORD_KEY
                      structure Snd : ORD_KEY) = struct
type ord_key = Fst.ord_key * Snd.ord_key
fun compare ((a, b), (a', b')) =
  case Fst.compare (a, a) of
      EQUAL => Snd.compare (b, b')
    | r => r
end

functor SumOrdKeyFn (structure L : ORD_KEY
                     structure R : ORD_KEY) = struct
open Util
type ord_key = (L.ord_key, R.ord_key) sum
fun compare (a, a') =
  case (a, a') of
      (inl _, inr _) => LESS
    | (inr _, inl _) => GREATER
    | (inl e, inl e') => L.compare (e, e')
    | (inr e, inr e') => R.compare (e, e')
end

