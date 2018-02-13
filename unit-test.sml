structure UnitTest = struct

val test_suites = [] : (string -> unit) list
(* val test_suites = TiML2MicroTiML.UnitTest.test_suites @ test_suites *)
(* val test_suites = MicroTiMLTypecheckUnitTest.test_suites @ test_suites *)
val test_suites = MicroTiMLVisitor2.UnitTest.test_suites @ test_suites
val test_suites = MicroTiMLExLocallyNameless.UnitTest.test_suites @ test_suites
(* val test_suites = CPSUnitTest.test_suites @ test_suites *)

end
