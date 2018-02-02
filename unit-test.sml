structure UnitTest = struct

val test_suites = []
(* val test_suites = TiML2MicroTiML.UnitTest.test_suites @ test_suites *)
(* val test_suites = MicroTiMLTypecheckUnitTest.test_suites @ test_suites *)
val test_suites = CPSUnitTest.test_suites @ test_suites

end
