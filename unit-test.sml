structure UnitTest = struct

val test_suites = []
(* val test_suites = TiML2MicroTiML.UnitTest.test_suites @ test_suites *)
val test_suites = MicroTiMLTypecheck.UnitTest.test_suites @ test_suites

end
