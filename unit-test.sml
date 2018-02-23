structure UnitTest = struct

val test_suites = [] : (string -> unit) list
                                        
(* val test_suites = test_suites @ TiML2MicroTiML.UnitTest.test_suites *)
(* val test_suites = test_suites @ MicroTiMLTypecheckUnitTest.test_suites *)
val test_suites = test_suites @ MicroTiMLVisitor2.UnitTest.test_suites
val test_suites = test_suites @ MicroTiMLExLocallyNameless.UnitTest.test_suites
val test_suites = test_suites @ CPSUnitTest.test_suites
val test_suites = test_suites @ CC.UnitTest.test_suites

end
