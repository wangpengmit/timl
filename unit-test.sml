structure UnitTest = struct

val test_suites = [] : (string -> unit) list
                                        
val test_suites = test_suites @ MicroTiMLVisitor2.UnitTest.test_suites
val test_suites = test_suites @ MicroTiMLLocallyNameless.UnitTest.test_suites
                                  
val test_suites = test_suites @ TiML2MicroTiML.UnitTest.test_suites
val test_suites = test_suites @ MicroTiMLTypecheck.UnitTest.test_suites
val test_suites = test_suites @ CPS.UnitTest.test_suites
val test_suites = test_suites @ CC.UnitTest.test_suites
(* val test_suites = test_suites @ PairAlloc.UnitTest.test_suites *)
(* val test_suites = test_suites @ CodeGen.UnitTest.test_suites *)
val test_suites = test_suites @ ToEVM1.UnitTest.test_suites

end
