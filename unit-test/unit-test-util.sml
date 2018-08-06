structure UnitTestUtil = struct

open Util

infixr 0 $
         
val success = OS.Process.success
val failure = OS.Process.failure

exception Failed of string
                      
fun fail msg = raise Failed msg
fun assert name p = if p then () else fail $ sprintf "assert $ failed" [name]

val foo = at_most_one_some_other_true
            (fn n => if n mod 2 = 0 then SOME (n div 2) else NONE)
            (fn n => n = 1 )
val test_cases =
    [
      ("at_most_one_some_other_true/1",
       fn () =>
          let
            val ls = [1, 6, 1, 1]
          in
            case foo ls of
                inl (p, a) => (assert "1" $ p = 1;
                               assert "2" $ a = 3)
              | _ => fail "should be inl"
          end
      ),
      ("at_most_one_some_other_true/2",
       fn () =>
          let
            val ls = [1, 1, 1, 1]
          in
            case foo ls of
                inr true => ()
              | _ => fail "should be: inr true"
          end
      ),
      ("at_most_one_some_other_true/3",
       fn () =>
          let
            val ls = [1, 6, 1, 2]
          in
            case foo ls of
                inr false => ()
              | _ => fail "should be: inr false"
          end
      ),
      ("at_most_one_some_other_true/4",
       fn () =>
          let
            val ls = [1, 1, 1, 3]
          in
            case foo ls of
                inr false => ()
              | _ => fail "should be: inr false"
          end
      ),
      ("at_most_one_some_other_true/5",
       fn () =>
          let
            val ls = [6, 1, 3, 1]
          in
            case foo ls of
                inr false => ()
              | _ => fail "should be: inr false"
          end
      )
    ]
      
fun main (prog_name, args : string list) =
  let
    val suite_name = "Util"
    val () = println "=========================================="
    val () = println $ "Start test suite: " ^ suite_name
    fun do_test_case (case_name, f) =
      let
        val () = println "------------------------------------------"
        val () = println $ "Start test case: " ^ case_name
        val () = f ()
        val () = println $ "Passed test case: " ^ case_name
      in
        ()
      end
    val () = app do_test_case test_cases
    val () = println $ "Passed test suite: " ^ suite_name
  in
    success
  end
  handle
  Failed msg =>
  (println msg;
   failure)

end

val ret = UnitTestUtil.main (CommandLine.name (), CommandLine.arguments ())

val () = OS.Process.exit ret
                         
