(*
Using the different reporters, we can run the tests, then
report the results.

Defaults to the JUnitTt reporter.

For inspecting per test result, VerboseTt.report may be useful
*)
structure Runner :> TestRunner = MkRunner(JUnitTt);

val tests : Test.t list = tl [
  Test.suite "" []
, DerivedSuite.suite
, ClassicalSuite.suite
];

fun main () = Runner.run tests;
