(*
Using any test reporter, we can run the tests, then
report the results.
*)
functor MkRunner(Reporter : Reporter) :> TestRunner = struct
  fun run tests =
    let
      val results = map Test.run tests;
    in
      Reporter.report_all results;
      ()
    end;
end;
