(* 
Print to the terminal (hence the "-Tt" suffix) a summary of test
results in the style of JUnit.

If any failures or errors occur, print those out with a bit more
detail.
*)
structure JUnitTt :> Reporter = struct
structure Result = Test.Result;

fun interval_to_string (dt : Time.time) =
  (LargeInt.toString (Time.toMicroseconds dt))^"ms";

fun report_iter p =
  let
    fun path "" s = s
      | path p s = p^"."^s; 
    fun for_case c =
      if Result.is_failure c
      then concat [path p (Result.name c),
                   " FAIL: ",
                   Result.msg c,
                   "\n"]
      else if Result.is_error c
      then concat [path p (Result.name c),
                   " ERROR: ",
                   (Result.exn_message c),
                   "\n"]
      else "";
    fun for_suite result =
      let
        val p2 = path p (Result.name result);
        val rs = Test.Result.results result;
      in
        concat ["Running ", p2, "\n",
                concat (map (report_iter p2) rs),
                "Tests run: ",
                Int.toString(Result.count_total result),
                ", Failures: ",
                Int.toString(Result.count_failures result),
                ", Errors: ",
                Int.toString(Result.count_errors result),
                ", Time elapsed: ",
                interval_to_string (Result.realtime result),
                " - in ",
                (Result.name result), "\n"]
      end;
  in
    fn r => if Test.Result.is_case r then for_case r
            else for_suite r
  end;

val report = print o (report_iter "");

val report_all = app report;
end;
