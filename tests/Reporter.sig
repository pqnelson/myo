signature Reporter = sig
  val report : Test.Result.t -> unit;
  val report_all : Test.Result.t list -> unit;
end;
