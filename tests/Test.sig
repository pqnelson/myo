signature Test = sig
  type t;
  structure Result : sig
              type t;
              val for_case : string -> (unit -> unit) -> t;
              val for_suite : string -> (unit -> (t list)) -> t;
              val name : t -> string;
              val msg : t -> string;
              val exn_message : t -> string;
              (* realtime excludes the time it took a TestSuite to
                 allocate infrastructure in memory. *)
              val realtime : t -> Time.time;
              val runtime : t -> Time.time;
              val results : t -> t list;
              val count_successes : t -> int;
              val count_failures : t -> int;
              val count_errors : t -> int;
              val count_total : t -> int;
              val is_success : t -> bool;
              val is_failure : t -> bool;
              val is_error : t -> bool;
              val is_case : t -> bool;
              val is_suite : t -> bool;
            end;
  val suite : string -> t list -> t;
  val mk : string -> (unit -> unit) -> t;
  val run : t -> Result.t;
end;
