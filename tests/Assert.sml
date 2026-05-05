structure Assert = struct
exception Fail of string;

(* that : bool -> string -> unit *)
fun that cond msg =
  if cond then ()
  else raise Fail msg;

(* eq : ''a -> ''a -> string -> unit *)
fun eq expected actual msg =
  that (expected = actual) msg;
end;
