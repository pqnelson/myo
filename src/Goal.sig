signature Goal = sig
  exception Unsolved of string;
  exception Mismatch of string;
  
  type t = { goals : ((string * Formula.t) list * Formula.t) list
           , justify : Thm.t list -> Thm.t };

  val subgoals : t -> ((string * Formula.t) list * Formula.t) list;
  val justify : t -> Thm.t list -> Thm.t;
  val to_string : t -> string;
  val setup : Formula.t -> t;
  val extract_thm : t -> Thm.t;
end;
