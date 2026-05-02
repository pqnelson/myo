signature Unif = sig
  structure Env :
            sig
              type t;
              val undefined : unit -> t;
              val apply : t -> Term.t -> Term.t;
              val defined : t -> Term.t -> bool;
              val insert : t -> Term.t -> Term.t -> t;
            end;
  val y : Env.t -> (Term.t * Term.t) list -> Env.t;
  val y_literals : Env.t -> Formula.t * Formula.t -> Env.t;
  val y_complements : Env.t -> Formula.t * Formula.t -> Env.t;
end;
