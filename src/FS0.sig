signature FS0 = sig
  exception Dest of string;
  (* individuals *)
  val zero : Term.t;
  val pair : Term.t -> Term.t -> Term.t;
  val app : Term.t -> Term.t -> Term.t;

  val dest_app : Term.t -> Term.t * Term.t;
  val dest_pair : Term.t -> Term.t * Term.t;

  (* functions *)
  val id_const : Term.t;
  val id : Term.t -> Term.t;
  val mk_id : Term.t -> Term.t;
  val if_eq_const : Term.t;
  val mk_if_eq : Term.t -> Term.t;
  val if_eq : Term.t -> Term.t;
  val proj1_const : Term.t;
  val mk_proj1 : Term.t -> Term.t;
  val proj1 : Term.t -> Term.t;
  val proj2_const : Term.t;
  val mk_proj2 : Term.t -> Term.t;
  val proj2 : Term.t -> Term.t;
  val const : Term.t -> Term.t;
  val dest_const : Term.t -> Term.t;
  val comp : Term.t -> Term.t -> Term.t;
  val dest_comp : Term.t -> Term.t * Term.t;
  val juxt : Term.t -> Term.t -> Term.t;
  val dest_juxt : Term.t -> Term.t * Term.t;
  val recur : Term.t -> Term.t -> Term.t;
  val dest_recur : Term.t -> Term.t * Term.t;

  (* classes *)
  val singleton : Term.t -> Term.t;
  val dest_singleton : Term.t -> Term.t;
  val preimage : Term.t -> Term.t -> Term.t;
  val dest_preimage : Term.t -> Term.t * Term.t;
  val union : Term.t -> Term.t -> Term.t;
  val dest_union : Term.t -> Term.t * Term.t;
  val intersection : Term.t -> Term.t -> Term.t;
  val dest_intersection : Term.t -> Term.t * Term.t;
  val induct : Term.t -> Term.t -> Term.t;
  val dest_induct : Term.t -> Term.t * Term.t;

  (* predicates *)
  val not_equal : Term.t -> Term.t -> Formula.t;
  val In : Term.t -> Term.t -> Formula.t;
  val dest_in : Formula.t -> Term.t * Term.t;
  val equal : Term.t -> Term.t -> Formula.t;
  val dest_equal : Formula.t -> Term.t * Term.t;
end;
