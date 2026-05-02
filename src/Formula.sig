signature Formula = sig
  exception Dest of string;
  type t;
  val is_atom : t -> bool;
  val mk_verum : unit -> t;
  val mk_falsum : unit -> t;
  val mk_pred : string * Term.t list -> t;
  val dest_pred : t -> string * Term.t list;
  val is_verum : t -> bool;
  val is_falsum : t -> bool;
  val is_pred : t -> bool;
  val mk_not : t -> t;
  val dest_not : t -> t;
  val is_not : t -> bool;
  val mk_and : t * t -> t;
  val mk_or : t * t -> t;
  val mk_imp : t * t -> t;
  val mk_iff : t * t -> t;

  val dest_and : t -> t * t;
  val dest_or : t -> t * t;
  val dest_imp : t -> t * t;
  val dest_iff : t -> t * t;

  val is_and : t -> bool;
  val is_or : t -> bool;
  val is_imp : t -> bool;
  val is_iff : t -> bool;
    val mk_forall : Term.t * t -> t;
    val mk_exists : Term.t * t -> t;
    
    val dest_forall : t -> Term.t * t;
    val dest_exists : t -> Term.t * t;

    val is_forall : t -> bool;
    val is_exists : t -> bool;
  val subst : Term.t -> Term.t -> t -> t;
  val fv : t -> Term.t list;
  val bv : t -> Term.t list;
  val contains_var : Term.t -> t -> bool;
  val precedence : t -> t -> order;
  val compare : t * t -> order;
  val eq : t -> t -> bool;
  val free_for : Term.t -> Term.t -> t -> bool;
  val serialize : t -> string;
  val is_e_plus : t -> bool;
  val atom_union : (t -> 'a list) -> t -> 'a list;
end;
