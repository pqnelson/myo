signature Thm = sig
  exception Fail of string;
  eqtype t;
  val hyps : t -> Formula.t list;
  val concl : t -> Formula.t;
  val mk_axiom : Formula.t -> t; (* danger! *)

  val assume : Formula.t -> Formula.t list -> t;
  val disch : Formula.t -> t -> t;
  val undisch : t -> t;
  val modus_ponens : t -> t -> t;
  val and_intro : t -> t -> t;
  val and_elim_l : t -> t;
  val and_elim_r : t -> t;
  val or_intro_l : Formula.t -> t -> t;
  val or_intro_r : Formula.t -> t -> t;
  val or_elim : t -> t -> t;
  val not_intro : t -> t;
  val not_elim : t -> t;
  val contr : Formula.t -> t -> t;
  val iff_intro : t -> t -> t;
  val iff_elim_l : t -> t;
  val iff_elim_r : t -> t;
  val forall_intro : Term.t -> t -> t;
  val forall_elim : Term.t -> t -> t;
  val exists_intro : Term.t -> Term.t -> Formula.t -> t -> t;
  val exists_elim : Term.t -> t -> t;

  val axiom_pair : Term.t -> Term.t -> t;
  val axiom_proj1 : Term.t -> Term.t -> t;
  val axiom_proj2 : Term.t -> Term.t -> t;
  val axiom_id : Term.t -> t;
  val axiom_const : Term.t -> Term.t -> t;
  val axiom_cond_true : Term.t -> Term.t -> Term.t -> Term.t -> t;
  val axiom_cond_false : Term.t -> Term.t -> Term.t -> Term.t -> t;
  val axiom_cond_err : Term.t -> Term.t -> Term.t -> Term.t -> t;
  val axiom_juxt : Term.t -> Term.t -> t;
  val axiom_comp : Term.t -> Term.t -> t;
  val axiom_recur_zero : Term.t -> Term.t -> t;
  val axiom_recur_base : Term.t -> Term.t -> t;
  val axiom_recur_rec : Term.t -> Term.t -> t;
  val axiom_singleton : Term.t -> Term.t -> t;
  val axiom_preimage : Term.t -> Term.t -> t;
  val axiom_union : Term.t -> Term.t -> t;
  val axiom_intersection : Term.t -> Term.t -> t;
  val axiom_induct_base : Term.t -> Term.t -> t;
  val axiom_induct_gen : Term.t -> Term.t -> t;
  val axiom_induct_min : Term.t -> Term.t -> Term.t -> t;
  val axiom_universe_ind : Term.t -> t;
  val Ind_ind : (Term.t -> Formula.t) -> t;
  val Fun_ind : (Term.t -> Formula.t) -> t;
  val Class_ind : (Term.t -> Formula.t) -> t;
  val axiom_class_comp : Formula.t -> Term.t list -> t;
  val axiom_fun_eq : Term.t -> Term.t -> t;
  val axiom_class_eq : Term.t -> Term.t -> t;
  val axiom_dec : (Term.t -> Formula.t) -> t;
  (* Database of axioms
  structure State : sig
              type t;
              val add_axiom : t -> string -> Formula.t -> t;
            end;x
   *)
end
