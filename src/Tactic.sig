signature Tactic = sig
  exception Fail of string;
  type t = Goal.t -> Goal.t;

  val prove : Formula.t -> t list -> Thm.t;
  
  val and_intro : t;
  val and_elim_l : Formula.t -> t;
  val and_elim_r : Formula.t -> t;
  val disch : string -> t;
  val undisch : Formula.t -> t;
  val undisch_lab : string -> t;
  val modus_ponens : Formula.t -> t;
  val mp : Thm.t -> t;
  val not_intro : t;
  val not_elim : t;
  val disj_cases : Thm.t -> t;
  val or_l : t;
  val or_r : t;
  val assume : t;
  val contr : Thm.t -> t;
  val iff : t;
  val gen : t;
  val spec : (Term.t * Term.t) -> t;
  val choose : Thm.t -> t;
  val exists : Term.t -> t;
  val autolabel : t;
end;
