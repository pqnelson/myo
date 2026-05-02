signature Tactic = sig
  type t = Goal.t -> Goal.t;

  val prove : Formula.t -> t list -> Thm.t;
  
    val and_intro : t;
    val and_elim_l : Formula.t -> t;
    val and_elim_r : Formula.t -> t;
    val disch : string -> t;
    val modus_ponens : Formula.t -> t;
end;
