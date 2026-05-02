signature Classical = sig
  val nnf : Formula.t -> Formula.t;
  val askolemize : Formula.t -> Formula.t;
  val tab : Formula.t -> int -> int;
end;
