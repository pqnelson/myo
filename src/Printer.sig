signature Printer = sig
  val term : Term.t -> string;
  val formula : Formula.t -> string;
  val thm : Thm.t -> string;
  val goals : ((string * Formula.t) list * Formula.t) list -> string;
end;
