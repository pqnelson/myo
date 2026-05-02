structure Tactic : Tactic = struct
type t = Goal.t -> Goal.t;

local
  fun tactic_proof (g : Goal.t) pf =
    Goal.extract_thm(foldr (fn (tac, g') => tac g')
                           g
                           pf);
in
fun prove (fm : Formula.t) pf =
  tactic_proof (Goal.setup fm) pf
end;
      
(* and_intro : Goal.t -> Goal.t *)
fun and_intro {goals = ((asl, and_p_q)::gls), justify} =
  let
    val (p,q) = Formula.dest_and and_p_q;
    fun jfn' (thp::thq::ths) = justify ((Thm.and_intro thp thq)::ths);
  in
    {goals = (asl,p)::(asl,q)::gls,
     justify = jfn'}
  end;
(* and_elim_l : Formula.t -> Goal.t -> Goal.t *)
fun and_elim_l B {goals = ((asl, A)::gls), justify} =
  let
    val AB = Formula.mk_and(A, B);
    fun jfn' (thAB::ths) = justify ((Thm.and_elim_l thAB)::ths);
  in
    {goals = (asl,AB)::gls,
     justify = jfn'}
  end;
(* and_elim_r : Formula.t -> Goal.t -> Goal.t *)
fun and_elim_r A {goals = ((asl, B)::gls), justify} =
  let
    val AB = Formula.mk_and(A, B);
    fun jfn' (thAB::ths) = justify ((Thm.and_elim_r thAB)::ths);
  in
    {goals = (asl,AB)::gls,
     justify = jfn'}
  end;
fun disch (label : string) {goals = (asl, A_imp_B)::gls,
                            justify = jfn} =
  let
    val (A,B) = Formula.dest_imp(A_imp_B);
    fun jfn' (th::thms) = jfn ((Thm.disch A th)::thms);
  in
    {goals = (((label, A)::asl, B)::gls),
     justify = jfn'}
  end;
fun modus_ponens A {goals = (asl, B)::gls, justify=jfn} =
  let
    val A_imp_B = Formula.mk_imp(A, B);
    fun jfn' (th_A_imp_B::th_A::thms) =
      jfn ((Thm.modus_ponens th_A_imp_B th_A)::thms);
  in
    {goals = (asl, A_imp_B)::(asl, A)::gls,
     justify = jfn'}
  end;

end;
