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

local
  fun iter [] _ = true
    | iter (h::hs) asl =
        (List.exists (Formula.eq h) asl) andalso
        iter hs asl;
in
fun assumptions_contain_hypotheses (thm : Thm.t) (asl : (string * Formula.t) list) =
  iter (Thm.hyps thm) (map (fn (_,fm) => fm) asl)
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
  if Formula.is_imp A_imp_B
  then let
         val (A,B) = Formula.dest_imp(A_imp_B);
         fun jfn' (th::thms) = jfn ((Thm.disch A th)::thms);
       in
         {goals = (((label, A)::asl, B)::gls),
          justify = jfn'}
       end
  else if Formula.is_not A_imp_B
  then let
         val A = Formula.dest_not A_imp_B;
         fun jfn' (th::thms) = jfn ((Thm.disch A (Thm.not_elim th))::thms);
       in
         {goals = (((label, A)::asl, Formula.mk_falsum())::gls),
          justify = jfn'}
       end
  else raise Fail "Tactic.disch"
fun modus_ponens A {goals = (asl, B)::gls, justify=jfn} =
  let
    val A_imp_B = Formula.mk_imp(A, B);
    fun jfn' (th_A_imp_B::th_A::thms) =
      jfn ((Thm.modus_ponens th_A_imp_B th_A)::thms);
  in
    {goals = (asl, A_imp_B)::(asl, A)::gls,
     justify = jfn'}
  end;
fun mp thm {goals = (asl, B)::gls, justify=jfn} =
  if not(assumptions_contain_hypotheses thm asl)
  then raise Fail("mp: assumptions do not contain all hypotheses of theorem")
  else
    let
      val A = Thm.concl thm;
      val A_imp_B = Formula.mk_imp(A, B);
      fun jfn' (th_A_imp_B::thms) =
        jfn ((Thm.modus_ponens th_A_imp_B thm)::thms);
    in
      {goals = (asl, A_imp_B)::gls,
       justify = jfn'}
    end;
fun disj_cases thm {goals = (asl, C)::gls, justify=jfn} =
  let
    val A_or_B = Thm.concl thm;
    val (A,B) = Formula.dest_or A_or_B
                handle _ => raise Fail "Tactic.disj_cases: theorem is not a disjunction";
    val A_imp_C = Formula.mk_imp(A,C);
    val B_imp_C = Formula.mk_imp(B,C);
    fun jfn' (th_A_imp_C::th_B_imp_C::thms) =
      jfn ((Thm.modus_ponens (Thm.or_elim th_A_imp_C th_B_imp_C) thm)::thms);
  in
    {goals = (asl, A_imp_C)::(asl, B_imp_C)::gls,
     justify = jfn'}
  end;
fun or_l {goals = (asl, A_or_B)::gls, justify=jfn} =
  let
    val (A,B) = Formula.dest_or A_or_B;
    fun jfn' (th_A::thms) =
      jfn ((Thm.or_intro_r B th_A)::thms);
  in
    {goals = (asl, A)::gls,
     justify = jfn'}
  end;

fun or_r {goals = (asl, A_or_B)::gls, justify=jfn} =
  let
    val (A,B) = Formula.dest_or A_or_B;
    fun jfn' (th_B::thms) =
      jfn ((Thm.or_intro_l A th_B)::thms);
  in
    {goals = (asl, B)::gls,
     justify = jfn'}
  end;
fun contr thm {goals = (asl, A)::gls, justify=jfn} =
  if not(assumptions_contain_hypotheses thm asl)
  then raise Fail("contr: assumptions do not contain all hypotheses of theorem")
  else if not(Formula.is_falsum(Thm.concl thm))
  then raise Fail("contr: theorem is not a contradiction")
  else
    let
      fun jfn' thms =
        jfn ((Thm.contr A thm)::thms);
    in
      {goals = gls,
       justify = jfn'}
    end;
fun iff {goals = (asl, A_iff_B)::gls, justify=jfn} =
  let
    val (A,B) = Formula.dest_iff A_iff_B;
    val A_imp_B = Formula.mk_imp(A, B);
    val B_imp_A = Formula.mk_imp(B, A);
    fun jfn' (th_A_imp_B::th_B_imp_A::thms) =
      jfn((Thm.iff_intro th_A_imp_B th_B_imp_A)::thms);
  in
    { goals = (asl, A_imp_B)::(asl, B_imp_A)::gls,
      justify = jfn' }
  end;
fun gen {goals = (asl, forall_A)::gls, justify=jfn} =
  let
    val (x as (Term.Var(x0,s0)),A) = Formula.dest_forall forall_A;
    val fvs = List.concat (map (fn (_,fm) => Formula.fv fm) asl);
    val x' = Term.fresh_var x0 s0 fvs;
    fun jfn' (th_A::thms) = jfn((Thm.forall_intro x' th_A)::thms);
  in
    { goals = (asl, Formula.subst x' x A)::gls,
      justify = jfn' }
  end;

fun spec (t, x) {goals = (asl, A)::gls, justify=jfn} =
  let
    val A' = Formula.mk_forall(x, Formula.subst x t A);
    fun jfn' (thm::thms) =
      jfn((Thm.forall_elim t thm)::thms);
  in
    { goals = (asl, A')::gls,
      justify = jfn' }
  end;
(* choose : Thm.t -> Tactic.t *)
fun choose th {goals = (asl, B)::gls, justify=jfn} =
  if not(assumptions_contain_hypotheses th asl)
  then raise Fail "choose: assumptions do not contain all hypotheses of theorem"
  else
    let
      val (x as (Term.Var(x0,s)),A) = Formula.dest_exists(Thm.concl th);
      val fvs = List.concat (map (fn (_,fm) => Formula.fv fm) asl);
      val x' = Term.fresh_var x0 s fvs;
      fun jfn' (thm::thms) = jfn((Derived.exists_elim x' th thm)::thms);
    in
      { goals = (("",Formula.subst x x' A)::asl, B)::gls
      , justify = jfn' }
    end;

(* exists : Term.t -> Tactic.t *)
fun exists tm {goals = (asl, ex_A)::gls, justify=jfn} =
  let
    val (x,A) = Formula.dest_exists(ex_A);
    fun jfn' (thm::thms) = jfn((Thm.exists_intro x tm A thm)::thms);
  in
    { goals = (asl, Formula.subst tm x A)::gls
    , justify = jfn' }
  end;

end;
