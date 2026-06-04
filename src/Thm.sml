structure Thm :> Thm = struct
exception Fail of string;

infix |-;
datatype t = |- of (Formula.t list) * Formula.t;

fun hyps (Gamma |- _) = Gamma;

fun concl (_ |- phi) = phi;

fun mk_axiom phi = ([] |- phi); 

infix @@
fun [] @@ ys = ys
  | xs @@ [] = xs
  | xs @@ ys = xs @ ys;

fun remove phi Gamma =
  List.filter (not o (Formula.eq phi)) Gamma;
fun assume phi Gamma = (phi::Gamma) |- phi;

fun disch phi (Gamma |- psi) = (remove phi Gamma) |- Formula.mk_imp(phi,psi);

fun undisch (Gamma |- A) =
  if not(Formula.is_imp A)
  then raise Fail "Thm.undisch: conclusion must be an implication"
  else let val (phi,psi) = Formula.dest_imp A
       in (phi::Gamma) |- psi end;

fun modus_ponens (Gamma1 |- imp) (Gamma2 |- phi) =
  if not(Formula.is_imp imp)
  then raise Fail("modus_ponens: major premise ("^
                  (Formula.serialize imp)^
                  ") expected implication")
  else let
    val (A, B) = Formula.dest_imp imp
  in
    if not(Formula.eq A phi)
    then raise Fail "modus_ponens: premise does not match argument"
    else (Gamma1 @@ Gamma2) |- B
  end;
fun and_intro (Gamma1 |- phi) (Gamma2 |- psi) =
  (Gamma1 @@ Gamma2) |- Formula.mk_and(phi, psi);

fun and_elim_l (Gamma |- phi) =
  if not(Formula.is_and phi)
  then raise Fail "and_elim_l: expects conjunction"
  else
    let val (A,B) = Formula.dest_and phi
    in Gamma |- A end;

fun and_elim_r (Gamma |- phi) =
  if not(Formula.is_and phi)
  then raise Fail "and_elim_r: expects conjunction"
  else
    let val (A,B) = Formula.dest_and phi
    in Gamma |- B end;
fun or_intro_l A (Gamma |- B) = (Gamma |- Formula.mk_or(A, B))

fun or_intro_r B (Gamma |- A) = (Gamma |- Formula.mk_or(A, B))

fun or_elim (Gamma1 |- A_imp_C) (Gamma2 |- B_imp_C) =
  if not(Formula.is_imp A_imp_C)
  then raise Fail "or_elim: first theorem must be an implication"
  else if not(Formula.is_imp B_imp_C)
  then raise Fail "or_elim: second theorem must be an implication"
  else
    let
      val (A,C1) = Formula.dest_imp A_imp_C;
      val (B,C2) = Formula.dest_imp B_imp_C;
      val A_or_B_imp_C = Formula.mk_imp(Formula.mk_or(A, B), C1);
    in
      if not(Formula.eq C1 C2)
      then raise Fail "or_elim: conclusions of theorems disagree"
      else (Gamma1 @@ Gamma2) |- A_or_B_imp_C
    end;
fun not_intro (Gamma |- phi_imp_false) =
  if not(Formula.is_imp phi_imp_false)
  then raise Fail "not_intro: theorem is not an implication"
  else let
    val (phi, F) = Formula.dest_imp phi_imp_false;
  in
    if not(Formula.is_falsum F)
    then raise Fail "not_intro: theorem is not 'implies falsum'"
    else Gamma |- Formula.mk_not(phi)
  end;

fun not_elim (Gamma |- not_phi) =
  if not(Formula.is_not not_phi)
  then raise Fail("not_elim: theorem ("^
                  (Formula.serialize not_phi)^
                  ") is not a negation")
  else let
    val (phi) = Formula.dest_not not_phi;
  in
    Gamma |- Formula.mk_imp(phi, Formula.mk_falsum())
  end;
fun contr phi (Gamma |- falsum) =
  if not(Formula.is_falsum falsum)
  then raise Fail "contr: theorem is not falsum"
  else Gamma |- phi;
fun iff_intro (Gamma1 |- A_imp_B) (Gamma2 |- B_imp_A) =
  if not(Formula.is_imp A_imp_B)
  then raise Fail "iff_intro: first theorem is not an implication"
  else if not(Formula.is_imp B_imp_A)
  then raise Fail "iff_intro: second theorem is not an implication"
  else let
    val (A1,B1) = Formula.dest_imp(A_imp_B);
    val (B2,A2) = Formula.dest_imp(B_imp_A);
  in
    if not(Formula.eq A1 A2)
    then raise Fail("iff_intro: premise of first theorem ("^
                    (Formula.serialize A1)^
                    ") is not conclusion of second theorem ("^
                    (Formula.serialize A2)^
                    ")")
    else if not(Formula.eq B1 B2)
    then raise Fail("iff_intro: premise of second theorem ("^
                    (Formula.serialize B2)
                    ^") is not conclusion of first theorem ("^
                    (Formula.serialize B1)
                    ^")")
    else (Gamma1 @@ Gamma2) |- Formula.mk_iff(A1,B2)
  end;

fun iff_elim_l (Gamma |- A_iff_B) =
  if not(Formula.is_iff A_iff_B)
  then raise Fail "iff_elim_l: theorem is not an iff"
  else
    let val (A,B) = Formula.dest_iff A_iff_B
    in Gamma |- Formula.mk_imp(A,B) end;

fun iff_elim_r (Gamma |- A_iff_B) =
  if not(Formula.is_iff A_iff_B)
  then raise Fail "iff_elim_r: theorem is not an iff"
  else
    let val (A,B) = Formula.dest_iff A_iff_B
    in Gamma |- Formula.mk_imp(B,A) end;
fun forall_intro (x : Term.t) (Gamma |- phi) =
  if not(Term.is_var x)
  then raise Fail "forall_intro: x is not a variable"
  else let fun free_in fm = List.exists (Term.eq x) (Formula.fv fm);
       in if List.exists free_in Gamma
          then raise Fail "forall_intro: x is free in hypotheses"
          else Gamma |- (Formula.mk_forall(x, phi))
       end;
fun forall_elim (t : Term.t) (Gamma |- forall_phi) =
  if not(Formula.is_forall forall_phi)
  then raise Fail "forall_elim: theorem is not universally quantified"
  else let val (x,phi) = Formula.dest_forall forall_phi
       in if not(Formula.free_for t x phi)
          then raise Fail "forall_elim: term is not free for conclusion"
          else Gamma |- (Formula.subst x t phi)
       end;
fun exists_intro (x : Term.t) (t : Term.t) (phi : Formula.t) (Gamma |- phi_t) =
  if not(Term.is_var(x))
  then raise Fail "exists_intro: x is not a variable"
  else if not(Term.have_same_sort x t)
  then raise Fail "exists_intro: x and t of different sorts"
  else if not(Formula.eq (Formula.subst x t phi) phi_t)
  then (if List.exists (Term.eq x) (Formula.bv phi)
        then raise Fail (
            concat["exists_intro: conclusion mismatch supplied formula ",
                   "(probably x is a bound variable with 't' in its scope)"])
        else raise Fail("exists_intro: conclusion "^
                        (Formula.serialize phi_t)^
                        " mismatch supplied formula "^
                        (Formula.serialize (Formula.subst x t phi))))
  else if not(Formula.free_for t x phi)
  then raise Fail "exists_intro: term is not free for var in formula"
  else Gamma |- (Formula.mk_exists(x, phi))
fun exists_elim (x : Term.t) (Gamma |- A_imp_B) =
  if not(Term.is_var x)
  then raise Fail "exists_elim: x is not a variable"
  else if not(Formula.is_imp A_imp_B)
  then raise Fail "exists_elim: theorem is not an implication"
  else let val (A,B) = Formula.dest_imp A_imp_B;
           fun free_in fm = List.exists (fn y => Term.eq x y) (Formula.fv fm);
       in if free_in B
          then raise Fail "exists_elim: x is free in conclusion of theorem"
          else if List.exists free_in Gamma
          then raise Fail "exists_elim: x is free in hypotheses"
          else Gamma |- (Formula.mk_imp(Formula.mk_exists(x, A), B))
       end;

fun axiom_pair x1 x2 =
  mk_axiom(FS0.not_equal (FS0.pair x1 x2) FS0.zero);

fun axiom_proj1 x1 x2 =
  mk_axiom(FS0.equal (FS0.mk_proj1 (FS0.pair x1 x2)) x1);

fun axiom_proj2 x1 x2 =
  mk_axiom(FS0.equal (FS0.mk_proj2 (FS0.pair x1 x2)) x2);
fun axiom_id x = mk_axiom(FS0.equal (FS0.mk_id x) x);

fun axiom_const a x = mk_axiom(FS0.equal (FS0.app (FS0.const a) x) a);

local
  fun quad x1 x2 y1 y2 = FS0.pair x1 (FS0.pair x2 (FS0.pair y1 y2));
in
fun axiom_cond_true x1 x2 y1 y2 =
  mk_axiom(Formula.mk_imp(FS0.equal x1 x2,
                              FS0.equal (FS0.mk_if_eq (quad x1 x2 y1 y2))
                                        y1));
fun axiom_cond_false x1 x2 y1 y2 =
  mk_axiom(Formula.mk_imp(FS0.not_equal x1 x2,
                              FS0.equal (FS0.mk_if_eq (quad x1 x2 y1 y2))
                                        y2));

fun axiom_cond_err x1 x2 y1 y2 =
  let
    val u = Term.fresh_var "u" Sort.IND ((Term.fv x1) @
                                         (Term.fv x2) @
                                         (Term.fv y1) @
                                         (Term.fv y2));
    val ex = List.foldr Formula.mk_exists
                        (FS0.equal u (quad x1 x2 y1 y2))
                        [x1,x2,y1,y2];
  in
    mk_axiom(Formula.mk_imp(Formula.mk_not(ex),
                            FS0.equal (FS0.mk_if_eq u)
                                      FS0.zero))
  end;
end;
fun axiom_juxt f g =
  let val x = Term.fresh_var "x" Sort.IND ((Term.fv f) @ (Term.fv g))
  in mk_axiom(Formula.mk_forall(x, FS0.equal (FS0.app (FS0.juxt f g) x)
                                             (FS0.pair (FS0.app f x)
                                                       (FS0.app g x))))
  end;

fun axiom_comp f g =
  let val x = Term.fresh_var "x" Sort.IND ((Term.fv f) @ (Term.fv g))
  in mk_axiom(Formula.mk_forall(x, FS0.equal (FS0.app (FS0.comp f g) x)
                                             (FS0.app f (FS0.app g x))))
  end;
fun axiom_recur_zero f g =
  mk_axiom(FS0.equal (FS0.app (FS0.recur f g) FS0.zero)
                     FS0.zero);

fun axiom_recur_base f g =
  let val x = Term.fresh_var "x" Sort.IND ((Term.fv f) @ (Term.fv g))
  in mk_axiom(Formula.mk_forall(x,
                                FS0.equal (FS0.app (FS0.recur f g)
                                                   (FS0.pair x FS0.zero))
                                          (FS0.app f x)))
  end;

fun axiom_recur_rec f g =
  let
    val vars = (Term.fv f) @ (Term.fv g);
    fun var x = Term.fresh_var x Sort.IND vars;
    val x = var "x";
    val y = var "y";
    val z = var "z";
    fun h x1 x2 = FS0.app (FS0.recur f g) (FS0.pair x1 x2);
    val lhs = h x (FS0.pair y z);
    val args = List.foldr (fn (a,b) => FS0.pair a b)
                          (h x z)
                          [x, y, z, (h x y)];
    val rhs = FS0.app g args;
    val eq = FS0.equal lhs rhs;
  in
    mk_axiom(List.foldr Formula.mk_forall eq [x,y,z])
  end;
fun axiom_singleton obj elt =
  mk_axiom(Formula.mk_iff(FS0.In obj (FS0.singleton elt),
                          FS0.equal obj elt));

fun axiom_preimage f C =
  let val x = Term.fresh_var "x" Sort.IND ((Term.fv f) @ (Term.fv C))
  in mk_axiom(Formula.mk_iff(FS0.In x (FS0.preimage f C),
                             FS0.In (FS0.app f x) C))
  end;

fun axiom_union A B =
  let val x = Term.fresh_var "x" Sort.IND ((Term.fv A) @ (Term.fv B))
  in mk_axiom(Formula.mk_iff(FS0.In x (FS0.union A B),
                             Formula.mk_or(FS0.In x A,
                                           FS0.In x B)))
  end;

fun axiom_intersection A B =
  let val x = Term.fresh_var "x" Sort.IND ((Term.fv A) @ (Term.fv B))
  in mk_axiom(Formula.mk_iff(FS0.In x (FS0.intersection A B),
                             Formula.mk_and(FS0.In x A,
                                            FS0.In x B)))
  end;
fun axiom_induct_base A B =
  let val x = Term.fresh_var "x" Sort.IND ((Term.fv A) @ (Term.fv B))
  in mk_axiom(Formula.mk_forall(x, Formula.mk_imp(FS0.In x A,
                                                  FS0.In x (FS0.induct A B))))
  end;

fun axiom_induct_gen A B =
  let
    val vars = ((Term.fv A) @ (Term.fv B));
    fun var x = Term.fresh_var x Sort.IND vars;
    val x = var "x";
    val y = var "y";
    val z = var "z";
    val C = FS0.induct A B;
    val triple = FS0.pair x (FS0.pair y z);
    val p1 = FS0.In y C;
    val p2 = FS0.In z C;
    val p3 = FS0.In triple B;
    val p4 = FS0.In x C;
    val premises = List.foldr Formula.mk_and p3 [p1, p2];
    val claim = Formula.mk_imp(premises, p4);
  in
    mk_axiom(List.foldr Formula.mk_forall claim [x,y,z])
  end;

fun axiom_induct_min A B X =
  let
    val vars = ((Term.fv A) @ (Term.fv B));
    fun var x = Term.fresh_var x Sort.IND vars;
    val x = var "x";
    val y = var "y";
    val z = var "z";
    val p0 = Formula.mk_forall(x, Formula.mk_imp(FS0.In x A,
                                                 FS0.In x X));
    val C = FS0.induct A B;
    val triple = FS0.pair x (FS0.pair y z);
    val p1 = FS0.In y X;
    val p2 = FS0.In z X;
    val p3 = FS0.In triple B;
    val p4 = FS0.In x X;
    val premises = List.foldr Formula.mk_and p3 [p1, p2];
    val claim = Formula.mk_imp(premises, p4);
    val ind_case = List.foldr Formula.mk_forall claim [x,y,z];
    val conc = Formula.mk_forall(x, Formula.mk_imp(FS0.In x C,
                                                   FS0.In x X));
  in
    mk_axiom(Formula.mk_imp(Formula.mk_and(p0,ind_case),
                            conc))
  end;
fun axiom_universe_ind X =
  let
    val vars = (Term.fv X);
    fun var x = Term.fresh_var x Sort.IND vars;
    val x = var "x";
    val y = var "y";
    val p0 = FS0.In (FS0.zero) X;
    val claim = Formula.mk_imp(Formula.mk_and(FS0.In x X,
                                              FS0.In y X),
                               FS0.In (FS0.pair x y) X);
    val p1 = List.foldr Formula.mk_forall claim [x,y];
    val conc = Formula.mk_forall(x, FS0.In x X);
  in
    mk_axiom(Formula.mk_imp(Formula.mk_and(p0, p1),
                            conc))
  end;
fun fresh_var_in (x : string) (s : Sort.t) (fm : Formula.t) =
  let
    fun tm_ident (tm as (Term.Var _)) = [tm]
      | tm_ident (Term.Fun(f,s0,args)) =
          (Term.Var(f,s0))::(List.concat(map tm_ident args));
    fun fm_ident (P : Formula.t) =
      if Formula.is_pred P
      then let val (P0,args) = Formula.dest_pred P
           in (Term.Var(P0,Sort.IND))::(List.concat(map tm_ident args)) end
      else [];
    val vars = fm_ident fm;
  in
    Term.fresh_var x s vars
  end;

(* Ind_ind : (Term.t -> Formula.t) -> Thm.t *)
fun Ind_ind P = 
  let
    val tmp = Term.Var("_", Sort.IND);
    val x = fresh_var_in "x" Sort.IND (P tmp);
    val y = fresh_var_in "y" Sort.IND (P x);
    val f = fresh_var_in "f" Sort.FUN (P x);
    val base = P (FS0.zero);
    val pair = Formula.mk_forall(x, Formula.mk_forall(y, Formula.mk_imp(Formula.mk_and(P x, P y),
                                                                        P (FS0.pair x y))));
    val app = Formula.mk_forall(f, Formula.mk_forall(x,
                                                     Formula.mk_imp(P x,
                                                                    P(FS0.app f x))));
    val hypo = Formula.mk_and(base, Formula.mk_and(pair,
                                                   app));
    val conc = Formula.mk_forall(x, P x);
  in
    mk_axiom(Formula.mk_imp(hypo,
                            conc))
  end;
(* Fun_ind : (Term.t -> Formula.t) -> t *)
fun Fun_ind P =
  let
    val tmp = Term.Var("_", Sort.FUN);
    val a = fresh_var_in "a" Sort.IND (P tmp);
    val f = fresh_var_in "f" Sort.FUN (P tmp);
    val g = fresh_var_in "g" Sort.FUN (P tmp);
    fun ind_case (con : Term.t -> Term.t -> Term.t) =
      Formula.mk_forall(f, Formula.mk_forall(g, Formula.mk_imp(Formula.mk_and(P f,
                                                                              P g),
                                                               P(con f g))));
    val premises =
      List.foldr Formula.mk_and
                 (ind_case FS0.recur)
                 [P (FS0.id_const),
                  P (FS0.proj1_const),
                  P (FS0.proj2_const),
                  Formula.mk_forall(a, P (FS0.const a)),
                  ind_case (FS0.comp),
                  ind_case (FS0.juxt)];
    val conc = Formula.mk_forall(f, P f);
  in
    mk_axiom(Formula.mk_imp(premises,
                            conc))
  end;  
(* Class_ind : (Term.t -> Formula.t) -> Thm.t *)
fun Class_ind P =
  let
    val tmp = Term.Var("_", Sort.CLASS);
    val a = fresh_var_in "a" Sort.IND (P tmp);
    val f = fresh_var_in "f" Sort.FUN (P tmp);
    val A = fresh_var_in "A" Sort.CLASS (P tmp);
    val B = fresh_var_in "B" Sort.CLASS (P tmp);
    fun ind_case (con : Term.t -> Term.t -> Term.t) =
      Formula.mk_forall(A, Formula.mk_forall(B, Formula.mk_imp(Formula.mk_and(P A,
                                                                              P B),
                                                               P(con A B))));
    val premises =
      List.foldr Formula.mk_and
                 (ind_case (FS0.induct))
                 [P (FS0.singleton (FS0.zero)),
                  Formula.mk_forall(f, Formula.mk_forall(A, Formula.mk_imp(P A,
                                                                           P (FS0.preimage f A)))),
                  ind_case (FS0.union),
                  ind_case (FS0.intersection)];
    val conc = Formula.mk_forall(A, P A);
  in
    mk_axiom(Formula.mk_imp(premises, conc))
  end;
(* axiom_class_comp : Formula.t -> Term.t list -> Thm.t *)
fun axiom_class_comp (P : Formula.t) ([] : Term.t list) =
      raise Fail "axiom_class_comp: variable list is empty"
  | axiom_class_comp P ((vars as (h::hs)) : Term.t list) =
      let
        fun not_in_vars y = List.all (not o (Term.eq y)) vars;
        val xs : Term.t = List.foldl (fn (x,acc) => FS0.pair acc x)
                                     h
                                     hs;
        val S = Term.Fun("S_{("^
                         (String.concatWith "," (map (fn (Term.Var(x,_)) => x)
                                                     vars))
                         ^")|"^(Formula.serialize P)^"}",
                         Sort.CLASS,
                         []);
      in
        if not(Formula.is_e_plus P)
        then raise Fail("axiom_class_comp: formula is not E+")
        else if List.exists not_in_vars (Formula.fv P)
        then raise Fail("axiom_class_comp: not all free variables of predicate "^
                        "contained in given list of variables")
        else if List.exists (not o Term.is_var) vars
        then raise Fail "axiom_class_comp: given list of variables contains a function"
        else if List.exists (not o Term.is_ind) vars
        then raise Fail "axiom_class_comp: given list of variables not all individual-sorted"
        else mk_axiom(List.foldr Formula.mk_forall
                                 (Formula.mk_iff (FS0.In xs S,
                                                  P))
                                 vars)
      end;
(* axiom_fun_eq : Term.t -> Term.t -> Thm.t *)
fun axiom_fun_eq lhs rhs =
  if not(Term.is_fun lhs)
  then raise Fail "axiom_fun_eq: left-hand side is not a function"
  else if not(Term.is_fun rhs)
  then raise Fail "axiom_fun_eq: right-hand side is not a function"
  else let val vars = (Term.fv lhs) @ (Term.fv rhs);
           val x = Term.fresh_var "x" Sort.IND vars;
           val iff = Formula.mk_iff;
           val forall = Formula.mk_forall;
       in mk_axiom(iff(forall(x, FS0.equal (FS0.app lhs x)
                                           (FS0.app rhs x)),
                       FS0.equal lhs rhs))
       end;
(* axiom_class_eq : Term.t -> Term.t -> Thm.t *)
fun axiom_class_eq lhs rhs =
  if not(Term.is_class lhs)
  then raise Fail "axiom_class_eq: left-hand side is not a class"
  else if not(Term.is_class rhs)
  then raise Fail "axiom_class_eq: right-hand side is not a class"
  else let val vars = (Term.fv lhs) @ (Term.fv rhs);
           val x = Term.fresh_var "x" Sort.IND vars;
           val iff = Formula.mk_iff;
           val forall = Formula.mk_forall;
       in mk_axiom(iff(forall(x, Formula.mk_iff (FS0.In x lhs,
                                                 FS0.In x rhs)),
                       (FS0.equal lhs rhs)))
       end;
(* axiom_dec : (Term.t -> Formula.t) -> Thm.t *)
fun axiom_dec P =
  let
    val x0 = Term.Var("x0", Sort.IND);
    val vars = (Formula.fv (P x0)) @ (Formula.bv (P x0));
    val x = Term.fresh_var "x" Sort.IND vars;
    val f = Term.fresh_var "f" Sort.FUN vars;
    val premise = Formula.mk_iff(FS0.equal (FS0.app f x)
                                           FS0.zero,
                                P x);
  in
    mk_axiom(Formula.mk_imp(Formula.mk_exists(f, Formula.mk_forall(x, premise)),
                            Formula.mk_forall(x,
                                              Formula.mk_or((P x),
                                                            Formula.mk_not(P x)))))
  end;
end;
