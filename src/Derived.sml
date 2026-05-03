structure Derived = struct
fun weaken Gamma th1 =
  let
    val th2 = Thm.assume (Thm.concl th1) Gamma;
    val th3 = Thm.disch (Thm.concl th1) th2;
  in
    Thm.modus_ponens th2 th1
  end;

fun hypo_syll thm1 thm2 =
  let
    val (A,B) = Formula.dest_imp(Thm.concl thm1)
                handle (Formula.Dest _) =>
                       raise Fail "hypo_syll: first theorem is not an implication";
    val th2 = Thm.modus_ponens thm2 (Thm.undisch thm1)
              handle (Thm.Fail _) =>
                     raise Fail "hypo_syll: conclusion of first theorem mismatches premise of second theorem";
  in
    Thm.disch A th2
  end;

fun weak_not_elim A B =
  let
    val not_A = Formula.mk_not A;
    val th1 = Thm.assume A [not_A];     (* A, not A |- A *)
    val th2 = Thm.assume not_A [A];     (* A, not A |- not A *)
    val th3 = Thm.not_elim th2;         (* A, not A |- A implies false *)
    val th4 = Thm.modus_ponens th3 th1; (* A, not A |- false *)
    val th5 = Thm.contr B th4;          (* A, not A |- B *)
    val th6 = Thm.disch not_A th5;      (* A |- not A implies B *)
  in
    Thm.disch A th6
  end;

fun absurdum A B =
  let
    val not_B = Formula.mk_not B;
    val A_imp_B = Formula.mk_imp(A, B);
    val A_imp_not_B = Formula.mk_imp(A, not_B);
    val th1 = Thm.assume A_imp_B [A_imp_not_B]; (* A => B, A => not B |- A => B *)
    val th2 = Thm.undisch th1;                  (* A, A => B, A => not B |- B *)
    val th3 = Thm.assume A_imp_not_B [A_imp_B]; (* A => B, A => not B |- A => not B *)
    val th4 = Thm.undisch th3;                  (* A, A => B, A => not B |- not B *)
    val th5 = Thm.not_elim th4;                 (* A, A => B, A => not B |- B => false *)
    val th6 = Thm.disch A (Thm.modus_ponens th5 th2); (* A => B, A => not B |- A => false *)
    val th7 = Thm.not_intro th6;                (* A => B, A => not B |- not A *)
    val th8 = Thm.disch A_imp_not_B th7;        (* A => B |- (A => not B) => not A *)
  in
    Thm.disch A_imp_B th8
  end;
fun or_idem A =
  let
    val th1 = Thm.assume A [];
    val th2 = Thm.disch A th1;
  in
    Thm.or_elim th2 th2
  end;

fun or_comm A B =
  let
    val th1 = Thm.assume A [];
    val th2 = Thm.or_intro_l B th1;
    val th3 = Thm.disch A th2;
    val th4 = Thm.assume B [];
    val th5 = Thm.or_intro_r A th4;
    val th6 = Thm.disch B th5;
  in
    Thm.or_elim th3 th6
  end;

local
  fun forward A B C =
    let
      val th1 = Thm.assume A [];
      val th2 = Thm.or_intro_r (Formula.mk_or(B, C)) th1;
      val th3 = Thm.disch A th2;
      val th4 = Thm.assume B [];
      val th5 = Thm.or_intro_r C th4;
      val th6 = Thm.or_intro_l A th5;
      val th7 = Thm.disch B th6;
      val th8 = Thm.assume C [];
      val th9 = Thm.or_intro_l B th8;
      val th10 = Thm.or_intro_l A th9;
      val th11 = Thm.disch C th10;
      val th12 = Thm.or_elim th3 th7;
    in
      Thm.or_elim th12 th11
    end;
  fun backward A B C =
    let
      val th1 = Thm.assume A [];
      val th2 = Thm.or_intro_r B th1;
      val th3 = Thm.or_intro_r C th2;
      val th4 = Thm.disch A th3;
      val th5 = Thm.assume B [];
      val th6 = Thm.or_intro_l A th5;
      val th7 = Thm.or_intro_r C th6;
      val th8 = Thm.disch B th7;
      val th9 = Thm.assume C [];
      val th10 = Thm.or_intro_l (Formula.mk_or(A, B)) th9;
      val th11 = Thm.disch C th10;
      val th12 = Thm.or_elim th11 th8;
    in
      Thm.or_elim th12 th4
    end;
in
fun or_assoc A B C =
  Thm.iff_intro (forward A B C) (backward A B C)
end;

fun or_cong_l A A' B =
  let
    val A_imp_A' = Formula.mk_imp(A, A');
    val th1 = Thm.assume A_imp_A' [];
    val th2 = Thm.undisch th1;
    val th3 = Thm.or_intro_r B th2;
    val th4 = Thm.disch A th3;
    val th5 = Thm.assume B [A_imp_A'];
    val th6 = Thm.or_intro_l A' th5;
    val th7 = Thm.disch B th6;
    val th8 = Thm.or_elim th4 th7;
  in
    Thm.disch A_imp_A' th8
  end;

fun or_cong_r A B B' =
  let
    val B_imp_B' = Formula.mk_imp(B, B');
    val th1 = Thm.assume A [B_imp_B'];
    val th2 = Thm.or_intro_r B' th1;
    val th3 = Thm.disch A th2;
    val th4 = Thm.assume B_imp_B' [];
    val th5 = Thm.undisch th4;
    val th6 = Thm.or_intro_l A th5;
    val th7 = Thm.disch B th6;
    val th8 = Thm.or_elim th3 th7;
  in
    Thm.disch B_imp_B' th8
  end;
fun and_thm A B =
  let
    val AB = Formula.mk_and(A, B);
    val th1 = Thm.assume A [B];
    val th2 = Thm.assume B [A];
    val th3 = Thm.and_intro th1 th2;
    val th4 = Thm.disch B th3;
  in
    Thm.disch A th4
  end;

fun and_comm A B =
  let
    val A_and_B = Formula.mk_and(A, B);
    val th1 = Thm.assume A_and_B [];
    val th2 = Thm.and_elim_r th1;
    val th3 = Thm.and_elim_l th1;
    val th4 = Thm.and_intro th2 th3;
  in
    Thm.disch A_and_B th4
  end;

local
  fun forward A B C =
    let
      val A_BC = Formula.mk_and(A, Formula.mk_and(B, C));
      val th1 = Thm.assume A_BC [];
      val th2 = Thm.and_elim_l th1; (* ... |- A *)
      val th3 = Thm.and_elim_r th1;
      val th4 = Thm.and_elim_l th3; (* ... |- B *)
      val th5 = Thm.and_elim_r th3; (* ... |- C *)
      val th6 = Thm.and_intro th2 th4;
      val th7 = Thm.and_intro th6 th5;
    in
      Thm.disch A_BC th7
    end;
  fun backward A B C =
    let
      val AB_C = Formula.mk_and(Formula.mk_and(A, B), C);
      val th1 = Thm.assume AB_C [];
      val th2 = Thm.and_elim_l th1; (* ... |- A & B *)
      val th3 = Thm.and_elim_l th2; (* ... |- A *)
      val th4 = Thm.and_elim_r th2; (* ... |- B *)
      val th5 = Thm.and_elim_r th1; (* ... |- C *)
      val th6 = Thm.and_intro th4 th5; (* ... |- B & C *)
      val th7 = Thm.and_intro th3 th6; (* ... |- A & (B & C) *)
    in
      Thm.disch AB_C th7
    end;
in
fun and_assoc A B C =
  Thm.iff_intro (forward A B C) (backward A B C)
end;

fun and_cong_l A A' B =
  let
    val A_imp_A' = Formula.mk_imp(A, A');
    val A_and_B = Formula.mk_and(A, B);
    val th1 = Thm.assume A_imp_A' [A_and_B];
    val th2 = Thm.assume A_and_B [A_imp_A'];
    val th3 = Thm.and_elim_l th2;
    val th4 = Thm.modus_ponens th1 th3;
    val th5 = Thm.and_elim_r th2;
    val th6 = Thm.and_intro th4 th5;
    val th7 = Thm.disch A_and_B th6;
  in
    Thm.disch A_imp_A' th7
  end;

fun and_cong_r A B B' =
  let
    val A_and_B = Formula.mk_and(A, B);
    val B_imp_B' = Formula.mk_imp(B, B');
    val th1 = Thm.assume B_imp_B' [];
    val th2 = Thm.assume A_and_B [];
    val th3 = Thm.and_elim_l th2;
    val th4 = Thm.and_elim_r th2;
    val th5 = Thm.modus_ponens th1 th4;
    val th6 = Thm.and_intro th3 th5;
    val th7 = Thm.disch A_and_B th6;
  in
    Thm.disch B_imp_B' th7
  end;
fun disj_imp_disj A B C D =
  let
    val B_imp_D = Formula.mk_imp(B, D);
    val A_imp_C = Formula.mk_imp(A, C);
    val A_or_B = Formula.mk_or(A, B);
    val th1 = or_cong_l A C B;
    val th2 = Thm.undisch (Thm.undisch th1);
    val th3 = or_cong_r C B D;
    val th4 = Thm.undisch th3;
    val th5 = Thm.modus_ponens th4 th2;
  in
    Thm.disch A_or_B (Thm.disch A_imp_C (Thm.disch B_imp_D th5))
  end;

local
  fun uncurry_imp A B C =
  let
    val AB = Formula.mk_and(A, B);
    val A_imp_B_imp_C = Formula.mk_imp(A, Formula.mk_imp(B, C));
    val th1 = Thm.assume A_imp_B_imp_C [AB];
    val th2 = Thm.assume AB [A_imp_B_imp_C];
    val th3 = Thm.and_elim_l th2; (* ... |- A *)
    val th4 = Thm.modus_ponens th1 th3; (* ... |- B => C *)
    val th5 = Thm.and_elim_r th2; (* ... |- B *)
    val th6 = Thm.modus_ponens th4 th5; (* ... |- C *);
    val th7 = Thm.disch AB th6;
  in
    Thm.disch A_imp_B_imp_C th7
  end;
  fun forward A B C =
    let
      (* taut X produces "A |- X => (A & X)" *)
      fun taut X =
        let
          val lm1 = Thm.assume X [A];
          val lm2 = Thm.assume A [X];
          val lm3 = Thm.and_intro lm2 lm1;
        in
          Thm.disch X lm3
        end;
      val B_or_C = Formula.mk_or(B, C);
      val AB_or_AC = Formula.mk_or(Formula.mk_and(A, B),
                                   Formula.mk_and(A, C));
      val th1 = disj_imp_disj B C (Formula.mk_and(A,B)) (Formula.mk_and(A,C));
      val th2 = Thm.assume B_or_C [];
      val th3 = Thm.modus_ponens th1 th2;
      val th4 = Thm.modus_ponens th3 (taut B);
      val th5 = Thm.modus_ponens th4 (taut C);
      val th6 = Thm.disch B_or_C th5;
      val th7 = Thm.disch A th6; (* |- A => ((B or C) => (A & B) or (A & C)) *)
    in
      Thm.modus_ponens (uncurry_imp A B_or_C AB_or_AC) th7
    end;
  fun backward A B C =
    let
      val AB = Formula.mk_and(A, B);
      val AC = Formula.mk_and(A, C);
      val th1 = Thm.assume AB [];
      val th2 = Thm.and_elim_r th1;
      val th3 = Thm.or_intro_r C th2;
      val th4 = Thm.and_elim_l th1;
      val th5 = Thm.disch AB (Thm.and_intro th4 th3);
      val th6 = Thm.assume AC [];
      val th7 = Thm.and_elim_r th6;
      val th8 = Thm.or_intro_l B th7;
      val th9 = Thm.and_elim_l th6;
      val th10 = Thm.disch AC (Thm.and_intro th9 th8);
    in
      Thm.or_elim th5 th10
    end;
in
fun conj_disj_distribL A B C =
  Thm.iff_intro (forward A B C) (backward A B C)
end;

local
  infixr &;
  fun (A & B) = Formula.mk_and(A, B);
  fun forward A B C =
    let
      val A_or_B = Formula.mk_or(A, B);
      val th1 = conj_disj_distribL C A B;
      val th2 = Thm.iff_elim_l th1;
      val th3 = and_comm A_or_B C;
      val th4 = hypo_syll th3 th2;
      val th5 = Thm.undisch th4;
      val th6 = and_comm C A;
      val th7 = or_cong_l (C & A) (A & C) (C & B);
      val th8 = Thm.modus_ponens th7 th6;
      val th9 = Thm.modus_ponens th8 th5;
      val th10 = and_comm C B;
      val th11 = or_cong_r (A & C) (C & B) (B & C);
      val th12 = Thm.modus_ponens th11 th10;
      val th13 = Thm.modus_ponens th9 th12;
    in
      Thm.disch (Formula.mk_or(A,B) & C) th13
    end;
  fun backward A B C =
    let
      fun iter X Y =
        let
          val lm1 = Thm.assume (X & C) [];
          val lm2 = Thm.and_elim_l lm1;
          val lm3 = Thm.or_intro_r Y lm2;
          val lm4 = Thm.and_elim_r lm1;
          val lm5 = Thm.and_intro lm3 lm4;
        in
          Thm.disch (X & C) lm5
        end;
      val th20 = iter A B;
      val th26 = iter B A;
    in
      Thm.and_intro th20 th26
    end;
in
fun conj_disj_distribR A B C =
  Thm.iff_intro (forward A B C) (backward A B C)
end;
fun imp_reflexive A =
  Thm.disch A (Thm.assume A []);

fun frege_id A B C =
  let
    val A_imp_B_imp_C = Formula.mk_imp(A, Formula.mk_imp(B, C));
    val A_imp_B = Formula.mk_imp(A, B);

    val th1 = Thm.assume A [A_imp_B_imp_C, A_imp_B]; (* ... |- A *)
    val th2 = Thm.assume A_imp_B [A_imp_B_imp_C, A];
    val th3 = Thm.modus_ponens th2 th1; (* ... |- B *)
    
    val th4 = Thm.assume A_imp_B_imp_C [A_imp_B, A];
    val th5 = Thm.modus_ponens th4 th1; (* ... |- B => C *)
    val th6 = Thm.modus_ponens th5 th2; (* ... |- C *)
    val th7 = Thm.disch A th6; (* ... |- A => C *)
    val th8 = Thm.disch A_imp_B th7;
  in
    Thm.disch A_imp_B_imp_C th8
  end;

fun curry_imp A B C =
  let
    val AB = Formula.mk_and(A, B);
    val AB_imp_C = Formula.mk_imp(AB, C);
    val th1 = Thm.assume A [B, AB_imp_C];
    val th2 = Thm.assume B [A, AB_imp_C];
    val th3 = Thm.and_intro th1 th2; (* ... |- A & B *)
    val th4 = Thm.assume AB_imp_C [A, B];
    val th5 = Thm.modus_ponens th4 th3; (* |- C *)
    val th6 = Thm.disch B th5;
    val th7 = Thm.disch A th6;
  in
    Thm.disch AB_imp_C th7
  end;

fun uncurry_imp A B C =
  let
    val AB = Formula.mk_and(A, B);
    val A_imp_B_imp_C = Formula.mk_imp(A, Formula.mk_imp(B, C));
    val th1 = Thm.assume A_imp_B_imp_C [AB];
    val th2 = Thm.assume AB [A_imp_B_imp_C];
    val th3 = Thm.and_elim_l th2; (* ... |- A *)
    val th4 = Thm.modus_ponens th1 th3; (* ... |- B => C *)
    val th5 = Thm.and_elim_r th2; (* ... |- B *)
    val th6 = Thm.modus_ponens th4 th5; (* ... |- C *);
    val th7 = Thm.disch AB th6;
  in
    Thm.disch A_imp_B_imp_C th7
  end;

fun hypo_syll_thm A B C =
  let
    val A_imp_B = Formula.mk_imp(A, B);
    val B_imp_C = Formula.mk_imp(B, C);
    val th1 = Thm.assume A [A_imp_B, B_imp_C];
    val th2 = Thm.assume A_imp_B [A, B_imp_C];
    val th3 = Thm.modus_ponens th2 th1;
    val th4 = Thm.assume B_imp_C [A, B_imp_C];
    val th5 = Thm.modus_ponens th4 th3;
    val th6 = Thm.disch A th5;
    val th7 = Thm.disch B_imp_C th6;
  in
    Thm.disch A_imp_B th7
  end;

fun imp_trans A B C =
  Thm.modus_ponens (uncurry_imp (Formula.mk_imp(A, B))
                                (Formula.mk_imp(B, C))
                                (Formula.mk_imp(A, C)))
                   (hypo_syll_thm A B C);

fun contrapositive A B =
  let
    val A_imp_B = Formula.mk_imp(A, B);
    val not_B = Formula.mk_not(B);
    val th1 = Thm.assume A_imp_B [A, not_B];
    val th2 = Thm.assume A [A_imp_B, not_B];
    val th3 = Thm.modus_ponens th1 th2;      (* A, not B, A => B |- B *)
    val th4 = Thm.assume not_B [A, A_imp_B]; (* A, not B, A => B |- not B *)
    val th5 = Thm.not_elim th4;
    val th6 = Thm.modus_ponens th5 th3;      (* A, not B, A => B |- false *)
    val th7 = Thm.disch A th6;           (* not B, A => B |- A => false *)
    val th8 = Thm.not_intro th7;             (* not B, A => B |- not A *)
    val th9 = Thm.disch not_B th8;
  in
    Thm.disch A_imp_B th9
  end;
fun contrapositive_not A B =
  let
    val not_B = Formula.mk_not B;
    val not_A = Formula.mk_not A;
    val A_imp_not_B = Formula.mk_imp(A, not_B);
    val not_A_imp_B = Formula.mk_imp(not_A, B);
    val th1 = Thm.assume A_imp_not_B [A, B];
    val th2 = Thm.assume A [A_imp_not_B, B];
    val th3 = Thm.modus_ponens th1 th2; (* A, B, A => not B |- not B *)
    val th4 = Thm.not_elim th3;         (* A, B, A => not B |- B => false *)
    val th5 = Thm.assume B [A_imp_not_B, A];
    val th6 = Thm.modus_ponens th4 th5; (* A, B, A => not B |- false *)
    val th7 = Thm.disch A th6;      (* B, A => not B |- A => false *)
    val th8 = Thm.not_intro th7;        (* B, A => not B |- not A *)
    val th9 = Thm.disch B th8;      (* A => not B |- B => not A *)
  in
    Thm.disch A_imp_not_B th9
  end;
local
  fun backward A B =
    let
      val not_A_and_not_B = Formula.mk_and(Formula.mk_not(A),
                                           Formula.mk_not(B));
      val th1 = Thm.assume not_A_and_not_B [];
      val th2 = Thm.and_elim_l th1;
      val th3 = Thm.not_elim th2;
      val th4 = Thm.and_elim_r th1;
      val th5 = Thm.not_elim th4;
      val th6 = Thm.or_elim th3 th5;
      val th7 = Thm.not_intro th6;
    in
      Thm.disch not_A_and_not_B th7
    end;
  fun forward A B =
    let
      val A_or_B = Formula.mk_or(A, B);
      val not_A_and_not_B = Formula.mk_and(Formula.mk_not(A),
                                           Formula.mk_not(B));
      val F = Formula.mk_falsum ();
      val th1 = Thm.assume F [A_or_B];
      val th2 = Thm.contr not_A_and_not_B th1;
      val th3 = Thm.disch F th2;
      val th4 = Thm.disch A_or_B th3;
      val th5 = frege_id A_or_B F not_A_and_not_B;
      val th6 = Thm.modus_ponens th5 th4;
      val th7 = Thm.disch not_A_and_not_B
                              (Thm.not_elim (Thm.assume not_A_and_not_B []));
    in
      hypo_syll th7 th6
    end;
in
fun not_or A B =
  Thm.iff_intro (forward A B) (backward A B)
end;

fun not_and A B =
  let
    val A_and_B = Formula.mk_and(A, B);
    val th1 = Thm.assume A_and_B [];
    fun iter X and_elim =
      let
        val lm2 = and_elim th1;
        val lm3 = Thm.disch A_and_B lm2;
        val lm4 = contrapositive A_and_B X;
      in
        Thm.modus_ponens lm4 lm3
      end;
    val th6 = iter A (Thm.and_elim_l);
    val th9 = iter B (Thm.and_elim_r);
  in
    Thm.or_elim th6 th9
  end;

fun not_disj_to_imp A B =
  let
    val not_A = Formula.mk_not(A);
    val th1 = weak_not_elim A B;
    val th2 = Thm.undisch (Thm.undisch th1);
    val th3 = Thm.disch not_A (Thm.disch A th2);

    val th4 = Thm.assume B [A];
    val th5 = Thm.disch A th4;
    val th6 = Thm.disch B th5;
  in
    Thm.or_elim th3 th6
  end;

fun imp_is_not_and A B =
  let
    val not_B = Formula.mk_not(B);
    val A_and_not_B = Formula.mk_and(A, not_B);
    val A_imp_B = Formula.mk_imp(A, B);
    val th1 = Thm.assume A_and_not_B [A_imp_B];
    val th2 = Thm.and_elim_l th1;            (* ... |- A *)
    val th3 = Thm.and_elim_r th1;            (* ... |- not B *)
    val th4 = Thm.not_elim th3;              (* ... |- B => false *)
    val th5 = Thm.assume A_imp_B [A_and_not_B]; (* ... |- A => B *)
    val th6 = Thm.modus_ponens th5 th2;      (* ... |- B *)
    val th7 = Thm.modus_ponens th4 th6;      (* ... |- false *)
    val th8 = Thm.disch A_and_not_B th7; (* ... |- (A & not B) => false *)
    val th9 = Thm.not_intro th8;             (* ... |- not (A & not B) *)
  in
    Thm.disch A_imp_B th9
  end;

fun iff_refl A =
  let val th1 = imp_reflexive A
  in Thm.iff_intro th1 th1 end;

fun iff_sym A B =
  let
    val A_iff_B = Formula.mk_iff(A, B);
    val th1 = Thm.assume A_iff_B [];
    val th2 = Thm.iff_elim_l th1; (* ... |- A => B *)
    val th3 = Thm.iff_elim_r th1; (* ... |- B => A *)
  in
    Thm.disch A_iff_B (Thm.iff_intro th3 th2)
  end;

fun iff_trans A B C =
  let
    val A_iff_B = Formula.mk_iff(A, B);
    val B_iff_C = Formula.mk_iff(B, C);
    val AB_and_BC = Formula.mk_and(A_iff_B, B_iff_C);
    val th1 = Thm.assume AB_and_BC [];
    val th2 = Thm.and_elim_l th1; (* ... |- A iff B *)
    val th3 = Thm.iff_elim_l th2; (* ... |- A => B *)
    val th4 = Thm.and_elim_r th1; (* ... |- B iff C *)
    val th5 = Thm.iff_elim_r th4; (* ... |- B => C *)
    val th6 = Thm.and_intro th3 th5; (* ... |- (A => B) & (B => C *)
    val th7 = Thm.modus_ponens (imp_trans A B C) th6; (* ... |- A => C *)
    val th8 = Thm.iff_elim_r th2; (* ... |- B => A *)
    val th9 = Thm.iff_elim_l th4; (* ... |- C => B *)
    val th10 = Thm.and_intro th4 th8; (* ... |- (C => B) & (B => A *)
    val th11 = Thm.modus_ponens (imp_trans C B A) th10; (* ... |- C => A *)
    val th12 = Thm.iff_intro th7 th11; (* ... |- A iff C *)
  in
    Thm.disch AB_and_BC th12
  end;


(* all_disjL : Term.t. -> Formula.t -> Formula.t -> Thm.t *)
fun all_disjL x A C =
  let
    val th1 = Thm.assume C [];
    val th2 = Thm.or_intro_l A th1;
    val th3 = Thm.forall_intro x th2;
    val th4 = Thm.disch C th3;
    val th5 = Thm.assume (Formula.mk_forall(x, A)) [];
    val th6 = Thm.forall_elim x th5;
    val th7 = Thm.or_intro_r C th6;
    val th8 = Thm.forall_intro x th7;
    val th9 = Thm.disch (Formula.mk_forall(x, A)) th8;
  in
    Thm.or_elim th9 th4
  end;
local
  fun forward x A B =
    let
      val th1 = Thm.assume A [];
      val th2 = Thm.or_intro_r B th1;
      val th3 = Thm.exists_intro x x (Formula.mk_or(A, B))
                                 th2;
      val th4 = Thm.disch A th3;
      val th5 = Thm.exists_elim x th4;
      val th6 = Thm.assume B [];
      val th7 = Thm.or_intro_l A th6;
      val th8 = Thm.exists_intro x x (Formula.mk_or(A, B)) th7;
      val th9 = Thm.disch B th8;
      val th10 = Thm.exists_elim x th9;
    in
      Thm.or_elim th5 th10
    end;
  fun backward x A B =
    let
      val th1 = Thm.assume A [];
      val th2 = Thm.exists_intro x x A th1;
      val th3 = Thm.or_intro_r (Formula.mk_exists(x, B)) th2;
      val th4 = Thm.disch A th3;
      val th5 = Thm.assume B [];
      val th6 = Thm.exists_intro x x B th5;
      val th7 = Thm.or_intro_l (Formula.mk_exists(x, A)) th6;
      val th8 = Thm.disch B th7;
      val th9 = Thm.or_elim th4 th8;
    in
      Thm.exists_elim x th9
    end;
in
fun ex_disj_distrib x A B =
  Thm.iff_intro (forward x A B) (backward x A B)
end;
fun all_conj_distrib x A B =
  let
    (* backward proof *)
    val th1 = Thm.assume (Formula.mk_forall(x, Formula.mk_and(A, B))) [];
    val th2 = Thm.forall_elim x th1;
    val th3 = Thm.and_elim_l th2; (* ... |- A[x] *)
    val th4 = Thm.forall_intro x th3;
    val th5 = Thm.and_elim_r th2; (* ... |- B[x] *)
    val th6 = Thm.forall_intro x th5;
    val th7 = Thm.and_intro th4 th6;
    val th8 = Thm.disch (Formula.mk_forall(x, Formula.mk_and(A, B))) th7;
    (* forward proof *)
    val th9 = Thm.assume (Formula.mk_and(Formula.mk_forall(x, A),
                                         Formula.mk_forall(x, B)))
                         [];
    val th10 = Thm.and_elim_l th9;
    val th11 = Thm.forall_elim x th10;
    val th12 = Thm.and_elim_r th9;
    val th13 = Thm.forall_elim x th12;
    val th14 = Thm.and_intro th11 th13;
    val th15 = Thm.forall_intro x th14;
    val th16 = Thm.disch (Formula.mk_and(Formula.mk_forall(x, A),
                                         Formula.mk_forall(x, B)))
                         th15;
  in
    Thm.iff_intro th16 th8
  end;
fun ex_conj_distrib x A B =
  let
    val AB = Formula.mk_and(A, B);
    val th1 = Thm.assume AB [];
    val th2 = Thm.and_elim_l th1;
    val th3 = Thm.exists_intro x x A th2;
    val th4 = Thm.and_elim_r th1;
    val th5 = Thm.exists_intro x x B th4;
    val th6 = Thm.and_intro th3 th5;
    val th7 = Thm.disch AB th6;
  in
    Thm.exists_elim x th7
  end;
local
fun backward x A C =
  let
    val ex_A = Formula.mk_exists(x, A);
    val ex_A_imp_C = Formula.mk_imp(ex_A, C);
    (* val A_imp_C = Formula.mk_imp(A, C); *)
    val th1 = Thm.assume A [ex_A_imp_C];
    val th2 = Thm.exists_intro x x A th1;
    val th3 = Thm.assume ex_A_imp_C [A];
    val th4 = Thm.modus_ponens th3 th2;
    val th5 = Thm.disch A th4;
    val th6 = Thm.forall_intro x th5;
  in
    Thm.disch ex_A_imp_C th6
  end;

fun forward x A C =
  let
    val A_imp_C = Formula.mk_imp(A, C);
    val for_x_st_A_holds_C = Formula.mk_forall(x, A_imp_C);
    val th1 = Thm.assume for_x_st_A_holds_C [];
    val th2 = Thm.forall_elim x th1;
    val th3 = Thm.exists_elim x th2;
  in
    Thm.disch for_x_st_A_holds_C th3
  end;
in
fun imp_ex x A C =
  Thm.iff_intro (forward x A C) (backward x A C)
end;
local
fun backward x A =
  let
    val ex_A = Formula.mk_exists(x, A);
    val F = Formula.mk_falsum ();
    val ex_A_imp_F = Formula.mk_imp(ex_A, F);
    (* val A_imp_F = Formula.mk_imp(A, F); *)
    val th1 = Thm.assume A [ex_A_imp_F];
    val th2 = Thm.exists_intro x x A th1;
    val th3 = Thm.assume ex_A_imp_F [A];
    val th4 = Thm.modus_ponens th3 th2; (* ... |- false *)
    val th5 = Thm.disch A th4; (* ... |- A => false *)
    val th6 = Thm.not_intro th5; (* ... |- not A[x] *)
    val th7 = Thm.forall_intro x th6; (* ... |- for x holds not A[x] *)
    val th8 = Thm.assume (Formula.mk_not ex_A) [];
    val th9 = Thm.not_elim th8;
  in
    hypo_syll (Thm.disch (Formula.mk_not ex_A) th9)
              (Thm.disch ex_A_imp_F th7)
  end;

fun forward x A =
  let
    val F = Formula.mk_falsum ();
    val A_imp_F = Formula.mk_imp(A, F);
    val for_x_holds_not_A = Formula.mk_forall(x, Formula.mk_not(A));
    val th1 = Thm.assume for_x_holds_not_A []; 
    val th2 = Thm.forall_elim x th1; (* ... |- not A[x] *)
    val th3 = Thm.not_elim th2; (* ... |- A[x] => false *)
    val th4 = Thm.exists_elim x th3; (* ... |- (exists x. A[x]) => false *)
    val th5 = Thm.not_intro th4; (* ... |- not(exists x. A[x]) *)
  in
    Thm.disch for_x_holds_not_A th5
  end;
in
fun not_all_iff_ex_not x A =
  Thm.iff_intro (forward x A) (backward x A)
end;
(* all_imp : Term.t -> Formula.t -> Formula.t -> Thm.t

all_imp x C A =
|- (for x st C holds A[x]) iff (C implies for x holds A[x]) *)
fun all_imp x C A =
  let
    val all_C_imp_A = Formula.mk_forall(x, Formula.mk_imp(C, A));
    (* forward direction *)
    val th1 = Thm.assume all_C_imp_A [];
    val th2 = Thm.forall_elim x th1;
    val th3 = Thm.undisch th2;
    val th4 = Thm.forall_intro x th3;
    val th5 = Thm.disch C th4;
    val th6 = Thm.disch all_C_imp_A th5;
    (* backward direction *)
    val C_imp_all_A = Formula.mk_imp(C, Formula.mk_forall(x, A));
    val th7 = Thm.assume C_imp_all_A [];
    val th8 = Thm.undisch th7;
    val th9 = Thm.forall_elim x th8;
    val th10 = Thm.disch C th9;
    val th11 = Thm.forall_intro x th10;
    val th12 = Thm.disch C_imp_all_A th11;
  in
    Thm.iff_intro th6 th12
  end;
fun imp_all x A C =
  let
    val A_imp_C = Formula.mk_imp(A, C);
    val all_A = Formula.mk_forall(x, A);
    val th1 = Thm.assume A_imp_C [];
    val th2 = Thm.assume all_A [];
    val th3 = Thm.forall_elim x th2;
    val th4 = Thm.modus_ponens th1 th3;
    val th5 = Thm.disch all_A th4;
    val th6 = Thm.disch A_imp_C th5;
  in
    Thm.exists_elim x th6
  end;
fun ex_not x A =
  let
    val not_A = Formula.mk_not A;
    val all_A = Formula.mk_forall(x, A);
    val F = Formula.mk_falsum ();
    val th1 = Thm.assume not_A [];
    val th2 = Thm.not_elim th1;
    val th3 = Thm.assume all_A [];
    val th4 = Thm.forall_elim x th3;
    val th5 = Thm.modus_ponens th2 th4;
    val th6 = Thm.disch all_A th5;
    val th7 = Thm.not_intro th6;
    val th8 = Thm.disch not_A th7;
  in
    Thm.exists_elim x th8
  end;
(* ex_imp : Term.t -> Formula.t -> Formula.t -> Thm.t

|- (ex x st C implies A[x]) implies (C implies ex x st A[x]) *)
fun ex_imp x C A =
  let
    val C_imp_A = Formula.mk_imp(C, A);
    val th1 = Thm.assume C_imp_A [];
    val th2 = Thm.assume C [];
    val th3 = Thm.modus_ponens th1 th2;
    val th4 = Thm.exists_intro x x A th3;
    val th5 = Thm.disch C th4;
    val th6 = Thm.disch C_imp_A th5;
  in
    Thm.exists_elim x th6
  end;
(* exists_elim : Term.t -> Thm.t -> Thm.t -> Thm.t *)
fun exists_elim (v : Term.t) (th1 : Thm.t) (th2 : Thm.t) : Thm.t =
  let
    val (x,A) = Formula.dest_exists(Thm.conc th1);
    val Av = Formula.subst x v A;
    val th3 = weaken Av th2;
    val th4 = Thm.disch Av th3;
    val th5 = Thm.exists_elim v th4;
    (* aside on renaming bound variables *)
    val lm1 = Thm.assume (Formula.mk_exists(x,A)) [Av];
    val lm2 = Thm.disch Av lm1;
    val lm3 = Thm.disch (Formula.mk_exists(x,A)) lm1;
    val th6 = Thm.modus_ponens lm3 th1;
    val th7 = hypo_syll lm4 th5;
  in
    Thm.modus_ponens th7 th1
  end;

end;
