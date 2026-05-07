structure TacticSuite : TestSuite = struct
val suite = Test.suite "TacticSuite" [
  Test.mk "and_comm test" (fn () =>
    let
      val A = Formula.mk_pred("A", []);
      val B = Formula.mk_pred("B", []);
      val expected = Formula.mk_imp(Formula.mk_and(A, B),
                                    Formula.mk_and(B, A));
      val g0 = Goal.setup expected;
      val g1 = Tactic.disch "" g0;
      val g2 = Tactic.and_intro g1;
      val g3 = Tactic.and_elim_r A g2;
      val g4 = Tactic.assume g3;
      val g5 = Tactic.and_elim_l B g4;
      val g6 = Tactic.assume g5;
      val thm = Goal.extract_thm g6;
      val actual = Thm.concl thm;
    in
      Assert.that (Formula.eq expected actual)
                  (concat ["EXPECTED: ",
                           Formula.serialize expected,
                           "\nACTUAL: ",
                           Formula.serialize actual,
                           "\n"])
    end)
, Test.mk "and_comm Tactic.prove test" (fn () =>
    let
      val A = Formula.mk_pred("A", []);
      val B = Formula.mk_pred("B", []);
      val expected = Formula.mk_imp(Formula.mk_and(A, B),
                                    Formula.mk_and(B, A));
      val thm = Tactic.prove expected
                             [ Tactic.disch ""
                             , Tactic.and_intro
                             , Tactic.and_elim_r A
                             , Tactic.assume
                             , Tactic.and_elim_l B
                             , Tactic.assume];
      val actual = Thm.concl thm;
    in
      Assert.that (Formula.eq expected actual)
                  (concat ["EXPECTED: ",
                           Formula.serialize expected,
                           "\nACTUAL: ",
                           Formula.serialize actual,
                           "\n"])
    end)
, Test.mk "or_cong_l Tactic.prove test" (fn () =>
    let
      val A0 = Formula.mk_pred("A", []);
      val A1 = Formula.mk_pred("A'", []);
      val B = Formula.mk_pred("B", []);
      val expected = Formula.mk_imp(Formula.mk_imp(A0, A1),
                                    Formula.mk_imp(Formula.mk_or(A0,B),
                                                   Formula.mk_or(A1,B)));
      val thm = Tactic.prove expected
                             [ Tactic.disch ""
                             , Tactic.disch ""
                             , Tactic.disj_cases (Thm.assume (Formula.mk_or(A0,B)) [])
                             , Tactic.disch ""
                             , Tactic.or_l
                             , Tactic.undisch A0
                             , Tactic.assume
                             , Tactic.disch ""
                             , Tactic.or_r
                             , Tactic.assume ];
      val actual = Thm.concl thm;
    in
      Assert.that (Formula.eq expected actual)
                  (concat ["EXPECTED: ",
                           Formula.serialize expected,
                           "\nACTUAL: ",
                           Formula.serialize actual,
                           "\n"])
    end)
]
end;
