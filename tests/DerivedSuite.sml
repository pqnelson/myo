structure DerivedSuite : TestSuite = struct
val suite = Test.suite "DerivedSuite" [
  Test.mk "all_disjL_test" (fn () =>
    let
      val x = Term.Var("x", Sort.IND);
      val A = Formula.mk_pred("A", [x]);
      val C = Formula.mk_pred("C", []);
      val expected = Formula.mk_imp(Formula.mk_or(Formula.mk_forall(x,A),C),
                                    Formula.mk_forall(x, Formula.mk_or(A,C)));
      val actual = Thm.concl (Derived.all_disjL x A C);
    in
      Assert.that (Formula.eq expected actual)
                  (concat ["EXPECTED: ",
                           (TBPrinter.formula expected),
                           "\nACTUAL: ",
                           (TBPrinter.formula actual)])
    end)
, Test.mk "ex_disj_distrib_test" (fn () =>
    let
      val x = Term.Var("x", Sort.IND);
      val A = Formula.mk_pred("A", [x]);
      val B = Formula.mk_pred("B", [x]);
      val expected =
        Formula.mk_iff(Formula.mk_or(Formula.mk_exists(x,A),
                                     Formula.mk_exists(x,B)),
                       Formula.mk_exists(x, Formula.mk_or(A,B)));
      val actual = Thm.concl (Derived.ex_disj_distrib x A B);
    in
      Assert.that (Formula.eq expected actual)
                  (concat["EXPECTED: ",
                          TBPrinter.formula expected,
                          "\nACTUAL: ",
                          TBPrinter.formula actual,
                          "\n"])
    end)
, Test.mk "all_conj_distrib_test" (fn () =>
    let
      val x = Term.Var("x", Sort.IND);
      val A = Formula.mk_pred("A", [x]);
      val B = Formula.mk_pred("B", [x]);
      val expected =
        Formula.mk_iff(Formula.mk_and(Formula.mk_forall(x,A),
                                      Formula.mk_forall(x,B)),
                       Formula.mk_forall(x, Formula.mk_and(A,B)));
      val actual = Thm.concl (Derived.all_conj_distrib x A B);
    in
      Assert.that (Formula.eq expected actual)
                  (concat ["Expecting: ",
                           (Formula.serialize expected),
                           "\nActual: ",
                           (Formula.serialize actual),
                           "\n"])
    end)
, Test.mk "ex_conj_distrib_test" (fn () =>
    let
      val x = Term.Var("x", Sort.IND);
      val A = Formula.mk_pred("A", [x]);
      val B = Formula.mk_pred("B", [x]);
      val expected =
        Formula.mk_imp(Formula.mk_exists(x, Formula.mk_and(A,B)),
                       Formula.mk_and(Formula.mk_exists(x, A),
                                      Formula.mk_exists(x, B)));
      val actual = Thm.concl (Derived.ex_conj_distrib x A B);
    in
      Assert.that (Formula.eq expected actual)
                  (concat ["Expecting: ",
                           (Formula.serialize expected),
                           "\nActual: ",
                           (Formula.serialize actual),
                           "\n"])
    end)
, Test.mk "imp_ex_test" (fn () =>
    let
      val x = Term.Var("x", Sort.IND);
      val A = Formula.mk_pred("A", [x]);
      val C = Formula.mk_pred("C", []);
      val expected =
        Formula.mk_iff(Formula.mk_forall(x, Formula.mk_imp(A,C)),
                       Formula.mk_imp(Formula.mk_exists(x, A),
                                      C));
      val actual = Thm.concl (Derived.imp_ex x A C);
    in
      Assert.that (Formula.eq expected actual)
                  (concat ["Expecting: ",
                           (Formula.serialize expected),
                           "\nActual: ",
                           (Formula.serialize actual),
                           "\n"])
    end)
, Test.mk "not_all_iff_ex_not_test" (fn () =>
    let
      val x = Term.Var("x", Sort.IND);
      val A = Formula.mk_pred("A", [x]);
      val expected =
        Formula.mk_iff(Formula.mk_forall(x, Formula.mk_not(A)),
                       Formula.mk_not(Formula.mk_exists(x, A)));
      val actual = Thm.concl (Derived.not_all_iff_ex_not x A);
    in
      Assert.that (Formula.eq expected actual)
                  (concat ["Expecting: ",
                           (Formula.serialize expected),
                           "\nActual: ",
                           (Formula.serialize actual),
                           "\n"])
    end)
, Test.mk "all_imp_test" (fn () =>
    let
      val x = Term.Var("x", Sort.IND);
      val A = Formula.mk_pred("A", [x]);
      val C = Formula.mk_pred("C", []);
      val expected =
        Formula.mk_iff(Formula.mk_forall(x, Formula.mk_imp(C, A)),
                       Formula.mk_imp(C, Formula.mk_forall(x, A)));
      val actual = Thm.concl (Derived.all_imp x C A);
    in
      Assert.that (Formula.eq expected actual)
                  (concat ["Expecting: ",
                           (Formula.serialize expected),
                           "\nActual: ",
                           (Formula.serialize actual),
                           "\n"])
    end)
, Test.mk "imp_all_test" (fn () =>
    let
      val x = Term.Var("x", Sort.IND);
      val A = Formula.mk_pred("A", [x]);
      val C = Formula.mk_pred("C", []);
      val expected =
        Formula.mk_imp(Formula.mk_exists(x, Formula.mk_imp(A,C)),
                       Formula.mk_imp(Formula.mk_forall(x, A),
                                      C));
      val actual = Thm.concl (Derived.imp_all x A C);
    in
      Assert.that (Formula.eq expected actual)
                  (concat ["Expecting: ",
                           (Formula.serialize expected),
                           "\nActual: ",
                           (Formula.serialize actual),
                           "\n"])
    end)
, Test.mk "ex_not_test" (fn () =>
    let
      val x = Term.Var("x", Sort.IND);
      val A = Formula.mk_pred("A", [x]);
      val expected =
        Formula.mk_imp(Formula.mk_exists(x, Formula.mk_not(A)),
                       Formula.mk_not(Formula.mk_forall(x, A)));
      val actual = Thm.concl (Derived.ex_not x A);
    in
      Assert.that (Formula.eq expected actual)
                  (concat ["Expecting: ",
                           (Formula.serialize expected),
                           "\nActual: ",
                           (Formula.serialize actual),
                           "\n"])
    end)
, Test.mk "ex_imp_test" (fn () =>
    let
      val x = Term.Var("x", Sort.IND);
      val A = Formula.mk_pred("A", [x]);
      val C = Formula.mk_pred("C", []);
      val expected =
        Formula.mk_imp(Formula.mk_exists(x, Formula.mk_imp(C,A)),
                       Formula.mk_imp(C,
                                      Formula.mk_exists(x, A)));
      val actual = Thm.concl (Derived.ex_imp x C A);
    in
      Assert.that (Formula.eq expected actual)
                  (concat ["Expecting: ",
                           (Formula.serialize expected),
                           "\nActual: ",
                           (Formula.serialize actual),
                           "\n"])
    end)
, Test.mk "forall_cong_test" (fn () =>
    let
      fun A x = Formula.mk_pred("A",[x]);
      val x = Term.Var("x",Sort.IND);
      val y = Term.Var("y",Sort.IND);
      val expected = Formula.mk_imp(Formula.mk_forall(x, A x),
                                    Formula.mk_forall(y, A y));
      val actual = Thm.concl(Derived.forall_cong x y A);
    in
      Assert.that (Formula.eq expected actual)
                  (concat ["Expecting: ",
                           (Formula.serialize expected),
                           "\nActual: ",
                           (Formula.serialize actual),
                           "\n"])
    end)
, Test.mk "exists_cong_test" (fn () =>
    let
      fun A x = Formula.mk_pred("A",[x]);
      val x = Term.Var("x",Sort.IND);
      val y = Term.Var("y",Sort.IND);
      val expected = Formula.mk_imp(Formula.mk_exists(x, A x),
                                    Formula.mk_exists(y, A y));
      val actual = Thm.concl(Derived.exists_cong x y A);
    in
      Assert.that (Formula.eq expected actual)
                  (concat ["Expecting: ",
                           (Formula.serialize expected),
                           "\nActual: ",
                           (Formula.serialize actual),
                           "\n"])
    end)
]
end;
