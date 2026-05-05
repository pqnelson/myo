structure ClassicalSuite : TestSuite = struct
(* helper functions to make unit tests prettier *)
val A = Formula.mk_pred("A", []);
val B = Formula.mk_pred("B", []);
infixr ==> <=>;
fun (p ==> q) = Formula.mk_imp(p, q);
fun (p <=> q) = Formula.mk_iff(p, q);
infixr &;
fun (p & q) = Formula.mk_and(p, q);

fun ~ p = Formula.mk_not(p);

fun exists(x, p) = Formula.mk_exists(x, p);
fun all(x, p) = Formula.mk_forall(x, p);

(* the tests themselves *)
val suite = Test.suite "ClassicalSuite" [
  Test.mk "Pelletier #1" (fn () =>
    let
      val fm = (A ==> B) <=> ((~ B) ==> (~ A));
      val expected = 0;
      val actual = Classical.tab fm 3;
    in
      Assert.eq expected
                actual
                (concat ["EXPECTED: ",
                         Int.toString expected,
                         "\nACTUAL: ",
                         Int.toString actual])
    end)
  , Test.mk "Pelletier #2" (fn () =>
      let
        val fm = (~ (~ A)) <=> A;
        val expected = 0;
        val actual = Classical.tab fm 3;
      in
        Assert.eq expected
                  actual
                  (concat ["EXPECTED: ",
                           Int.toString expected,
                           "\nACTUAL: ",
                           Int.toString actual])
      end)
  , Test.mk "Pelletier #3" (fn () =>
      let
        val fm = (~(A ==> B)) ==> (B ==> A);
        val expected = 0;
        val actual = Classical.tab fm 3;
      in
        Assert.eq expected
                  actual
                  (concat ["EXPECTED: ",
                           Int.toString expected,
                           "\nACTUAL: ",
                           Int.toString actual])
      end)
  , Test.mk "Pelletier #4" (fn () =>
      let
        val fm = (((~ A) ==> B) <=> ((~ B) ==> A));
        val expected = 0;
        val actual = Classical.tab fm 3;
      in
        Assert.eq expected
                  actual
                  (concat ["EXPECTED: ",
                           Int.toString expected,
                           "\nACTUAL: ",
                           Int.toString actual])
      end)
  , Test.mk "Pelletier #5" (fn () =>
      let
        val fm = Formula.mk_or(A, ~ A);
        val expected = 0;
        val actual = Classical.tab fm 3;
      in
        Assert.eq expected
                  actual
                  (concat ["EXPECTED: ",
                           Int.toString expected,
                           "\nACTUAL: ",
                           Int.toString actual])
      end)
  , Test.mk "Pelletier #18" (fn () =>
      let
        val x = Term.Var("x",Sort.IND);
        val y = Term.Var("y",Sort.IND);
        fun P t = Formula.mk_pred("P", [t]);
        val fm = (exists(y, all(x, (P y) ==> (P x))));
        val expected = 2;
        val actual = Classical.tab fm 5;
      in
        Assert.eq expected
                  actual
                  (concat ["EXPECTED: ",
                           Int.toString expected,
                           "\nACTUAL: ",
                           Int.toString actual])
      end)
  , Test.mk "Pelletier #19" (fn () =>
      let
        val x = Term.Var("x",Sort.IND);
        val y = Term.Var("y",Sort.IND);
        val z = Term.Var("z",Sort.IND);
        fun P t = Formula.mk_pred("P", [t]);
        fun Q t = Formula.mk_pred("Q", [t]);
        val fm = exists(x,
                        all(y,
                            all(z, ((P y) ==> (Q z))
                                     ==>
                                   (P x) ==> (Q x))));
        val expected = 2;
        val actual = Classical.tab fm 5;
      in
        Assert.eq expected
                  actual
                  (concat ["EXPECTED: ",
                           Int.toString expected,
                           "\nACTUAL: ",
                           Int.toString actual])
      end)
];
end;
