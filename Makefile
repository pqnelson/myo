.POSIX:
TEX=latex
FILE=myo
NOWEBOPTS=-latex -n -indexfrom $(FILE).defs
NWFILES=nw/many-sorted-term.nw nw/many-sorted-formula.nw nw/kernel.nw \
	nw/fs0-syntax.nw nw/state.nw nw/derived.nw nw/goal.nw \
	nw/unification.nw nw/classical.nw nw/printer.nw nw/xunit.nw
.SUFFIXES: .nw .tex
.PHONY: pdf extract_text nw %.nw $(NWFILES)

all: extract_text pdf

pdf:
	$(TEX) $(FILE)
	bibtex $(FILE)
	$(TEX) $(FILE)
	$(TEX) $(FILE)
	dvipdfmx $(FILE).dvi

extract_text: defs $(NWFILES)

# Amazingly enough, this is POSIX-compliant!
$(NWFILES):
	noweave $(NOWEBOPTS) $@ > tex/$(*F).tex

defs:
	nodefs $(NWFILES) > $(FILE).defs
	sort -u $(FILE).defs | cpif $(FILE).defs

code:
	notangle -RSort.sml $(NWFILES) | tr -d '\r' > src/Sort.sml
	notangle -RTerm.sml $(NWFILES) | tr -d '\r' > src/Term.sml
	notangle -RTerm.sig $(NWFILES) | tr -d '\r' > src/Term.sig
	notangle -RFormula.sml $(NWFILES) | tr -d '\r' > src/Formula.sml
	notangle -RFormula.sig $(NWFILES) | tr -d '\r' > src/Formula.sig
	notangle -RThm.sml $(NWFILES) | tr -d '\r' > src/Thm.sml
	notangle -RThm.sig $(NWFILES) | tr -d '\r' > src/Thm.sig
	notangle -RFS0.sml $(NWFILES) | tr -d '\r' > src/FS0.sml
	notangle -RFS0.sig $(NWFILES) | tr -d '\r' > src/FS0.sig
	notangle -RDerived.sml $(NWFILES) | tr -d '\r' > src/Derived.sml
	notangle -Rtests/DerivedSuite.sml $(NWFILES) | tr -d '\r' > tests/DerivedSuite.sml
	notangle -RGoal.sml $(NWFILES) | tr -d '\r' > src/Goal.sml
	notangle -RGoal.sig $(NWFILES) | tr -d '\r' > src/Goal.sig
	notangle -RTactic.sig $(NWFILES) | tr -d '\r' > src/Tactic.sig
	notangle -RTactic.sml $(NWFILES) | tr -d '\r' > src/Tactic.sml
	notangle -Rtests/TacticSuite.sml $(NWFILES) | tr -d '\r' > tests/TacticSuite.sml
	notangle -RPrinter.sig $(NWFILES) | tr -d '\r' > src/Printer.sig
	notangle -RTBPrinter.sml $(NWFILES) | tr -d '\r' > src/TBPrinter.sml
	notangle -RUnif.sig $(NWFILES) | tr -d '\r' > src/Unif.sig
	notangle -RUnif.sml $(NWFILES) | tr -d '\r' > src/Unif.sml
	notangle -RClassical.sig $(NWFILES) | tr -d '\r' > src/Classical.sig
	notangle -RClassical.sml $(NWFILES) | tr -d '\r' > src/Classical.sml
	notangle -Rtests/ClassicalSuite.sml $(NWFILES) | tr -d '\r' > tests/ClassicalSuite.sml
	notangle -Rtest.mlb $(NWFILES) | tr -d '\r' > test.mlb
	notangle -RAssert.sml $(NWFILES) | tr -d '\r' > tests/Assert.sml
	notangle -RTest.sig $(NWFILES) | tr -d '\r' > tests/Test.sig
	notangle -RTest.sml $(NWFILES) | tr -d '\r' > tests/Test.sml
	notangle -RReporter.sig $(NWFILES) | tr -d '\r' > tests/Reporter.sig
	notangle -RJUnitTt.sml $(NWFILES) | tr -d '\r' > tests/JUnitTt.sml
	notangle -RTestRunner.sig $(NWFILES) | tr -d '\r' > tests/TestRunner.sig
	notangle -Rtests/MkRunner.sml $(NWFILES) | tr -d '\r' > tests/MkRunner.sml
	notangle -Rtests/main.sml $(NWFILES) | tr -d '\r' > tests/main.sml
	notangle -Rtests/TestSuite.sig $(NWFILES) | tr -d '\r' > tests/TestSuite.sig


clean:
	rm src/*.sig src/*.sml tests/*.sig tests/*.sml