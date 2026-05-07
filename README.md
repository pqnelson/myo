# Myo, the proof assistant

## Overview

This is a small proof assistant to explore implementing intuitionistic
first-order logic plus Feferman's FS0 axioms as a metalogical
framework for exploring proof assistants.

Myo is an attempt to answer the [MYSTIC challenge](https://pqnelson.github.io/2024/06/11/MYSTIC-challenge.html) (i.e., create a toy
simplified clone of Isabelle, for the intended purpose of reasoning
about the metatheory of a Mizar-like proof assistant).

The name is a pun ([妙](https://en.wiktionary.org/wiki/%E5%A6%99), Japanese _myō_, for "mystic", "subtle", "fine",
"mysterious", "marvelous", "wondrous", or "ineffable").

## What's it got?

So far, we are implementing an LCF-style kernel (which is, more or
less, done), tactics-style procedural proofs (which we have started
but not finished), and classical tableaux proof procedure (which is
done and tested against several of Pelletier's problems).

We intend to finish the LCF-style tactics, then implement a state
monad for tracking definitions, and then implement an Intuitionistic
tableaux proof procedure.

## How do I use it?

This is a literate program, and the TeX has been extracted already. If
you do not have Noweb on your system, then you can just run `make pdf`
to produce the literate program.

If you want to run the code, I have tested it with PolyML and Moscow ML.

For Moscow ML users: Simply open up a terminal, and 

```
~/myo/$ cd src
~/myo/src/$ rlwrap mosml
Moscow ML version 2.10
Enter `quit();' to quit.
- use "mosml.sml";
```

Then it will load all the code.

For PolyML users:

```
~/myo/$ cd src
~/myo/src/$ rlwrap poly
Poly/ML 5.9.1 Release (Git version v5.9.1-64-ga71e81c1)
> use "poly.sml";
```

Then it will load all the code.

You can run unit tests, if you're using MLton or Polymlb, as:

```
~/myo/$ mlbton test.mlb
~/myo/$ ./test
```

...and...

```
~/myo/$ polymlb test.mlb
~/myo/$ ./test
```

If you want to use Moscow ML's [MLB library](https://github.com/kfl/mosml/tree/13c581aec46eea134e478f2e2b6456278e36ecce/src/mosmlb),
then you need to add a subdirectory `/usr/local/lib/mosml/basis/` and
a file `/usr/local/lib/mosml/basis/basis.mlb` which will load all the
necessary Standard ML 1997 files. After doing this, you then run:

```
~/myo/$ camlrunm /usr/local/lib/mosml/mosmlb test.mlb
~/myo/$ test
```

## What? Why?

This is trying to play around with some simple programs suitable for
exploring the design space of proof assistants. That's the "What".

We're trying to see if Hilbert's finitary metatheory could be
developed in a more "friendly" way for this endeavour.

So this experiment adheres to the "letter of the law", in the sense
that it implements essentially the finitary metatheory of Hilbert's
programme. But it violates the "spirit of the law" in the sense that
Hilbert's finitary metatheory was essentially Primitive Recursive
Arithmetic (PRA) _because_ it was so simple it could easily be
justified by [informal] "intuition" alone...however, this proof
assistant is not so "self-evidently self-checkable".

The alternative would be some form of intuitionistic HOL, which would
not be finitary (since it facilitates nearly arbitrary recursive types
and recursion) but it would be simpler to a large degree. This would
be adhering to the "spirit of the law" but not the "letter".

## Some History and References

Feferman's FS0 (as discussed in his paper [Finitary inductively presented logics](https://math.stanford.edu/~feferman/papers/presentedlogics.pdf)) 
is essentially as strong as Primitive Recursive Arithmetic (PRA) but
more "user friendly" for investigating the foundations of Mathematics.

Sean Matthews did a lot of research in the early '90s about FS0 in
proof assistants.
