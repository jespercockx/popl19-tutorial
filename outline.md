Agda tutorial at POPL 2019
==========================

Running example:

* type-checker and interpreter for simple typed language
* FFI binding to parser

Language: WHILE-language

1. What is Agda?
----------------

Agda is...

* A strongly typed functional programming language in the tradition of
  Haskell
* An interactive theorem prover in the tradition of Martin-Löf

The main way to write Agda code is through the Emacs mode which lets
you write and edit code interactively: Incomplete programs may contain
holes, the Agda mode gives information about the type of each hole and
allows you to interactively edit the program, for example by
*refining* the hole or by *case splitting* on a variable.

**Installation**:

* Agda: Assuming you are working on Linux and already have
  Haskell, a simple 'cabal install agda && agda-mode setup' should be
  sufficient (it's possible you need some of the following packages:
  alex happy epic zlib1g-dev libgc-dev libicu-dev).  For further
  instructions, see
  https://agda.readthedocs.io/en/v2.5.4.1/getting-started/installation.html

* Standard library: See
  https://github.com/agda/agda-stdlib#quick-installation-instructions

* BNFC: For this tutorial, you also need to install the bnfc package
  from Cabal.

2. Correct-by-construction programming
--------------------------------------

The main reason to use a dependently typed programming language is to
write programs that can statically be verified to satisfy a given
correctness property. In contrast to most code verification tools,
verification is not done by a separate tool but built into the
language itself.

Agda allows two approaches to implement verified programs:
- Extrinsic approach: first write the program as you would in Haskell
  and then give a separate proof of correctness
- Intrinsic approach: first define a specific *type* that only allows
programs that satisfy the correctness properties and then write the
program that inhabits this type The intrinsic approach is also called
**correct-by-construction** programming.

Example: division on natural numbers Nat:
- Extrinsic approach: ...
- Intrinsic approach: ...

In this tutorial, we apply correct-by-construction programming to the
construction of a typechecker and interpreter for a simple C-like
language (see src/While.cf for the syntax).

3. Simple data types and pattern matching
-----------------------------------------

**Example code**: abstract syntax, untyped interpreter (see files
  AST.agda & UntypedInterpreter.agda).

Note on termination checking: all functions in Agda are checked to be
terminating. Since it is possible to write non-terminating programs in
our While language, the evaluator takes an extra argument called the
'fuel' (a natural number), which represents the number of steps before
the evaluator gives up. Later we will see a better approach to deal
with non-termination in Agda, the Delay monad.

**Exercise**: add the following language constructions: boolean
  conjunction ('and'), integer subtraction ('minus'), conditionals
  ('if/then/else'). (TODO: remove these from the provided code)
  Also update the functions in 

4. BNFC and the Haskell FFI
----------------------------------------

Compared to Haskell, the Agda ecosystem is still rather
small. However, we can piggyback on the Haskell ecosystem using FFI
bindings. For parsing our While language, we use the BNFC parser
generator via the Haskell FFI

**Example code**: see While.cf, Main.hs, Parser.agda

**Exercise**: Update the grammar with the features you added in the
  previous step.

TODO: add a parse-only mode so it is possible to test the program
already?

5. Dependent types and indexed datatypes
----------------------------------------

**Example code**: see WellTypedSyntax.agda

**Exercise**: add well-typed syntax for the new additions to the
  language.

6. Monads, instance arguments, and do-notation
----------------------------------------------

*Instance arguments* are Agda's builtin mechanism for ad-hoc
 overloading (serving a similar role as type classes in Haskell).  See
 Library/Print.agda for a simple example, and Library.agda for some
 example instances. A more elaborate example showcasing multiple
 methods and superclasses can be found in Library/Monad.agda.

**Example code**: see TypeChecker.agda

**Exercise**: update the typechecker to deal with the new additions to
  the language.

7. Coinduction and sized types
------------------------------

We saw one crude way to deal with possibly infinite computations in
Agda in UntypedInterpreter.agda: use a 'fuel' arguments which encodes
the number of steps we can still take. A much better way is to use a
*coinductive type*, i.e. a type which may contain possibly infinite
values, such as Streams. A simple general-purpose coinductive type is
the Delay type: a value of type Delay A is either a value of type A
which is produced now, or a value of type Delay A which is produced
later, possibly at nauseam (see Delay.agda). 

**Example code**: see Interpreter.agda

**Exercise**: update the well-typed evaluator to deal with the new
  additions to the language.