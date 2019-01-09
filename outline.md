Agda tutorial at POPL 2019
==========================

Running example:

* type-checker and interpreter for simply typed language
* FFI binding to parser

Language: WHILE-language

1. What is Agda?
----------------

Agda is...

* A strongly typed functional programming language in the tradition of
  Haskell
* An interactive theorem prover in the tradition of Martin-Löf

Main features of Agda:

- Dependent types (= families of types indexed over terms of another
  type)
- Indexed datatypes and dependent pattern matching
- Termination checking and productivity checking
- An infinite universe hierachy, with support for universe
  polymorphism
- Record types with copattern matching (= defining programs in terms
  of possible observations)
- Coinductive datatypes (= types containing possibly infinite terms,
  such as streams)
- Sized types (= a type-directed approach for modular proofs of
  termination and productivity)
- Implicit arguments (with a constraint solver filling in implicit
  arguments automatically when they have a unique solution)
- Instance arguments for ad-hoc polymorphism (similar to Haskell's
  typeclasses)
- A module system with parametrized modules and module application (~
  ML functors)
- A FFI to Haskell

We will use many of these in the course of this tutorial!

**Interaction with the Emacs mode.** The main way to write Agda code is
through the Emacs mode which lets you write and edit code
interactively: Programs may contain holes (`?` or `{! !}`) and still
be typechecked (C-c C-l). The Agda mode gives information about the
type of each hole (C-c C-,) and allows you to interactively edit the
program, for example by *solving* a hole (C-c C-space), *refining* the
hole with a certain function applied to new holes (C-c C-r) or by
*case splitting* on a variable (C-c C-c).

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
- Extrinsic approach: first write the *program* as you would in, say, Haskell
  and then give a separate proof of correctness
- Intrinsic approach: first define a specific *type* that only allows
programs that satisfy the correctness properties and then write the
program that inhabits this type. The intrinsic approach is also called
**correct-by-construction** programming.

Example: division on natural numbers `Nat`:
- Extrinsic approach: first implement functions `_/_ : Nat → Nat →
  Nat` and `_%_ : Nat → Nat → Nat` and then give separate proofs that
  `x ≡ y * (x / y) + x % y` and `x % y < y`.
- Intrinsic approach: first define a type `Quot x y` consisting of two
  numbers `p q : Nat` together with proofs of `x ≡ y * p + q` and `q <
  y` and then implement a function `quotient : (x y : Nat) → Quot x
  y`. `_/_` and `_%_` can then be defined as the first and second
  projections from this type.

In this tutorial, we apply correct-by-construction programming to the
construction of a typechecker and interpreter for a simple C-like
language called WHILE (see src/While.cf for the syntax).

3. Simple data types and pattern matching
-----------------------------------------

**Theory**:
- A (simple) datatype is defined by zero or more constructors
- Each constructor is of a function type ending in the datatype
- Syntax: similar to GADT's in Haskell
- Examples: ⊥, Nat, Brouwer ordinals
- Datatypes must be *strictly positive*: the datatype cannot occur to
  the left of an arrow in the recursive arguments of a constructor.
- Functions are defined using pattern matching, i.e. by giving a
  complete set of clauses (computation rules) that the function should
  satisfy.

**Example code**: abstract syntax, untyped interpreter (see files
  AST.agda & UntypedInterpreter.agda).

Note on termination checking: all functions in Agda are checked to be
terminating. Since it is possible to write non-terminating programs in
our WHILE language, the evaluator takes an extra argument called the
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
generator via the Haskell FFI.

**Theory**:
- To use a Haskell file from Agda, we first need to import it using a
  {-# FOREIGN GHC import<HaskellModule> #-} pragma.
- To import a Haskell function in Agda, we first postulate it in Agda
  and then associate it to the Haskell function using a {-# COMPILE
  GHC <Name> = <HaskellCode> #-} pragma.
- To import a Haskell datatype in Agda, we first mirror the definition
  of the datatype in Agda and then bind it to the Haskell datatype
  using a {-# COMPILE GHC <Name> = data <HaskellData> (<HsCon1> | .. |
  <HsConN>) #-} pragma

**Example code**: see While.cf, Main.hs, Parser.agda

**Exercise**: Update the grammar with the features you added in the
  previous step.

TODO: add a parse-only mode so it is possible to test the program
already?

5. Dependent types and indexed datatypes
----------------------------------------

**Theory**:
- Indexed datatypes are families of datatypes indexed over some base
  type(s). Example: Vectors
- Syntax: similar to GADT's in Haskell
- When defining functions by pattern matching on an argument of an
  indexed datatype, some of the other arguments may be
  specialized. For example, if `x : Vec A n` is `x ∷ xs`, then we know
  that `n = suc m` where `xs : Vec A m`. These specialized arguments
  are written as *dot patterns* (example: vector concatenation).
- Sometimes one or more cases of an indexed datatype are ruled out,
  for example when defining a function taking an argument of type `Vec
  A 0` there is only a case for `[]` but not for `x ∷ xs`. If all
  cases are ruled out we can use the special *absurd pattern* `()`.

**Example code**: see WellTypedSyntax.agda

**Exercise**: add well-typed syntax for the new additions to the
  language.

6. Monads, instance arguments, and do-notation
----------------------------------------------

**Theory**: *Instance arguments* are Agda's builtin mechanism for
 ad-hoc overloading (serving a similar role as type classes in
 Haskell).

 * First, we define a record type containing a field for each method
   of the typeclass (as in the dictionary translation of typeclasses)
 * Next, we declare all fields of the record type as being eligible
   for instance search using the special statement `open <TypeClass>
   {{...}}`.
 * We can define new instances of the typeclass by defining elements
   of the record type (using copatterns) and marking them with the
   `instance` keyword.
 * Functions that use methods from the typeclass should take an extra
   argument of the record type as an instance argument (using {{_ :
   R}} syntax).
 * When using a function, instance arguments are automatically
   resolved if there is a unique instance of the appropriate type in
   scope.

 See Library/Print.agda for a simple example, and Library.agda for
 some example instances. A more elaborate example showcasing multiple
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
values, such as Streams.

* A coinductive type is defined as a recursive record type with the
  special `coinductive` keyword.
* To define an element of a coinductive type, we give all of its
  possible *observations* (i.e. fields of the record type).
* By default, recursive calls should be *guarded* by
  constructors. Since this is often quite limiting, coinductive types
  are often defined as *sized types*.

A simple general-purpose coinductive type is
the Delay type: a value of type Delay A is either a value of type A
which is produced now, or a value of type Delay A which is produced
later, possibly at nauseam (see Delay.agda).

**Example code**: see Delay.agda, Interpreter.agda

**Exercise**: update the well-typed evaluator to deal with the new
  additions to the language.
