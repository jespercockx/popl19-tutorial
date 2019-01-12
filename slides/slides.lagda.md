
---
title: "Correct-by-construction programming in Agda"
subtitle: "Tutorial at POPL 2019"
author: "Andreas Abel and Jesper Cockx"
date: "January 14 2019"

transition: "linear"
center: "true"
width: "1280"
height: "720"
margin: "0.2"
---

# Introduction to Agda

## What is Agda?

Agda is...

* A strongly typed functional programming language in the tradition of
  Haskell
* An interactive theorem prover in the tradition of Martin-Löf

## Main features of Agda

- Dependent types
- Indexed datatypes and dependent pattern matching
- Termination checking and productivity checking
- A universe hierachy with universe polymorphism
- Record types with copattern matching
- Coinductive datatypes
- Sized types
- Implicit arguments
- Instance arguments (~ Haskell's typeclasses)
- Parametrized modules (~ ML functors)
- A FFI to Haskell

We will use many of these in the course of this tutorial!

## Emacs mode for Agda

Programs may contain **holes** (`?` or `{! !}`).

- **`C-c C-l`**: typecheck and highlight the current file
- **`C-c C-,`**: get information about the hole under the cursor
- **`C-c C-space`**: give a solution
- **`C-c C-r`**: *refine* the hole
  * Introduce a lambda or constructor
  * Apply given function to some new holes
- **`C-c C-c`**: case split on a variable

## Installation

Agda: `cabal install agda && agda-mode setup`

Standard library: see [github.com/agda/agda-stdlib](https://github.com/agda/agda-stdlib#quick-installation-instructions)

BNFC: `cabal install bnfc`

# Correct-by-construction programming

## Why use dependent types?

With dependent types, we can **statically verify** that a program satisfies a given correctness property.

Verification is **built into** the language itself.

## Two approaches to verification with dependent types:

- **Extrinsic approach**: first write the program and then prove
    correctness
- **Intrinsic approach**: first define the *type* of programs that
  satisfy the correctness property and then write the program that
  inhabits this type

The intrinsic approach is also called **correct-by-construction** programming.

## Example of extrinsic verification
<!--
```agda
{-# OPTIONS --guardedness --sized-types #-}

open import Data.List.Base using (List; []; _∷_)
open import Data.Maybe.Base using (Maybe; nothing; just)
open import Data.Nat.Base using (ℕ; zero; suc; _+_; _*_; _<_)
open import Data.Product using (_×_; _,_)
open import Agda.Builtin.Equality using (_≡_; refl)

postulate
  ⋯ : ∀ {ℓ} {A : Set ℓ} → A

module Intro where
```
-->

```agda
  module Extrinsic where
    _/_ : ℕ → ℕ → ℕ
    k / l = ⋯

    _%_ : ℕ → ℕ → ℕ
    k % l = ⋯

    divmod-lemma : ∀ {k l} → l * (k / l) + k % l ≡ k
    divmod-lemma = ⋯

    divmod-minimal : ∀ {k l} → k % l < l
    divmod-minimal = ⋯
```

## Example of intrinsic verification
```agda
  module Intrinsic where
    record Quotient (k l : ℕ) : Set where
      field
        q r     : ℕ
        divmod  : l * q + r ≡ k
        minimal : r < l

    quotient : (k l : ℕ) → Quotient k l
    quotient = ⋯

    _/_ : ℕ → ℕ → ℕ
    k / l = Quotient.q (quotient k l)

    _%_ : ℕ → ℕ → ℕ
    k % l = Quotient.r (quotient k l)
```

## Correct-by-construction programming

≠ verifying *all* properties we want

= verifying as many properties as we can get *for free*

## Goal of this tutorial

Implement a correct-by-construction **typechecker** + **interpreter** for a C-like language (WHILE)
```c
int main () {
  int n = 100;
  int sum = 0;
  while (n > 0) {
    sum = sum + n;
    n = n - 1;
  }
  printInt(sum);
}
```

## Structure of a WHILE program
```c
int main () {
  <type> var₁ = expr₁;
  ...
  <type> varₘ = exprₘ;
  stmt₁
  ...
  stmtₙ
  printInt(expr);
}
```

# Simple data types and pattern matching

## Some simple Agda datatypes

<!--
```agda
module SimpleData where
```
-->

```agda
  data Bool : Set where
    true false : Bool

  data Nat : Set where
    zero : Nat
    suc  : Nat → Nat

  data Ord : Set where
    zero : Ord
    suc  : Ord → Ord
    sup  : (Nat → Ord) → Ord

  data ⊥ : Set where
    -- no constructors
```

## Pattern matching in Agda
```agda
  not : Bool → Bool
  not true  = false
  not false = true

  max : Nat → Nat → Nat
  max zero    l       = l
  max k       zero    = k
  max (suc k) (suc l) = suc (max k l)

  magic : {A : Set} → ⊥ → A
  magic ()
```

## Type and expression syntax for WHILE

<!--
```agda
  postulate
    Id ℤ Boolean : Set
```
-->

```agda
  data Type : Set where
    bool int : Type

  data Exp : Set where
    eId   : (x : Id)      → Exp  -- x,y,z,...
    eInt  : (i : ℤ)       → Exp  -- ...-2,-1,0,1,2...
    eBool : (b : Boolean) → Exp  -- true or false
    ePlus : (e e' : Exp)  → Exp  -- x+y
    eGt   : (e e' : Exp)  → Exp  -- x>y
    eAnd  : (e e' : Exp)  → Exp  -- x&&y
```

## Statement syntax for WHILE

```agda
  data Stm : Set where
    sAss   : (x : Id) (e : Exp)        → Stm
      -- ^ x = e;
    sWhile : (e : Exp) (ss : List Stm) → Stm
      -- ^ while (b) { ... }
```

## Program syntax for WHILE

```agda
  record Decl : Set where
    constructor dInit   -- <type> x = e;
    field
      declType : Type   -- variable type
      declId   : Id     -- variable name (x)
      declExp  : Exp    -- initial value (e)
  open Decl public

  record Program : Set where
    constructor program
    field
      theDecls : List Decl
      theStms  : List Stm
      theMain  : Exp
  open Program public
```

## Untyped interpreter

File `UntypedInterpreter.agda` defines an *untyped* interpreter for WHILE:

```agda
  data Val : Set where
    intV  : ℤ       → Val
    boolV : Boolean → Val

  Env : Set
  Env = List (Id × Val)

  eval : Env → Exp → Maybe Val
  eval ρ e = ⋯

  execDecl : Decl → Env → Maybe Env
  execDecl d ρ = ⋯
```

## Untyped interpreter (continued)

All Agda functions must be **total**

But WHILE programs can loop!

⇒ we must limit the number of times we repeat the loop

```agda
  execStm : (fuel : ℕ) → Stm → Env → Maybe Env
  execStm fuel stm ρ = ⋯

  evalPrg : (fuel : ℕ) → Program → Maybe ℤ
  evalPrg fuel (program ds ss e) = ⋯
```

## Exercise #1

Go to `AST.agda` and extend the syntax with one or more of the following:

- Boolean negation `!x`
- Integer subtraction `x-y`
- Conditionals `if (x) { d₁ } else { d₂ }

Ignore the pragmas `{-# COMPILE ... #-}` for now.

Also go to `UntypedInterpreter.agda` and add the missing cases!

# Haskell FFI

## Haskell FFI: basics

<!--
```agda
module FFI where
```
-->

Import a Haskell module:
```agda
  {-# FOREIGN GHC import HaskellModule.hs #-}
```

Bind Haskell function to Agda name:
<!--
```
  postulate AgdaType : Set
```
-->
```agda
  postulate agdaName : AgdaType
  {-# COMPILE GHC agdaName = haskellCode #-}
```

Bind Haskell datatype to Agda datatype:
```
  data D : Set where c₁ c₂ : D
  {-# COMPILE GHC D = data hsData (hsCon₁ | hsCon₂) #-}
```

## Haskell FFI example:
```haskell
  -- In file `While/Abs.hs`:
  data Type = TBool | TInt
```
```agda
  -- In file `AST.agda`:
  {-# FOREIGN GHC import While.Abs #-}
  data Type : Set where
    bool int : Type

  {-# COMPILE GHC Type = data Type
    ( TBool
    | TInt
    ) #-}
```

## BNFC: the Bachus-Nauer Form Compiler

BNFC is a Haskell library for generating Haskell code from a grammar:

- Datatypes for abstract syntax
- Parser
- Pretty-printer

See `While.cf` for the grammar of WHILE.

## Exercise #2

Extend the BNFC grammar with the new syntactic constructions you added.

Don't forget to update the Haskell bindings in `AST.agda`!

Testing the grammar: `make parser` will compile the parser and run it on `/test/fib.c`.

# Dependent types and indexed datatypes

## Indexed datatypes

**Indexed datatype** = family of datatypes indexed over some base type
<!--
```agda
module IndexedData where
  open import Data.Nat.Base
  open import Data.Integer.Base using (ℤ)
  open import Data.List.Membership.Propositional using (_∈_; _∉_)
  open import Data.List.All using (All; []; _∷_) hiding (module All)
  open FFI using (Type; int; bool)

  data Boolean : Set where BTrue BFalse : Boolean
```
-->
```agda
  data Vec (A : Set) : ℕ → Set where
    []  : Vec A zero
    _∷_ : {n : ℕ} → A → Vec A n → Vec A (suc n)
```
(like GADTs in Haskell)

## Dependent pattern matching

```agda
  _++_ : {A : Set} {m n : ℕ}
       → Vec A m → Vec A n → Vec A (m + n)
  []       ++ ys = ys              -- m = zero
  (x ∷ xs) ++ ys = x ∷ (xs ++ ys)  -- m = suc m′

  head : {A : Set} {n : ℕ} → Vec A (suc n) → A
  -- head []         -- Impossible!
  head (x ∷ xs) = x
```

## Well-typed syntax representation

Our correct-by-construction typechecker produces **intrinsically well-typed syntax**:

```
  Cxt = List Type

  data Exp (Γ : Cxt) : Type → Set
```

A term `e : Exp Γ t` is a *well-typed* WHILE expression in context `Γ`.

## Well-typed syntax

```agda
  Var : (Γ : Cxt) (t : Type) → Set
  Var Γ t = t ∈ Γ

  data Op : (dom codom : Type) → Set where
    plus  : Op int  int
    gt    : Op int  bool
    and   : Op bool bool

  data Exp Γ where
    eInt  : (i : ℤ)            → Exp Γ int
    eBool : (b : Boolean)      → Exp Γ bool
    eOp   : ∀{t t'} (op : Op t t')
          → (e e' : Exp Γ t)   → Exp Γ t'
    eVar  : ∀{t} (x : Var Γ t) → Exp Γ t
```
see `WellTypedSyntax.agda`

## Evaluating well-typed syntax

We can now define `eval` for well-typed expressions:
```
  Val : Type → Set
  Val int    = ℤ
  Val bool   = Boolean

  Env : Cxt → Set
  Env = All Val

  eval : ∀ {Γ} {t} → Env Γ → Exp Γ t → Val t
  eval = ⋯
```
that **always** returns a value (bye bye `Maybe`!)

See definition of `eval` in `Interpreter.agda`.

## Exercise #3

Extend the well-typed syntax with the new syntactic constructions you added.

# BREAK (30 min)

# Monads and instance arguments

## Instance arguments

*Instance arguments* are Agda's builtin mechanism for
 ad-hoc overloading (~ type classes in Haskell).

Syntax:

- Using an instance: `{{x : A}} → ...`
- Defining new instances: `instance ...`

When using a function of type `{{x : A}} → B`, Agda will automatically
resolve the argument if there is a **unique** instance of the
right type in scope.


## Defining a typeclass with instance arguments

<!--
```agda
module Instances where
  open import Data.Bool.Base
  open import Data.String.Base
```
-->

```agda
  record Print {ℓ} (A : Set ℓ) : Set ℓ where
    field
      print : A → String
  open Print {{...}}  -- print : {{r : Print A}} → A → String

  instance
    PrintBool : Print Bool
    PrintBool .print true  = "true"
    PrintBool .print false = "false"

    PrintString : Print String
    PrintString .print x = x

  testPrint : String
  testPrint = (print true) ++ (print "a string")
```

## Monads

`Monad` is a typeclass with two fields `return` and `_>>=_`.

Example: `Error` monad (see `Library/Error.agda`)

## Correct-by-construction typechecker

See `TypeChecker.agda`

## Exercise #4

Extend the typechecker with rules for the new syntactic constructions you added.

# Coinduction and sized types

## Coinduction in Agda

Coinductive type = type containing infinite values
<!--
```agda
module Coinduction where
  module GuardedStream where
```
-->
```agda
    record Stream (A : Set) : Set where
      coinductive
      field
        head : A
        tail : Stream A
    open Stream

    repeat : {A : Set} → A → Stream A
    repeat x .head = x
    repeat x .tail = repeat x
```

## Dealing with infinite computations

Remember: all Agda functions must be **total**

⇒ interpreter for WHILE takes `fuel` argument

Can we do better?

## Going carbon-free with the `Delay` monad

**Monads** allow us to use effects in a pure language

The `Delay` monad captures the effect of *non-termination*

A value of type `Delay A` is
- either a value of type `A` produced **now**
- or a computation of type `Delay A` produced **later**

## The Delay monad: definition

```agda
  mutual
    record Delay (A : Set) : Set where
      coinductive
      field force : Delay' A

    data Delay' (A : Set) : Set where
      now   : A       → Delay' A
      later : Delay A → Delay' A

  open Delay public

  never : {A : Set} → Delay A
  never .force = later never
```

## Sized types

Totality requirement: coinductive definitions should be **productive**:
computing each observation should be terminating.

To ensure this, Agda checks that corecursive calls are **guarded by constructors**, but this is often quite limiting.

A more flexible and modular approach is to use **sized types**.

## The type `Size`

`Size` ≃ abstract version of the natural numbers extended with `∞`

For each `i : Size`, we have a type `Size< i` of sizes **smaller than `i`**.

**Note**: pattern matching on `Size` is not allowed!

## The sized delay monad

<!--
```agda
module SizedTypes where
  open import Size
```
-->

```agda
  mutual
    record Delay (i : Size) (A : Set) : Set where
      coinductive
      constructor delay
      field
        force : {j : Size< i} → Delay' j A

    data Delay' (i : Size) (A : Set) : Set where
      return' : A         → Delay' i A
      later'  : Delay i A → Delay' i A
```
`i` ≃ how many more steps are we allowed to observe.

`Delay ∞ A` is the type of computations that can take *any* number of steps.

## Interpreting well-typed WHILE programs

WHILE statements can have two effects:

- Modify the environment   ⇒ `State` monad
- Go into an infinite loop ⇒ `Delay` monad

We combine both effects in the `Exec` monad.

## The `Exec` monad

<!--
```agda
  open import Data.Unit
  open import Data.Integer.Base
  open IndexedData
  postulate
    Stm : Cxt → Set
    Program : Set
```
-->

```agda
  record Exec {Γ : Cxt} (i : Size) (A : Set) : Set where
    field
      runExec : (ρ : Env Γ) → Delay i (A × Env Γ)
  open Exec public

  execStm : ∀ {Γ} {i} (s : Stm Γ) → Exec {Γ} i ⊤
  execStm = ⋯

  execPrg : ∀ {i} (prg : Program) → Delay i ℤ
  execPrg prg = ⋯
```
See `Interpreter.agda` for full code

## Exercise #5

Extend the interpreter with rules for the new syntactic constructions you added.
