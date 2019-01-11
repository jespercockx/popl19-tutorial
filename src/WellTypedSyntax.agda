-- Intrinsically well-typed WHILE syntax.

module WellTypedSyntax where

open import Library
open import AST public using (Type; bool; int; Boolean; true; false; PrintBoolean)

-- Variables are de Bruijn indices into the context, a list of types.

Cxt = List Type

Var : (Γ : Cxt) (t : Type) → Set
Var Γ t = t ∈ Γ

-- Binary Operators.

data Op : (dom codom : Type) → Set where
  plus  : Op int  int
  gt    : Op int  bool
  and   : Op bool bool

-- Well-typed expressions: context is fixed.

data Exp (Γ : Cxt) : Type → Set where
  -- Literals:
  eInt  : (i : ℤ)                                 → Exp Γ int
  eBool : (b : Boolean)                           → Exp Γ bool
  -- Operators:
  eOp   : ∀{t t'} (op : Op t t') (e e' : Exp Γ t) → Exp Γ t'
  -- Variables:
  eVar  : ∀{t}    (x : Var Γ t)                   → Exp Γ t

-- Well-typed declarations (extending the context).

data Decl (Γ : Cxt) (t : Type) : Set where
  dInit : (e : Exp Γ t) → Decl Γ t

data Decls (Γ : Cxt) : Cxt → Set where
  []  : Decls Γ Γ
  _∷_ : ∀{t Γ′} (s : Decl Γ t) (ss : Decls (t ∷ Γ) Γ′) → Decls Γ Γ′

-- Well-typed statements.

mutual

  data Stm (Γ : Cxt) : Set where
    sAss    : ∀{t} (x : Var Γ t) (e : Exp Γ t)               → Stm Γ
    sWhile  : ∀ (e : Exp Γ bool) (s  : Stms Γ)               → Stm Γ
    sIfElse : ∀ (e : Exp Γ bool) (s₁ : Stms Γ) (s₂ : Stms Γ) → Stm Γ

  Stms : Cxt → Set
  Stms Γ = List (Stm Γ)

-- A program is a list of statements and a final expression.

record Program : Set where
  constructor program
  field
    {Γ}      : Cxt
    theDecls : Decls [] Γ
    theStms  : Stms Γ
    theMain  : Exp Γ int

open Program public


-- -}
