-- Intrinsically well-typed While syntax.

module WellTypedSyntax where

open import Library
open import AST using (Type; bool; int)

Cxt = List Type

Var : (Γ : Cxt) (t : Type) → Set
Var Γ t = t ∈ Γ

-- Context extensions.

CxtExt = Maybe Type

_▷_ : Cxt → CxtExt → Cxt
Δ ▷ nothing = Δ
Δ ▷ just t  = t ∷ Δ

-- Types that support arithmetic operations

data ArithType : Type → Set where
  int    : ArithType int

-- Arithmetical operators

data ArithOp (t : Type) : Set where
  plus minus : (a : ArithType t) → ArithOp t

-- Comparison operators

data CmpOp (t : Type) : Set where
  gt : (a : ArithType t) → CmpOp t

-- Logical operators

data LogicOp : Set where
  and : LogicOp

-- Binary Operators

data Op : (t t' : Type) → Set where
  arith : ∀{t} (op : ArithOp t) → Op t t
  cmp   : ∀{t} (op : CmpOp t) → Op t bool
  logic : (op : LogicOp) → Op bool bool

-- The signature is fixed in both expressions and statements.

-- Well-typed expressions: context is fixed.

data Exp (Γ : Cxt): Type → Set where
  eInt  : (i : ℤ)                                 → Exp Γ int
  eBool : (b : Bool)                              → Exp Γ bool
  eVar  : ∀{t}    (x : Var Γ t)                   → Exp Γ t
  eOp   : ∀{t t'} (op : Op t t') (e e' : Exp Γ t) → Exp Γ t'

-- Well-typed statements (might extend the context)

mutual

  data Stm (Γ : Cxt) : CxtExt → Set where
    sInit   : ∀{t}     (e : Exp (t ∷ Γ) t)                                → Stm Γ (just t)
    sAss    : ∀{t}     (x : Var Γ t) (e : Exp Γ t)                        → Stm Γ nothing
    sWhile  : ∀{Γ'}    (e : Exp Γ bool) (s  : Stms Γ Γ')                  → Stm Γ nothing
    sIfElse : ∀{Γ₁ Γ₂} (e : Exp Γ bool) (s₁ : Stms Γ Γ₁) (s₂ : Stms Γ Γ₂) → Stm Γ nothing

  data Stms (Γ : Cxt) : Cxt → Set where
    []  : Stms Γ Γ
    _∷_ : ∀{mt} (s : Stm Γ mt) {Γ′} (ss : Stms (Γ ▷ mt) Γ′) → Stms Γ Γ′

-- Stms can be concatenated.

_++ˢ_ : ∀{Γ Γ' Γ''} → Stms Γ Γ' → Stms Γ' Γ'' → Stms Γ Γ''
[]       ++ˢ ss' = ss'
(s ∷ ss) ++ˢ ss' = s ∷ (ss ++ˢ ss')

record Program : Set where
  constructor program
  field
    {Γ}     : Cxt
    theStms : Stms [] Γ
    theMain : Exp Γ int

-- Testing types

arithType? : ∀ t → Dec (ArithType t)
arithType? int    = yes int
arithType? bool   = no λ()

module TypeEq where

  _≟_ : (t t' : Type) → Dec (t ≡ t')
  bool   ≟ bool   = yes refl
  bool   ≟ int    = no λ()
  int    ≟ bool   = no λ()
  int    ≟ int    = yes refl


-- -}
