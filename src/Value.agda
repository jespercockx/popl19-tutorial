-- Common definitions for operational semantics and interpreter.

module Value where

open import Library
open import WellTypedSyntax

-- Well-typed values.

Val : Type → Set
Val int    = ℤ
Val bool   = Boolean

instance
  PrintVal : ∀ {t} → Print (Val t)
  PrintVal {int}  .print i = print {{PrintInt}} i
  PrintVal {bool} .print b = print {{PrintBoolean}} b

Env : Cxt → Set
Env = List.All Val

-- Semantics of operations.

bNot : Boolean → Boolean
bNot true = false
bNot false = true

iGt : (i j : ℤ) → Boolean
iGt i j = case i Integer.<= j of λ where
  false → true
  true  → false

iArith : (op : ArithOp) (i j : ℤ) → ℤ
iArith plus  i j = i Integer.+ j
iArith minus i j = i Integer.- j
