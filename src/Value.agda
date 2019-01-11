-- Values and primitive operations; environments.

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

-- Well-typed Environments.

Env : Cxt → Set
Env = List.All Val

-- Semantics of operations.

-- Boolean negation.

bNot : Boolean → Boolean
bNot true  = false
bNot false = true

-- Greater-than on integers.

iGt : (i j : ℤ) → Boolean
iGt i j = case i Integer.<= j of λ where
  false → true
  true  → false
