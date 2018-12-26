module Delay where

open import Library
open import Category.Monad
open import Category.Applicative.Indexed

-- Coinductive delay monad.

mutual

  record Delay (i : Size) (A : Set) : Set where
    coinductive
    constructor delay
    field
      force : {j : Size< i} → Delay' j A

  data Delay' (i : Size) (A : Set) : Set where
    return' : A         → Delay' i A
    later'  : Delay i A → Delay' i A

open Delay public

-- Smart constructor.

return : ∀{A i} → A → Delay i A
return a .force = return' a

later : ∀ {A i} → Delay i A → Delay (↑ i) A
later x .force = later' x

-- Example: non-termination.

never : ∀ {A i} → Delay A i
never .force = later' never

-- Monad instance.

infixl 10 _>>=_

_>>=_ : ∀ {i A B} → Delay i A → (A → Delay i B) → Delay i B
(m >>= k) .force = case m .force of λ where
  (return' a) → k a .force
  (later' m') → later' (m' >>= k)

delayMonad : ∀ {i} → RawMonad (Delay i)
delayMonad {i} = record
  { return = return
  ; _>>=_  = _>>=_ {i}
  }

-- Functor and applicative.

module _ {i : Size} where
  open module DelayMonad = RawMonad (delayMonad {i = i})
                           public using (_<$>_) renaming (_⊛_ to _<*>_)

-- -}
-- -}
-- -}
-- -}
-- -}
