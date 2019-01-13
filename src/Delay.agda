-- The delay monad for potentially non-terminating computation.

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

later : ∀ {A i} → Delay i A → Delay (↑ i) A
later x .force = later' x

-- Example: non-termination.

never : ∀ {A i} → Delay A i
never .force = later' never

-- Monad instance.

private
  returnDelay : ∀{A i} → A → Delay i A
  returnDelay a .force = return' a

  bindDelay : ∀ {i A B} → Delay i A → (A → Delay i B) → Delay i B
  bindDelay m k .force = case m .force of λ where
    (return' a) → k a .force
    (later' m') → later' (bindDelay m' k)

instance
  functorDelay : ∀ {i} → Functor (Delay i)
  fmap {{functorDelay}} f mx = bindDelay mx (λ x → returnDelay (f x))

  applicativeDelay : ∀ {i} → Applicative (Delay i)
  pure  {{applicativeDelay}}       = returnDelay
  _<*>_ {{applicativeDelay}} mf mx = bindDelay mf (_<$> mx)

  monadDelay : ∀ {i} → Monad (Delay i)
  _>>=_ {{monadDelay}} = bindDelay

-- Unwinding the delay monad might not terminate.

{-# NON_TERMINATING #-}

runDelay : ∀{A} → Delay ∞ A → A
runDelay m = case m .force of λ where
  (return' a) → a
  (later' m') → runDelay m'

-- -}
-- -}
-- -}
-- -}
-- -}
