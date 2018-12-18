module Delay where

open import Library
open import Category.Monad
open import Category.Applicative.Indexed

-- Coinductive delay monad.

mutual

  data Delay (i : Size) (A : Set) : Set where
    now   : A          → Delay i A
    later : ∞Delay i A → Delay i A

  record ∞Delay (i : Size) (A : Set) : Set where
    coinductive
    constructor delay
    field
      force : {j : Size< i} → Delay j A

open ∞Delay public

-- Smart constructor.

later! : ∀ {A i} → Delay i A → Delay (↑ i) A
later! x = later (delay x)

-- Example: non-termination.

never : ∀ {A i} → ∞Delay A i
force never = later never

-- Monad instance.

module Bind where

  infixl 10 _>>=_  _∞>>=_

  mutual
    _>>=_ : ∀ {i A B} → Delay i A → (A → Delay i B) → Delay i B
    now   x >>= f = f x
    later x >>= f = later (x ∞>>= f)

    _∞>>=_ :  ∀ {i A B} → ∞Delay i A → (A → Delay i B) → ∞Delay i B
    force (x ∞>>= f) = force x >>= f

delayMonad : ∀ {i} → RawMonad (Delay i)
delayMonad {i} = record
  { return = now
  ; _>>=_  = _>>=_ {i}
  } where open Bind

module _ {i : Size} where
  open module DelayMonad = RawMonad (delayMonad {i = i})
                           public renaming (_⊛_ to _<*>_)
open Bind public using (_∞>>=_)

-- Map for ∞Delay

_∞<$>_ : ∀ {i A B} (f : A → B) (∞a : ∞Delay i A) → ∞Delay i B
f ∞<$> ∞a = ∞a ∞>>= λ a → return (f a)
-- force (f ∞<$> ∞a) = f <$> force ∞a


_∞<*>_ : ∀ {i A B} (f : ∞Delay i (A → B))(a : Delay i A) → ∞Delay i B
f ∞<*> a = f ∞>>= λ f → f <$> a
-- Double bind

_=<<2_,_ : ∀ {i A B C} → (A → B → Delay i C) → Delay i A → Delay i B → Delay i C
f =<<2 x , y = x >>= λ a → y >>= λ b → f a b
