
open import Library.Monad

open import Level

module Library.Error where

open import Data.Sum.Base using (_⊎_; inj₁; inj₂)

module ErrorMonad {e} {E : Set e} where

  Error : ∀{a} (A : Set a) → Set (e ⊔ a)
  Error A = E ⊎ A

  pattern fail err = inj₁ err
  pattern ok   val = inj₂ val

  instance
    FunctorError : ∀ {a} → Functor (Error {a})
    FunctorError .fmap f (fail err) = fail err
    FunctorError .fmap f (ok   a  ) = ok (f a)

    ApplicativeError : ∀ {a} → Applicative (Error {a})
    ApplicativeError .pure               = ok
    ApplicativeError ._<*>_ (fail err) x = fail err
    ApplicativeError ._<*>_ (ok   f  ) x = f <$> x

    MonadError : ∀ {a} → Monad (Error {a})
    MonadError ._>>=_ (fail err) k = fail err
    MonadError ._>>=_ (ok   a  ) k = k a

  liftM2 : ∀ {ℓ} {A B C : Set ℓ} (f : A → B → C) → Error A → Error B → Error C
  liftM2 f m n = f <$> m <*> n

  throwError : ∀{a} {A : Set a} → E → Error A
  throwError = fail

  catchError : ∀{a} {A : Set a} → Error A → (E → Error A) → Error A
  catchError (fail e) h = h e
  catchError (ok a)   h = ok a
