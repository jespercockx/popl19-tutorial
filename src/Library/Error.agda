
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
    functorError : ∀ {a} → Functor (Error {a})
    fmap {{functorError}} f (fail err) = fail err
    fmap {{functorError}} f (ok   a  ) = ok (f a)

    applicativeError : ∀ {a} → Applicative (Error {a})
    pure  {{applicativeError}}              = ok
    _<*>_ {{applicativeError}} (fail err) x = fail err
    _<*>_ {{applicativeError}} (ok   f  ) x = f <$> x

    monadError : ∀ {a} → Monad (Error {a})
    _>>=_ {{monadError}} (fail err) k = fail err
    _>>=_ {{monadError}} (ok   a  ) k = k a

  liftM2 : ∀ {ℓ} {A B C : Set ℓ} (f : A → B → C) → Error A → Error B → Error C
  liftM2 f m n = f <$> m <*> n

  throwError : ∀{a} {A : Set a} → E → Error A
  throwError = fail

  catchError : ∀{a} {A : Set a} → Error A → (E → Error A) → Error A
  catchError (fail e) h = h e
  catchError (ok a)   h = ok a
