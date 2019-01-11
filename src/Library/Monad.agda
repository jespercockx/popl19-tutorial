-- Monads and (applicative) functors.

module Library.Monad where

open import Agda.Primitive
open import Agda.Builtin.Unit

-- Functor type class.

record Functor {a b} (F : Set a → Set b) : Set (lsuc a ⊔ b) where
  infixl 4 _<$>_
  field
    fmap : ∀ {A B} → (A → B) → F A → F B
  _<$>_ = fmap

open Functor {{...}} public

-- Indexed applicative functors.

record IApplicative {i a b} {I : Set i} (F : I → I → Set a → Set b) : Set (i ⊔ lsuc a ⊔ b) where
  infixl 4 _<*>_
  field
    pure  : ∀ {i A} → A → F i i A
    _<*>_ : ∀ {i j k A B} → F i j (A → B) → F j k A → F i k B
    overlap {{super}} : ∀ {i j} → Functor (F i j)

open IApplicative {{...}} public

-- Applicative functors (IApplicative with trivial index type).

Applicative : ∀ {a b} (M : Set a → Set b) → Set (lsuc a ⊔ b)
Applicative F = IApplicative {I = ⊤} (λ _ _ → F)

-- Indexed monads.

record IMonad {i a b} {I : Set i} (M : I → I → Set a → Set b) : Set (i ⊔ lsuc a ⊔ b) where
  infixl 1 _>>=_ _>>_
  infixr 1 _=<<_
  field
    _>>=_ : ∀ {i j k A B} → M i j A → (A → M j k B) → M i k B
    overlap {{super}} : IApplicative {I = I} M

  return : ∀ {i A} → A → M i i A
  return = pure

  _>>_ : ∀ {i j k A B} → M i j A → M j k B → M i k B
  m₁ >> m₂ = m₁ >>= λ _ → m₂

  _=<<_ : ∀ {i j k A B} → (A → M j k B) → M i j A → M i k B
  f =<< m = m >>= f

open IMonad {{...}} public

-- Monads (IMonad with trivial index type).

Monad : ∀ {a b} (M : Set a → Set b) → Set (lsuc a ⊔ b)
Monad M = IMonad {I = ⊤} (λ _ _ → M)

-- Instances for basic types

module ErrorMonad {e} {E : Set e} where

  open import Data.Sum.Base using (_⊎_; inj₁; inj₂)

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

module IOMonad where

  open import IO.Primitive as IO using (IO) public

  instance
    FunctorIO : ∀ {a} → Functor (IO {a})
    FunctorIO .fmap f mx = mx IO.>>= λ x → IO.return (f x)

    ApplicativeIO : ∀ {a} → Applicative (IO {a})
    ApplicativeIO .pure        = IO.return
    ApplicativeIO ._<*>_ mf mx = mf IO.>>= λ f → f <$> mx

    MonadIO : ∀ {a} → Monad (IO {a})
    MonadIO ._>>=_ = IO._>>=_
