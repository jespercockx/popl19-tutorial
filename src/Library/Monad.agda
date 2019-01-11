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
