
module Library.Eq where

open import Data.Bool.Base using (Bool)
open import Data.Char
import Data.Char.Unsafe
open import Data.Integer using (ℤ)
open import Data.List.Base using (List; []; _∷_)
open import Data.String using (String)
import Data.String.Unsafe

open import Data.Product using (_×_; _,_)

open import Function using (case_of_)

open import Relation.Binary using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)

-- Type class for decidable equality.

record Eq {ℓ} (A : Set ℓ) : Set ℓ where
  field
    _≟_ : Decidable (_≡_ {A = A})

  _==_ : A → A → Bool
  x == y = ⌊ x ≟ y ⌋

open Eq {{...}} public

-- Instances for basic types

instance
  EqBool : Eq Bool
  EqBool ._≟_ = Data.Bool.Base._≟_

instance
  Eqℤ : Eq ℤ
  Eqℤ ._≟_ = Data.Integer._≟_

instance
  EqChar : Eq Char
  EqChar ._≟_ = Data.Char.Unsafe._≟_

instance
  EqString : Eq String
  EqString ._≟_ = Data.String.Unsafe._≟_

instance
  EqList : ∀ {ℓ} {A : Set ℓ} {{_ : Eq A}} → Eq (List A)
  EqList ._≟_ = λ where
    []       []       → yes refl
    []       (y ∷ ys) → no λ ()
    (x ∷ xs) []       → no λ ()
    (x ∷ xs) (y ∷ ys) → case (x ≟ y , xs ≟ ys) of λ where
      (yes p , yes q) → yes (cong₂ _∷_ p q)
      (yes _ , no ¬q) → no (λ { refl → ¬q refl })
      (no ¬p , _    ) → no (λ { refl → ¬p refl })
