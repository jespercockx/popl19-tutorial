
module Library.Eq where

open import Agda.Builtin.Bool

open import Relation.Binary using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary.Decidable using (⌊_⌋)

-- Type class for decidable equality.

record Eq {ℓ} (A : Set ℓ) : Set ℓ where
  field
    _≟_ : Decidable (_≡_ {A = A})

  _==_ : A → A → Bool
  x == y = ⌊ x ≟ y ⌋

open Eq {{...}} public
