
module Library.Print where

open import Agda.Builtin.String

-- Type class for printing to String.

record Print {ℓ} (A : Set ℓ) : Set ℓ where
  field
    print : A → String

open Print {{...}} public
