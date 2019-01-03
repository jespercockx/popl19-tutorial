
module Library.Print where

open import Agda.Builtin.String

record Print {ℓ} (A : Set ℓ) : Set ℓ where
  field
    print : A → String

open Print {{...}} public
