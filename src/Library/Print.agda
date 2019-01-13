
module Library.Print where

open import Agda.Builtin.String

open import Data.Bool    using (Bool; true; false)
open import Data.Integer using (ℤ)

-- Type class for printing to String.

record Print {ℓ} (A : Set ℓ) : Set ℓ where
  field
    print : A → String

open Print {{...}} public

-- Showing builtin types

private
  postulate
    printInt : ℤ → String
  {-# COMPILE GHC printInt    = \ i -> Data.Text.pack (show (i :: Integer)) #-}

  printBool : Bool → String
  printBool true  = "true"
  printBool false = "false"

instance
  PrintInt : Print ℤ
  print {{PrintInt}} = printInt

  PrintBool : Print Bool
  print {{PrintBool}} = printBool
