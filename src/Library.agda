-- Imports from the standard library and additional Haskell bindings.

module Library where

open import Data.Bool.Base                        public using (Bool; true; false; not; if_then_else_) hiding (module Bool)
open import Data.Char.Base                        public using (Char)
open import Data.Empty                            public using (⊥)
open import Data.Integer.Base                     public using (ℤ; -[1+_]; +_; _+_; _-_; _*_)
open import Data.List.Base                        public using (List; []; _∷_; _++_) hiding (module List)
open import Data.List.Membership.Propositional    public using (_∈_; _∉_)
open import Data.List.All                         public using ([]; _∷_)
open import Data.List.Any                         public using (here; there)
open import Data.Maybe.Base                       public using (Maybe; nothing; just)
open import Data.Nat.Base                         public using (ℕ; zero; suc)
open import Data.Product                          public using (∃; ∃₂; _×_; _,_; proj₁; proj₂; map₂)
open import Data.String.Base                      public using (String)
open import Data.Sum.Base                         public using (_⊎_; inj₁; inj₂)
open import Data.Unit.Base                        public using (⊤)

open import Function                              public using (id; _∘_; _∘′_; _$_; case_of_)
open import Level                                 public using (_⊔_)

open import Library.Eq                            public
open import Library.Monad                         public
open import Library.Print                         public

open import IO.Primitive                          public using (IO)

open import Relation.Binary.PropositionalEquality public using (_≡_; _≢_; refl; cong; cong₂; subst)
open import Relation.Binary                       public using (Decidable; Rel)
open import Relation.Nullary                      public using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable            public using (⌊_⌋)

open import Size                                  public

-- Qualified imports

module Bool where
  open import Data.Bool.Base public

module Character where
  open import Data.Char public

module Integer where
  open import Data.Integer public

  _<=_ : (i j : ℤ) → Bool
  i <= j = ⌊ i ≤? j ⌋

  postulate div : (i j : ℤ) → ℤ
  {-# COMPILE GHC div = div #-}

module String where
  open import Data.String.Base public

module List where
  open import Data.List.Base public
  open import Data.List.All public using (All; []; _∷_) hiding (module All)

  module All where
    open import Data.List.All public using (lookup; map; tail)

    -- Update function for All

    data Update {a p} {A : Set a} {P : A → Set p} {x} (v : P x)
      : ∀ {xs} (x∈xs : x ∈ xs) (vs vs' : All P xs) → Set where

      here : ∀{xs} {vs : All P xs} {v₀ : P x}
        → Update v (here refl) (v₀ ∷ vs) (v ∷ vs)

      there : ∀{xs} {x∈xs : x ∈ xs} {vs vs' : All P xs} {y} {w : P y}
        → Update v x∈xs vs vs'
        → Update v (there x∈xs) (w ∷ vs) (w ∷ vs')

    data UpdateWith {a p r} {A : Set a} {P : A → Set p} {x} (R : Rel (P x) r)
      : ∀ {xs} (x∈xs : x ∈ xs) (vs vs' : All P xs) → Set r where

      here : ∀{xs} {vs : All P xs} {v v' : P x}
        → R v v'
        → UpdateWith R (here refl) (v ∷ vs) (v' ∷ vs)

      there : ∀{xs} {x∈xs : x ∈ xs} {vs vs' : All P xs} {y} {w : P y}
        → UpdateWith R x∈xs vs vs'
        → UpdateWith R (there x∈xs) (w ∷ vs) (w ∷ vs')

    -- A simple, unverified implementation of UpdateWith.

    updateWith : ∀ {a p} {A : Set a} {P : A → Set p} {x xs}
      (x∈xs : x ∈ xs) (f : P x → P x) (vs : All P xs) → All P xs
    updateWith (here refl)  f (v ∷ vs) = f v ∷ vs
    updateWith (there x∈xs) f (v ∷ vs) = v ∷ updateWith x∈xs f vs

open List.All public using (here; there)

module _ {a p} {A : Set a} {P : A → Set p} where

  -- Update in List.All

  _[_≔_]↝_ : ∀ {x xs}
    (vs : List.All P xs)
    (x∈xs : x ∈ xs)
    (v : P x)
    (vs' : List.All P xs) → Set
  vs [ x∈xs ≔ v ]↝ vs' = List.All.Update v x∈xs vs vs'

  -- Membership in List.All

  data _↤_∈_ {x} (v : P x) : ∀ {xs} → x ∈ xs → List.All P xs → Set where

    here  : ∀ {xs} {vs : List.All P xs}
      → v ↤ here refl ∈ (v ∷ vs)

    there : ∀ {xs} {x∈xs : x ∈ xs} {vs : List.All P xs} {y} {w : P y}
      → v ↤ x∈xs ∈ vs
      → v ↤ there x∈xs ∈ (w ∷ vs)

  -- This is how we want to write it:

  _↦_∈_ : ∀ {x xs} → x ∈ xs → P x → List.All P xs → Set
  x ↦ v ∈ vs = v ↤ x ∈ vs

-- Non-dependent association lists

AssocList : ∀{a b} {A : Set a} (B : Set b) (xs : List A) → Set (a ⊔ b)
AssocList B xs = List.All (λ _ → B) xs

module AssocList where

  module _ {a b} {A : Set a} {B : Set b} where

    -- Cons for non-dependent association lists.

    _↦_∷_ : ∀ (x : A) (v : B) {xs} (vs : AssocList B xs) → AssocList B (x ∷ xs)
    x ↦ v ∷ vs = _∷_ {x = x} v vs

  module DecidableRange {b} {B : Set b} {{_ : Eq B}} where

    module _ {a} {A : Set a} where

      -- It is decidable whether something points to v in vs.

      ?↦_∈_ : ∀ (v : B) {xs : List A} (vs : AssocList B xs) →
        Dec (∃₂ λ x (x∈xs : x ∈ xs) → x∈xs ↦ v ∈ vs)

      ?↦ v ∈ [] = no λ{(x , () , _)}

      ?↦ v ∈ (w ∷ vs) with v ≟ w
      ?↦ v ∈ (v ∷ vs) | yes refl = yes (_ , here refl , here)

      ?↦ v ∈ (w ∷ vs) | no v≢w with ?↦ v ∈ vs
      ?↦ v ∈ (w ∷ vs) | no v≢w | yes (x , x∈xs , x∈xs↦v)
                               = yes (x , there x∈xs , there x∈xs↦v)
      ?↦ v ∈ (w ∷ vs) | no v≢w | no ¬p = no λ where
        (_ , _ , here)                  → v≢w refl
        (x , there x∈xs , there x∈xs↦v) → ¬p (x , x∈xs , x∈xs↦v)




{-# FOREIGN GHC import qualified Data.Text #-}
{-# FOREIGN GHC import qualified Data.Text.IO #-}
{-# FOREIGN GHC import qualified System.Exit #-}
{-# FOREIGN GHC import qualified System.Environment #-}
{-# FOREIGN GHC import qualified System.IO #-}

-- Binding more Haskell functions

postulate
  exitFailure    : ∀{a} {A : Set a} → IO A
  getArgs        : IO (List String)
  putStr         : String → IO ⊤
  putStrLn       : String → IO ⊤
  readFiniteFile : String → IO String
  readInt        : IO ℤ

{-# COMPILE GHC exitFailure    = \ _ _ -> System.Exit.exitFailure #-}
{-# COMPILE GHC getArgs        = map Data.Text.pack <$> System.Environment.getArgs #-}
{-# COMPILE GHC putStr         = System.IO.putStr   . Data.Text.unpack #-}
{-# COMPILE GHC putStrLn       = System.IO.putStrLn . Data.Text.unpack #-}
{-# COMPILE GHC readFiniteFile = Data.Text.IO.readFile . Data.Text.unpack #-}
{-# COMPILE GHC readInt        = (System.IO.readLn :: System.IO.IO Integer) #-}

-- Showing builtin types

private
  postulate
    printInt : ℤ → String

{-# COMPILE GHC printInt    = \ i -> Data.Text.pack (show (i :: Integer)) #-}

private
  printBool : Bool → String
  printBool true  = "true"
  printBool false = "false"

instance
  PrintInt : Print ℤ
  PrintInt .print = printInt

  PrintBool : Print Bool
  PrintBool .print = printBool

-- -}
