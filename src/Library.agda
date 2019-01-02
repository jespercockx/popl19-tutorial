-- Imports from the standard library and additional Haskell bindings.

module Library where

open import Agda.Builtin.Float public using (Float) renaming
  ( primFloatNumericalEquality to _==?ᵈ_
  ; primFloatNumericalLess     to _<?ᵈ_
  ; primNatToFloat             to ℕ→double
  ; primFloatPlus              to _+ᵈ_
  ; primFloatMinus             to _-ᵈ_
  ; primFloatTimes             to _*ᵈ_
  ; primFloatDiv               to _/ᵈ_
  )
1ᵈ = ℕ→double 1

open import Data.Bool.Base    public using (Bool; true; false; _xor_; not; if_then_else_) hiding (module Bool)
open import Data.Char.Base    public using (Char)
open import Data.Empty        public using (⊥)
open import Data.Integer.Base public using (ℤ; -[1+_]; +_; _+_; _-_; _*_)
open import Data.List.Base    public using (List; []; _∷_; _++_) hiding (module List)
open import Data.List.Membership.Propositional public using (_∈_; _∉_)
open import Data.List.All public using ([]; _∷_)
open import Data.List.Any public using (here; there)
open import Data.List.NonEmpty public using (List⁺; _∷_; _∷⁺_) hiding (module List⁺)
open import Data.Maybe.Base   public using (Maybe; nothing; just)
open import Data.Product      public using (∃; ∃₂; _×_; _,_; proj₁; proj₂; map₂)
  renaming (map to ∃-map)
open import Data.String.Base  public using (String)
open import Data.Sum.Base     public using (_⊎_; inj₁; inj₂)
open import Data.Unit.Base    public using (⊤)

open import Function          public using (id; _∘_; _∘′_; _$_; case_of_)
open import Level             public using (_⊔_)

open import IO.Primitive      public using (IO)

open import Monad             public

open import Relation.Binary.PropositionalEquality public using (_≡_; _≢_; refl; cong; subst)
open import Relation.Binary public using (Decidable; Rel)
open import Relation.Nullary public using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable public using (⌊_⌋)

open import Size public

-- Qualified imports:

-- module ∃ = Data.Product -- bad idea, Agda's printer cannot deal with it

module Bool where
  open import Data.Bool.Base public using (_≟_)

  _==_ : (b b' : Bool) → Bool
  b == b' = ⌊ b ≟ b' ⌋

module Integer where
  open import Data.Integer public

  _==_ : (i j : ℤ) → Bool
  i == j = ⌊ i ≟ j ⌋

  _<=_ : (i j : ℤ) → Bool
  i <= j = ⌊ i ≤? j ⌋

  postulate div : (i j : ℤ) → ℤ
  {-# COMPILE GHC div = div #-}

module List where
  open import Data.List.Base public using (map; foldl)
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

    -- An non-dependent association list is unique
    -- if its range is a unique list.

    UniqueRange : ∀ {xs : List A} (vs : AssocList B xs) → Set (a ⊔ b)
    UniqueRange {xs} vs = ∀ {v x y} {x∈xs : x ∈ xs} {y∈xs : y ∈ xs}
      (p : x∈xs ↦ v ∈ vs)
      (q : y∈xs ↦ v ∈ vs)
      → ∃ λ(x≡y : x ≡ y) → subst (_∈ xs) x≡y x∈xs ≡ y∈xs

    -- The empty association list is unique.

    []ᵘ : UniqueRange []
    []ᵘ () _

    -- ↦ v ∉ vs  means nothing points to v in vs.

    ↦_∉_ : ∀{xs} → B → AssocList B xs → Set a
    ↦_∉_ {xs} v vs = ∀{x : A} {x∈xs : x ∈ xs} → ¬ (x∈xs ↦ v ∈ vs)

    -- If nothing points to v we can cons it to a unique association list.

    _∷ᵘ_ : ∀{v xs x} {vs : AssocList B xs}
      (u : ↦ v ∉ vs) (us : UniqueRange vs) → UniqueRange (x ↦ v ∷ vs)
    (u ∷ᵘ us) here here = refl , refl
    (u ∷ᵘ us) here (there q) = case u q of λ()
    (u ∷ᵘ us) (there p) here = case u p of λ()
    (u ∷ᵘ us) (there p) (there q) with us p q
    ... | refl , refl = refl , refl

    -- The singleton association list is unique.

    sgᵘ : ∀ (x : A) (v : B) → UniqueRange (x ↦ v ∷ [])
    sgᵘ x v = (λ()) ∷ᵘ []ᵘ

    -- If something already points to v, we cannot add x↦v to
    -- an association list without losing uniqueness.

    head-not-unique : ∀{x y : A} {xs} {y∈xs : y ∈ xs} {v : B} {vs}
      (y↦v∈vs : y∈xs ↦ v ∈ vs) → ¬ UniqueRange (x ↦ v ∷ vs)
    head-not-unique y↦v∈vs us = case us here (there y↦v∈vs) of λ where
      (refl , ())

  module DecidableRange {b} {B : Set b} (_≟_ : Decidable (_≡_ {A = B})) where

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

      -- It is decidable whether we can cons to an association list
      -- without losing uniqueness.

      _↦_∷ᵘ?_ : ∀ (x : A) (v : B) {xs} {vs : AssocList B xs}
        (us : UniqueRange vs) → Dec (UniqueRange (x ↦ v ∷ vs))
      _↦_∷ᵘ?_ x v {xs} {vs} us with ?↦ v ∈ vs
      _↦_∷ᵘ?_ x v {xs} {vs} us | no ¬p = yes ((λ p → ¬p (_ , _ , p)) ∷ᵘ us)
      _↦_∷ᵘ?_ x v {xs} {vs} us | yes (_ , _ , y↦v∈vs) = no (head-not-unique y↦v∈vs)

-- Non-empty lists.

module List⁺ where
  open import Data.List.NonEmpty public using (toList; tail)

  All : ∀{a p} {A : Set a} (P : A → Set p) → List⁺ A → Set (p ⊔ a)
  All P xs = List.All P (toList xs)

module String where
  open import Data.String.Base public
  open import Data.String.Unsafe public using (_≟_)

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

open IOMonad public

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
  readDouble     : IO Float

{-# COMPILE GHC exitFailure    = \ _ _ -> System.Exit.exitFailure #-}
{-# COMPILE GHC getArgs        = map Data.Text.pack <$> System.Environment.getArgs #-}
{-# COMPILE GHC putStr         = System.IO.putStr   . Data.Text.unpack #-}
{-# COMPILE GHC putStrLn       = System.IO.putStrLn . Data.Text.unpack #-}
{-# COMPILE GHC readFiniteFile = Data.Text.IO.readFile . Data.Text.unpack #-}
{-# COMPILE GHC readInt        = (System.IO.readLn :: System.IO.IO Integer) #-}
{-# COMPILE GHC readDouble     = (System.IO.readLn :: System.IO.IO Double)  #-}

-- Showing builtin types

postulate
  printInt : ℤ → String
  printDouble : Float → String

{-# COMPILE GHC printInt    = \ i -> Data.Text.pack (show (i :: Integer)) #-}
{-# COMPILE GHC printDouble = \ d -> Data.Text.pack (show (d :: Double )) #-}

printBool : Bool → String
printBool true  = "true"
printBool false = "false"

-- -}
