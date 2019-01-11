
open import Data.List
open import Data.List.Membership.Propositional
open import Data.List.Any
open import Data.Product

open import Level

open import Library.Eq

open import Relation.Binary using (Decidable; Rel)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

module Library.List where

open import Data.List.Base public using (List; []; _∷_; foldl)
open import Data.List.All public using (All; []; _∷_) hiding (module All)

module All where
  open import Data.List.All public using (lookup; map; tail)

  -- A simple, unverified implementation of UpdateWith.

  updateWith : ∀ {a p} {A : Set a} {P : A → Set p} {x xs}
    (x∈xs : x ∈ xs) (f : P x → P x) (vs : All P xs) → All P xs
  updateWith (here refl)  f (v ∷ vs) = f v ∷ vs
  updateWith (there x∈xs) f (v ∷ vs) = v ∷ updateWith x∈xs f vs

module _ {a p} {A : Set a} {P : A → Set p} where

  -- Membership in List.All

  data _↤_∈_ {x} (v : P x) : ∀ {xs} → x ∈ xs → All P xs → Set where

    here  : ∀ {xs} {vs : All P xs}
      → v ↤ here refl ∈ (v ∷ vs)

    there : ∀ {xs} {x∈xs : x ∈ xs} {vs : All P xs} {y} {w : P y}
      → v ↤ x∈xs ∈ vs
      → v ↤ there x∈xs ∈ (w ∷ vs)

  -- This is how we want to write it:

  _↦_∈_ : ∀ {x xs} → x ∈ xs → P x → All P xs → Set
  x ↦ v ∈ vs = v ↤ x ∈ vs


-- Non-dependent association lists

AssocList : ∀{a b} {A : Set a} (B : Set b) (xs : List A) → Set (a ⊔ b)
AssocList B xs = All (λ _ → B) xs

module _ {a b} {A : Set a} {B : Set b} where

  -- Cons for non-dependent association lists.

  _↦_∷_ : ∀ (x : A) (v : B) {xs} (vs : AssocList B xs) → AssocList B (x ∷ xs)
  x ↦ v ∷ vs = _∷_ {x = x} v vs

module _ {a} {b} {A : Set a} {B : Set b} {{_ : Eq B}} where

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
