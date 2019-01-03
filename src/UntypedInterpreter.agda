
open import Library
open import AST
open Integer

-- Untyped values.

data Val : Set where
  intV  : ℤ       → Val
  boolV : Boolean → Val

instance
  PrintVal : Print Val
  PrintVal .print = λ where
    (intV i)  → printInt i
    (boolV b) → printBoolean b

Env : Set
Env = List (Id × Val)

-- Semantics of operations.

bNot : Boolean → Boolean
bNot true = false
bNot false = true

bAnd : Boolean → Boolean → Boolean
bAnd true true = true
bAnd _    _    = false

iGt : (i j : ℤ) → Boolean
iGt i j = case i Integer.<= j of λ where
  false → true
  true  → false

module EvalExp (ρ : Env) where

  lookupId : List (Id × Val) → Id → Maybe Val
  lookupId []             y = nothing
  lookupId ((x , v) ∷ xs) y =
    if x == y
    then just v
    else lookupId xs y

  eval : Exp → Maybe Val
  eval (eId x) = lookupId ρ x
  eval (eInt i) = just (intV i)
  eval (eBool b) = just (boolV b)
  eval (eNot e) = case (eval e) of λ where
    (just (boolV b)) → just (boolV (bNot b))
    _ → nothing
  eval (ePlus e₁ e₂) = case (eval e₁ , eval e₂) of λ where
    (just (intV i) , just (intV j)) → just (intV (i + j))
    _ → nothing
  eval (eMinus e₁ e₂) = case (eval e₁ , eval e₂) of λ where
    (just (intV i) , just (intV j)) → just (intV (i - j))
    _ → nothing
  eval (eGt e₁ e₂) = case (eval e₁ , eval e₂) of λ where
    (just (intV i) , just (intV j)) → just (boolV (iGt i j))
    _ → nothing
  eval (eAnd e₁ e₂) = case (eval e₁ , eval e₂) of λ where
    (just (boolV b₁) , just (boolV b₂)) → just (boolV (bAnd b₁ b₂))
    _ → nothing

open EvalExp

execDecl : Decl → Env → Maybe Env
execDecl (dInit t x e) ρ = case eval ρ e of λ where
  (just v) → just ((x , v) ∷ ρ)
  nothing  → nothing

execDecls : List Decl → Env → Maybe Env
execDecls [] ρ = just ρ
execDecls (d ∷ ds) ρ = case execDecl d ρ of λ where
  (just ρ') → execDecls ds ρ'
  nothing   → nothing

module ExecStm where

  updateEnv : Id → Val → Env → Env
  updateEnv x v [] = (x , v) ∷ []
  updateEnv x v ((y , w) ∷ ρ) =
    if x == y
    then (x , v) ∷ ρ
    else (y , w) ∷ updateEnv x v ρ

  mutual

    execStm : (fuel : ℕ) → Stm → Env → Maybe Env
    execStm 0 _ _ = nothing
    execStm (suc n) (sAss x e) ρ = case eval ρ e of λ where
      (just v) → just (updateEnv x v ρ)
      nothing  → nothing
    execStm (suc n) (sWhile e ss) ρ = case eval ρ e of λ where
      (just (boolV true)) → case execStms n ss ρ of λ where
        (just ρ') → execStm n (sWhile e ss) ρ'
        nothing   → nothing
      (just (boolV false)) → just ρ
      _                    → nothing
    execStm (suc n) (sIfElse e ss ss') ρ = case eval ρ e of λ where
      (just (boolV true))  → execStms n ss ρ
      (just (boolV false)) → execStms n ss' ρ
      _                    → nothing

    execStms : (fuel : ℕ) → List Stm → Env → Maybe Env
    execStms n [] ρ = just ρ
    execStms n (s ∷ ss) ρ = case execStm n s ρ of λ where
      (just ρ') → execStms n ss ρ'
      nothing   → nothing

  evalPrg : (fuel : ℕ) → Program → Maybe ℤ
  evalPrg n (program ds ss e) = case execDecls ds [] of λ where
    (just ρ₀) → case execStms n ss ρ₀ of λ where
      (just ρ) → case eval ρ e of λ where
        (just (intV v)) → just v
        _               → nothing
      nothing  → nothing
    nothing   → nothing
