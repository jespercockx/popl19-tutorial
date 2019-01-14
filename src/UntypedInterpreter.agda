-- Untyped interpreter for the WHILE language.
--
-- * Runs directly on the unchecked abstract syntax tree.
-- * May fail due to scope and other runtime errors.
-- * while loops may not terminate.

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
    (intV i)  → print i
    (boolV b) → print b

-- Poor man's environments (association list).

Env : Set
Env = List (Id × Val)

-- Looking up the value bound to a variable in an environment.

lookupId : Env → Id → Maybe Val
lookupId []             y = nothing
lookupId ((x , v) ∷ xs) y =
  if x == y
  then just v
  else lookupId xs y

-- Adding or updating a binding in the environment.

updateEnv : Id → Val → Env → Env
updateEnv x v []            = (x , v) ∷ []
updateEnv x v ((y , w) ∷ ρ) =
  if x == y
  then (x , v) ∷ ρ
  else (y , w) ∷ updateEnv x v ρ

-- -- Poor man's version, keeps history of bindings.
-- updateEnv x v ρ = (x , v) ∷ ρ
-- updateEnv : Id → Val → Env → Env

-- Semantics of operations.

-- Boolean negation.

bNot : Boolean → Boolean
bNot true = false
bNot false = true

-- Boolean conjunction.

bAnd : Boolean → Boolean → Boolean
bAnd true  b = b
bAnd false _ = false

-- Greater-than on integers.

iGt : (i j : ℤ) → Boolean
iGt i j = case i Integer.<= j of λ where
  false → true
  true  → false

-- Evaluation of expressions.  The environment is fixed.

module EvalExp (ρ : Env) where

  -- Evaluation may fail due to scope or type errors, thus eval is partial.
  -- E.g. eval (eNot (eInt zero)) ≡ nothing.

  eval : Exp → Maybe Val
  eval (eId x)   = lookupId ρ x
  eval (eInt i)  = just (intV i)
  eval (eBool b) = just (boolV b)
  eval (ePlus e₁ e₂) = case (eval e₁ , eval e₂) of λ where
    (just (intV i) , just (intV j)) → just (intV (i + j))
    _ → nothing
  eval (eGt e₁ e₂) = case (eval e₁ , eval e₂) of λ where
    (just (intV i) , just (intV j)) → just (boolV (iGt i j))
    _ → nothing
  eval (eAnd e₁ e₂) = case (eval e₁ , eval e₂) of λ where
    (just (boolV b₁) , just (boolV b₂)) → just (boolV (bAnd b₁ b₂))
    _ → nothing

open EvalExp

-- The execution of a declaration adds a new binding
-- to the environment.

execDecl : Decl → Env → Maybe Env
execDecl (dInit t x e) ρ = case eval ρ e of λ where
  (just v) → just ((x , v) ∷ ρ)
  nothing  → nothing

-- Execution of declarations returns the extended environment.

execDecls : List Decl → Env → Maybe Env
execDecls [] ρ = just ρ
execDecls (d ∷ ds) ρ = case execDecl d ρ of λ where
  (just ρ') → execDecls ds ρ'
  nothing   → nothing

-- Execution of statements can change values in the environment
-- and can diverge.

module ExecStm where

  -- Execution is parameterized by a number (fuel : ℕ)
  -- that limits the number of executions of while loops.
  -- This is necessary to please Agda's termination checker.

  mutual

    execStm : (fuel : ℕ) → Stm → Env → Maybe Env

    execStm _ (sAss x e) ρ = case eval ρ e of λ where
      (just v) → just (updateEnv x v ρ)
      nothing  → nothing

    execStm 0          (sWhile e ss) ρ = nothing
    execStm (suc fuel) (sWhile e ss) ρ = case eval ρ e of λ where
      (just (boolV true)) → case execStms fuel ss ρ of λ where
        (just ρ') → execStm fuel (sWhile e ss) ρ'
        nothing   → nothing
      (just (boolV false)) → just ρ
      _                    → nothing

    -- Execution of a statement sequence, passes the fuel
    -- to every statement.

    execStms : (fuel : ℕ) → List Stm → Env → Maybe Env
    execStms _    []       ρ = just ρ
    execStms fuel (s ∷ ss) ρ = case execStm fuel s ρ of λ where
      (just ρ') → execStms fuel ss ρ'
      nothing   → nothing

  -- We evaluate a program by first executing the declarations,
  -- then the statements, and finally evaluating the main expression.

  evalPrg : (fuel : ℕ) → Program → Maybe ℤ
  evalPrg fuel (program ds ss e) = case execDecls ds [] of λ where
    (just ρ₀) → case execStms fuel ss ρ₀ of λ where
      (just ρ) → case eval ρ e of λ where
        (just (intV v)) → just v
        _               → nothing
      nothing  → nothing
    nothing   → nothing
