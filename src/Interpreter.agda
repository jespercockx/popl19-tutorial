module Interpreter where

open import Library
open import WellTypedSyntax
open import Value

open import Delay as Del public using (force; now; later) renaming (∞Delay to Delay; module ∞Delay to ∞Delay)

module Delay where
  open Del public using (force; now; later) renaming (_∞>>=_ to _>>=_)

  return : ∀{i A} (a : A) → Delay i A
  return a .force = now a

-- Evaluation of expressions.

module EvalExp {Γ} (ρ : Env Γ) where

  eval : ∀{t} (e : Exp Γ t) → Val t
  eval (eInt  i)              = i
  eval (eBool b)              = b
  eval (eVar x)               = List.All.lookup ρ x
  eval (eNot e)               = bNot (eval e)
  eval (eOp (arith op) e₁ e₂) = iArith op (eval e₁) (eval e₂)
  eval (eOp gt  e₁ e₂)        = iGt (eval e₁) (eval e₂)
  eval (eOp and e₁ e₂)        = case eval e₁ of λ where
    true  → eval e₂
    false → false

-- Execution of statements.

-- We use the delay monad for non-termination.

module ExecStm where

    record Exec (i : Size) (Γ Γ' : Cxt) (A : Set) : Set where
      field
        runExec : (ρ : Env Γ) → Delay i (A × Env Γ')
    open Exec public

    -- Monad.

    return : ∀{i Γ A} (a : A) → Exec i Γ Γ A
    return a .runExec ρ = Delay.return (a , ρ)

    _>>=_ : ∀{i Γ Γ′ Γ″ A B}
      (m :     Exec i Γ  Γ′ A)
      (k : A → Exec i Γ′ Γ″ B)
             → Exec i Γ  Γ″ B
    (m >>= k) .runExec ρ = m .runExec ρ Delay.>>= λ where
      (a , ρ') → {! k a .runExec ρ' !}

    _=<<_ : ∀{i Γ Γ′ Γ″ A B}
      (k : A → Exec i Γ′ Γ″ B)
      (m :     Exec i Γ  Γ′ A)
             → Exec i Γ  Γ″ B
    k =<< m = m >>= k

    _>>_ : ∀{i Γ Γ′ Γ″ B}
     (m : Exec i Γ  Γ′ ⊤)
     (k : Exec i Γ′ Γ″ B)
        → Exec i Γ  Γ″ B
    m >> m' = m >>= λ _ → m'

    -- Functoriality

    _<$>_ : ∀{i Γ Γ′ A B} (f : A → B) (m : Exec i Γ Γ′ A) → Exec i Γ Γ′ B
    f <$> m = m >>= λ a → return (f a)

    -- Updating the environment.

    modify : ∀{i Γ Γ'} (f : Env Γ → Env Γ') → Exec i Γ Γ' ⊤
    modify f .runExec ρ = Delay.return (_ , f ρ)

    newScope : ∀{i Γ Γ' A} → Exec i Γ Γ' A → Exec i Γ Γ A
    newScope m .runExec ρ = {! Delay.<$> m .runExec ρ !}

    -- Evaluate an expression.

    evalExp : ∀{Γ i t} (e : Exp Γ t) → Exec i Γ Γ (Val t)
    evalExp {Γ} e .runExec ρ = Delay.return (M.eval e , ρ)
      where module M = EvalExp {Γ} ρ

    mutual

      -- Executing a single statement.

      execStm : ∀{i Γ mt} (s : Stm Γ mt) → Exec i Γ (Γ ▷ mt) ⊤

      execStm (sInit e) = do
        v ← evalExp e
        modify (v ∷_)

      execStm (sAss x e) = do
        v ← evalExp e
        modify $ List.All.updateWith x (λ _ → v)

      execStm (sWhile e ss) = do
        true ← evalExp e where
          false → return _
        newScope $ execStms ss
        -- The recursive call needs to be guarded:
        λ{ .runExec γ .force → later $ execStm (sWhile e ss) .runExec γ }

      execStm (sIfElse e ss ss') = do
        b ← evalExp e
        case b of λ where
          true  → newScope $ execStms ss
          false → newScope $ execStms ss'

      -- Executing a list of statments.

      execStms : ∀{i Γ Γ'} (ss : Stms Γ Γ') → Exec i Γ Γ' ⊤
      execStms []       = return _
      execStms (s ∷ ss) = do
        execStm  s
        execStms ss

  -- exec : ∀{i Γ Γ'} (s : Stm Γ Γ') → Env Γ → Delay i (Env Γ')
  -- exec s

evalPrg : ∀{i} (prg : Program) → Delay i ℤ
evalPrg (program ss e) = do
  (_ , ρ) ← ExecStm.execStms ss .ExecStm.runExec []
  {!return $ EvalExp.eval ρ e !}
  where open Delay

-- -}
