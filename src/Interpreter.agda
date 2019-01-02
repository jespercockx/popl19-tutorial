module Interpreter where

open import Library
open import WellTypedSyntax
open import Value

open import Delay using (Delay; force; later'; runDelay) public

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

open EvalExp

execDecl : ∀{Γ t} (d : Decl Γ t) (ρ : Env Γ) → Env (t ∷ Γ)
execDecl (dInit e) ρ = eval ρ e ∷ ρ

execDecls : ∀{Γ Γ'} (ds : Decls Γ Γ') (ρ : Env Γ) → Env Γ'
execDecls []       ρ = ρ
execDecls (d ∷ ds) ρ = execDecls ds (execDecl d ρ)

-- Execution of statements.

-- We use the delay monad for non-termination.

module ExecStm {Γ : Cxt} where

    record Exec (i : Size) (A : Set) : Set where
      field
        runExec : (ρ : Env Γ) → Delay i (A × Env Γ)
    open Exec public

    -- Monad.

    private
      returnExec : ∀{i A} (a : A) → Exec i A
      returnExec a .runExec ρ = return (a , ρ)

      bindExec : ∀{i A B} (m : Exec i A) (k : A → Exec i B) → Exec i B
      bindExec m k .runExec ρ = m .runExec ρ >>= λ where
        (a , ρ') → k a .runExec ρ'


    instance
      FunctorExec : ∀ {i} → Functor (Exec i)
      FunctorExec .fmap f mx = bindExec mx (λ x → returnExec (f x))

      ApplicativeExec : ∀ {i} → Applicative (Exec i)
      ApplicativeExec .pure  = returnExec
      ApplicativeExec ._<*>_ mf mx = bindExec mf (_<$> mx)

      MonadExec : ∀ {i} → Monad (Exec i)
      MonadExec ._>>=_ = bindExec


    -- Updating the environment.

    modify : ∀{i} (f : Env Γ → Env Γ) → Exec i ⊤
    modify f .runExec ρ = return (_ , f ρ)

    -- Evaluate an expression.

    evalExp : ∀{i t} (e : Exp Γ t) → Exec i(Val t)
    evalExp e .runExec ρ = return (M.eval e , ρ)
      where module M = EvalExp ρ

    mutual

      -- Executing a single statement.

      execStm : ∀{i} (s : Stm Γ) → Exec i ⊤

      execStm (sAss x e) = do
        v ← evalExp e
        modify $ List.All.updateWith x (λ _ → v)

      execStm (sWhile e ss) = do
        true ← evalExp e where
          false → return _
        execStms ss
        -- The recursive call needs to be guarded:
        λ{ .runExec γ .force → later' $ execStm (sWhile e ss) .runExec γ }

      execStm (sIfElse e ss ss') = do
        b ← evalExp e
        case b of λ where
          true  → execStms ss
          false → execStms ss'

      -- Executing a list of statments.

      execStms : ∀{i} (ss : Stms Γ) → Exec i ⊤
      execStms []       = return _
      execStms (s ∷ ss) = do
        execStm  s
        execStms ss

evalPrg : ∀{i} (prg : Program) → Delay i ℤ
evalPrg (program ds ss e) = do
  let ρ₀ = execDecls ds []
  (_ , ρ) ← ExecStm.execStms ss .ExecStm.runExec ρ₀
  return $ EvalExp.eval ρ e

runProgram : (prg : Program) → ℤ
runProgram prg = runDelay (evalPrg prg)

-- -}
