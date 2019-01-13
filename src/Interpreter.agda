-- Interpreter for WHILE language.

-- As computation is not guaranteed to terminate,
-- execution of statements is placed in the Delay monad.

module Interpreter where

open import Library
open import WellTypedSyntax
open import Value

open import Delay using (Delay; force; later'; runDelay) public

-- Evaluation of expressions in fixed environment ρ.

module EvalExp {Γ} (ρ : Env Γ) where

  eval : ∀{t} (e : Exp Γ t) → Val t
  eval (eInt  i)              = i
  eval (eBool b)              = b
  eval (eVar x)               = All.lookup ρ x
  eval (eOp plus e₁ e₂)       = eval e₁ + eval e₂
  eval (eOp gt  e₁ e₂)        = iGt (eval e₁) (eval e₂)
  eval (eOp and e₁ e₂)        = case eval e₁ of λ where
    true  → eval e₂
    false → false

open EvalExp

-- Execution of declarations, extending the environment.

execDecl : ∀{Γ t} (d : Decl Γ t) (ρ : Env Γ) → Env (t ∷ Γ)
execDecl (dInit e) ρ = eval ρ e ∷ ρ

execDecls : ∀{Γ Γ'} (ds : Decls Γ Γ') (ρ : Env Γ) → Env Γ'
execDecls []       ρ = ρ
execDecls (d ∷ ds) ρ = execDecls ds (execDecl d ρ)

-- Execution of statements.

-- We use the delay monad for non-termination
-- and the state monad for environment update.

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
    functorExec : ∀ {i} → Functor (Exec i)
    fmap {{functorExec}} f mx = bindExec mx (λ x → returnExec (f x))

    applicativeExec : ∀ {i} → Applicative (Exec i)
    pure  {{applicativeExec}}       = returnExec
    _<*>_ {{applicativeExec}} mf mx = bindExec mf (_<$> mx)

    monadExec : ∀ {i} → Monad (Exec i)
    _>>=_ {{monadExec}} = bindExec

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
      modify $ All.updateWith x (λ _ → v)

    execStm (sIfElse e ss ss') = do
      b ← evalExp e
      case b of λ where
        true  → execStms ss
        false → execStms ss'

    execStm (sWhile e ss) = do
      true ← evalExp e where
        false → return _
      execStms ss
      -- The recursive call needs to be guarded:
      λ{ .runExec γ .force → later' $ execStm (sWhile e ss) .runExec γ }

    -- Executing a list of statments.

    execStms : ∀{i} (ss : Stms Γ) → Exec i ⊤
    execStms []       = return _
    execStms (s ∷ ss) = do
      execStm  s
      execStms ss

-- Execution of the program (main loop).

execPrg : ∀{i} (prg : Program) → Delay i ℤ
execPrg (program ds ss e) = do

  -- Execute the declarations to get the initial environment ρ₀.
  let ρ₀ = execDecls ds []

  -- Execute the statements (may not terminate).
  (_ , ρ) ← ExecStm.execStms ss .ExecStm.runExec ρ₀

  -- Evaluate the main expression to yield result.
  return $ EvalExp.eval ρ e

-- The result of a program is an integer.

runProgram : (prg : Program) → ℤ
runProgram prg = runDelay (execPrg prg)

-- -}
