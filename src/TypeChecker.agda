-- Type checker for the WHILE language.

{-# OPTIONS --postfix-projections #-}

module TypeChecker where

open import Library

import AST as A
open import WellTypedSyntax

-- Names as coming from the abstract syntax are just strings.

Name = String

idToName : A.Id → Name
idToName (A.mkId x) = String.fromList x

-- Local context for the type checker.

TCCxt : (Γ : Cxt) → Set
TCCxt Γ = AssocList Name Γ

-- Querying the local context.

-- Type errors.
--
-- Currently, these errors do not carry enough evidence that
-- something is wrong.  The type checker does not produce
-- evidence of ill-typedness in case of failure,
-- only of well-typedness in case of success.

data TypeError : Set where
  unboundVariable        : Name → TypeError
  typeMismatch           : (tinf texp : Type)  → tinf ≢ texp → TypeError

instance
  PrintError : Print TypeError
  PrintError .print = λ where
    (unboundVariable x)        → "unbound variable " String.++ x
    (typeMismatch tinf texp _) → String.concat $
      "type mismatch: expected " ∷ print texp ∷
      ", but inferred " ∷ print tinf ∷ []

-- Type error monad.

open ErrorMonad {E = TypeError}

-- Checking expressions
---------------------------------------------------------------------------

-- During checking of expressions, the context is fixed.

module CheckExpressions {Γ : Cxt} (γ : TCCxt Γ) where

  -- We work in the error monad.

  M = Error

  -- Environment.

  lookupVar : (x : Name) → M (∃ λ t → Var Γ t)
  lookupVar x =
    case ?↦ x ∈ γ of λ where
      (yes (t , x' , _)) → return (t , x')
      (no ¬p)            → throwError $ unboundVariable x

  -- The expression checker.

  mutual

    -- Type inference.

    inferExp : (e : A.Exp) → M (∃ λ (t : Type) → Exp Γ t)

    inferExp (A.eInt i)  = return (int  , eInt  i)
    inferExp (A.eBool b) = return (bool , eBool b)

    inferExp (A.eId x) = do
      (t , x') ← lookupVar (idToName x)
      return (t , eVar x')

    inferExp (A.ePlus  e₁ e₂) = inferOp plus  e₁ e₂

    inferExp (A.eGt    e₁ e₂) = inferOp gt    e₁ e₂

    inferExp (A.eAnd   e₁ e₂) = inferOp and   e₁ e₂

    -- Type checking.
    -- Calls inference and checks inferred type against given type.

    checkExp : (e : A.Exp) (t : Type) → M (Exp Γ t)
    checkExp e t = do
      (t' , e') ← inferExp e
      case t' ≟ t of λ where
        (yes refl) → return e'
        (no  t'≢t) → throwError (typeMismatch t' t t'≢t)

    -- Operators.

    inferOp : ∀{t t'} (op : Op t t') (e₁ e₂ : A.Exp) → M (∃ λ t → Exp Γ t)
    inferOp {t} {t'} op e₁ e₂ = do
      e₁' ← checkExp e₁ t
      e₂' ← checkExp e₂ t
      return (t' , eOp op e₁' e₂')

  mutual

    -- Checking a single statement.

    checkStm : (s : A.Stm) → M (Stm Γ)

    checkStm (A.sAss x e) = do
      (t , x') ← lookupVar (idToName x)
      e' ← checkExp e t
      return (sAss x' e')

    checkStm (A.sWhile e ss) = do
      e'  ← checkExp e bool
      ss' ← checkStms ss
      return (sWhile e' ss')

    -- Checking a list of statements.

    checkStms : (ss : List A.Stm) → M (Stms Γ)
    checkStms []       = return []
    checkStms (s ∷ ss) = do
      s' ← checkStm s
      (s' ∷_) <$> checkStms ss

-- The declaration checker calls the expression checker.
-- Exported interface of expression checker:

-- Monad for checking expressions

record TCExp Γ (A : Set) : Set where
  field
    runTCExp : TCCxt Γ → Error A
open TCExp

checkExp : ∀{Γ} (e : A.Exp) (t : Type) → TCExp Γ (Exp Γ t)
checkExp e t .runTCExp γ = CheckExpressions.checkExp γ e t

checkStms : ∀{Γ} (ss : List A.Stm) → TCExp Γ (Stms Γ)
checkStms ss .runTCExp γ = CheckExpressions.checkStms γ ss

-- Checking declarations.
---------------------------------------------------------------------------

-- Monad for checking declarations.

-- Variable declarations can be inserted into the top block, thus,
-- we need to treat the top block as mutable state.

record TCDecl Γ Γ' (A : Set) : Set where
  field
    runTCDecl : TCCxt Γ → Error (A × TCCxt Γ')
open TCDecl

module CheckDeclarations where

  -- TCDecl is a monad.

  private

    returnTCDecl : ∀ {Γ A} (a : A) → TCDecl Γ Γ A
    returnTCDecl a .runTCDecl γ = ok (a , γ)

    bindTCDecl : ∀{Γ Γ′ Γ″ A B}
      (m :     TCDecl Γ  Γ′ A)
      (k : A → TCDecl Γ′ Γ″ B)
             → TCDecl Γ  Γ″ B

    bindTCDecl m k .runTCDecl γ =
      case m .runTCDecl γ of λ where
        (fail err)    → fail err
        (ok (a , γ')) → k a .runTCDecl γ'


  instance
    FunctorTCDecl : ∀ {Γ Γ′} → Functor (TCDecl Γ Γ′)
    FunctorTCDecl .fmap f m = bindTCDecl m (returnTCDecl ∘′ f)

    IApplicativeTCDecl : IApplicative TCDecl
    IApplicativeTCDecl .pure        = returnTCDecl
    IApplicativeTCDecl ._<*>_ mf mx = bindTCDecl mf (_<$> mx)

    IMonadTCDecl : IMonad TCDecl
    IMonadTCDecl ._>>=_ = bindTCDecl
    IMonadTCDecl .super = IApplicativeTCDecl

  -- Lifting a TCExp computation into TCDecl.

  lift : ∀{Γ A} (m : TCExp Γ A) → TCDecl Γ Γ A
  lift m .runTCDecl γ =
    case m .runTCExp γ of λ where
      (fail err) → fail err
      (ok a)     → ok (a , γ)

  -- Add a variable declaration.

  addVar : ∀{Γ} (x : Name) t → TCDecl Γ (t ∷ Γ) ⊤
  addVar {Γ = Γ} x t .runTCDecl γ = ok (_ , (t ↦ x ∷ γ))

  -- Predicting the next shape of the context.

  Next : (Γ : Cxt) (s : A.Decl) → Cxt
  Next Γ s = A.declType s ∷ Γ

  Nexts : (Γ : Cxt) (ss : List A.Decl) → Cxt
  Nexts = foldl Next

  mutual

    -- Checking a single declaration.

    checkDecl : ∀ {Γ} (d : A.Decl) (let t = A.declType d)
      → TCDecl Γ (t ∷ Γ) (Decl Γ t)

    checkDecl (A.dInit t x e) = do
      e' ← lift $ checkExp e t
      addVar (idToName x) t
      return (dInit e')

    -- Checking a list of declarations.

    checkDecls : ∀ {Γ} (ds : List A.Decl) (let Γ' = Nexts Γ ds)
      → TCDecl Γ Γ' (Decls Γ Γ')

    checkDecls []       = return []
    checkDecls (d ∷ ds) = do
      d' ← checkDecl d
      (d' ∷_) <$> checkDecls ds

  -- Checking the program in TCDecl.

  checkProgram : (prg : A.Program) (let Γ = Nexts [] (A.theDecls prg))
    → TCDecl [] Γ Program

  checkProgram (A.program ds ss e) = do
    ds' ← checkDecls ds
    ss' ← lift $ checkStms ss
    e'  ← lift $ checkExp e int
    return (program ds' ss' e')

-- Checking the program.
---------------------------------------------------------------------------

checkProgram : (prg : A.Program) → Error Program
checkProgram prg = proj₁ <$> CheckDeclarations.checkProgram prg .runTCDecl []
  where open ErrorMonad


-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
