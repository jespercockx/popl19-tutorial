-- Type checker for the WHILE language.

module TypeChecker where

open import Library
open String using (_≟_)
open AssocList
open AssocList.DecidableRange _≟_

import AST as A
open import WellTypedSyntax

-- Names as coming from the abstract syntax are just strings.

Name = String

idToName : A.Id → Name
idToName (A.mkId x) = String.fromList x

-- Decorating list elements with unique identifiers.
--
-- NameDecorated xs is a decoration of the elements
-- of list xs with unique Names.

record NameDecorated {A : Set} (xs : List A) : Set where
  field
    scope : AssocList Name xs
    uniq  : UniqueRange scope
open NameDecorated

-- The empty list has the empty decoration.

[]ⁿ : ∀{A} → NameDecorated {A} []
[]ⁿ .scope = []
[]ⁿ .uniq  = []ᵘ

-- Local context for the type checker.

TCCxt : (Γ : Cxt) → Set
TCCxt = NameDecorated {Type}

-- Querying the local context.

-- y ↦ x ∈Γ γ  states that index y points to identifier x in type checking context γ.

_↦_∈Γ_ : ∀{t Γ} (y : Var Γ t) (x : Name) (γ : TCCxt Γ) → Set
t∈Γ ↦ x ∈Γ γ = t∈Γ ↦ x ∈ scope γ

-- x ∈?Γ γ  tests whether identifier x is bound in type checking environment γ.

_∈?Γ_ : ∀{Γ} (x : Name) (γ : TCCxt Γ) → Dec (∃₂ λ t (y : Var Γ t) → y ↦ x ∈Γ γ)
x ∈?Γ γ = ?↦ x ∈ scope γ

-- Type errors.
--
-- Currently, these errors do not carry enough evidence that
-- something is wrong.  The type checker does not produce
-- evidence of ill-typedness in case of failure,
-- only of well-typedness in case of success.

data TypeError : Set where
  unboundVariable        : Name → TypeError
  shadowingDeclaration   : Name → TypeError
  typeMismatch           : (tinf texp : Type)  → tinf ≢ texp → TypeError

printError : TypeError → String
printError = λ where
  (unboundVariable x)        → "unbound variable " String.++ x
  (shadowingDeclaration x)   → "illegal shadowing by "  String.++ x
  (typeMismatch tinf texp _) → String.concat $
    "type mismatch: expected " ∷ A.printType texp ∷
    ", but inferred " ∷ A.printType tinf ∷ []

-- Type error monad.

open ErrorMonad {E = TypeError} using (Error; fail; ok)

-- Checking expressions
---------------------------------------------------------------------------

-- During checking of expressions, the context is fixed.

module CheckExpressions {Γ : Cxt} (γ : TCCxt Γ) where

  -- We work in the error monad.

  M = Error
  open ErrorMonad {E = TypeError} hiding (Error; fail; ok)

  -- Environment.

  lookupVar : (x : Name) → M (∃ λ t → Var Γ t)
  lookupVar x =
    case x ∈?Γ γ of λ where
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

    inferExp (A.eNot   e)     = ((bool ,_) ∘′ eNot) <$> checkExp e bool
    inferExp (A.ePlus  e₁ e₂) = inferOp (arith plus)  e₁ e₂
    inferExp (A.eMinus e₁ e₂) = inferOp (arith minus) e₁ e₂

    inferExp (A.eGt    e₁ e₂) = inferOp gt    e₁ e₂

    inferExp (A.eAnd   e₁ e₂) = inferOp and   e₁ e₂

    -- Type checking.
    -- Calls inference and checks inferred type against given type.

    checkExp : (e : A.Exp) (t : Type) → M (Exp Γ t)
    checkExp e t = do
      (t' , e') ← inferExp e
      case t' TypeEq.≟ t of λ where
        (yes refl) → return e'
        (no  t'≢t) → throwError (typeMismatch t' t t'≢t)

    -- Operators.

    inferOp : ∀{t t'} (op : Op t t') (e₁ e₂ : A.Exp) → M (∃ (Exp Γ))
    inferOp {t} {t'} op e₁ e₂ = do
      e₁' ← checkExp e₁ t
      e₂' ← checkExp e₂ t
      return (t' , eOp op e₁' e₂')

-- The statement checker calls the expression checker.
-- Exported interface of expression checker:

-- Monad for checking expressions

record TCExp Γ (A : Set) : Set where
  field
    runTCExp : TCCxt Γ → Error A
open TCExp

lookupVar : ∀{Γ} (x : Name) → TCExp Γ (∃ λ t → Var Γ t)
lookupVar x .runTCExp γ = CheckExpressions.lookupVar γ x

inferExp : ∀{Γ} (e : A.Exp) → TCExp Γ (∃ λ (t : Type) → Exp Γ t)
inferExp e .runTCExp γ = CheckExpressions.inferExp γ e

checkExp : ∀{Γ} (e : A.Exp) (t : Type) → TCExp Γ (Exp Γ t)
checkExp e t .runTCExp γ = CheckExpressions.checkExp γ e t

-- Checking statements.
---------------------------------------------------------------------------

-- Monad for checking statements.

-- Variable declarations can be inserted into the top block, thus,
-- we need to treat the top block as mutable state.

record TCStm Γ Γ' (A : Set) : Set where
  field
    runTCStm : TCCxt Γ → Error (A × TCCxt Γ')
open TCStm

-- Signature and return type stay fixed during checking of expressions.

module CheckStatements where

  -- TCStm is a monad.

  -- Return.

  return : ∀{Γ A} (a : A) → TCStm Γ Γ A
  return a .runTCStm γ = ok (a , γ)

  -- Bind.

  _>>=_ : ∀{Γ Γ′ Γ″ A B}
    (m :     TCStm Γ  Γ′ A)
    (k : A → TCStm Γ′ Γ″ B)
           → TCStm Γ  Γ″ B

  (m >>= k) .runTCStm γ =
    case m .runTCStm γ of λ where
      (fail err)    → fail err
      (ok (a , γ')) → k a .runTCStm γ'

  -- Sequence.

  _>>_  : ∀{Γ Γ′ Γ″ B}
    (m  : TCStm Γ  Γ′ ⊤)
    (m' : TCStm Γ′ Γ″ B)
        → TCStm Γ  Γ″ B
  m >> m' = m >>= λ _ → m'

  -- Map.

  _<$>_ : ∀{Γ Γ' A B} (f : A → B) → TCStm Γ Γ' A → TCStm Γ Γ' B
  f <$> m = m >>= (return ∘′ f)


  -- Error raising.

  throwError : ∀{Γ Γ' A} → TypeError → TCStm Γ Γ' A
  throwError err .runTCStm γ = fail err

  -- Lifting a TCExp computation into TCStm.

  lift : ∀{Γ A} (m : TCExp Γ A) → TCStm Γ Γ A
  lift m .runTCStm γ =
    case m .runTCExp γ of λ where
      (fail err) → fail err
      (ok a)     → ok (a , γ)

  -- In a new scope.

  newScope : ∀{Γ Γ' A} (m : TCStm Γ Γ' A) → TCStm Γ Γ A
  newScope m .runTCStm γ =

    case m .runTCStm γ of λ where
      (fail err)   → fail err  -- Here, err changes into a different context.
      (ok (a , _)) → ok (a , γ)

  -- Add a variable declaration.

  addVar : ∀{Γ} (x : Name) t → TCStm Γ (t ∷ Γ) ⊤
  addVar {Γ = Γ} x t .runTCStm γ =
    -- Try to uniquely extend the context.
    case t ↦ x ∷ᵘ? uniq γ of λ where
      (yes us) → ok (_ , record { uniq = us })
      (no _)  → fail (shadowingDeclaration x)

  -- Checking expressions.

  -- Predicting the next shape of the top block.

  cext : (Γ : Cxt) (s : A.Stm) → CxtExt
  cext Γ (A.sInit t x e)     = just t
  cext Γ (A.sAss x e)        = nothing
  cext Γ (A.sWhile e s)      = nothing
  cext Γ (A.sIfElse e s s₁)  = nothing

  Next : (Γ : Cxt) (s : A.Stm) → Cxt
  Next Γ s = Γ ▷ cext Γ s

  Nexts : (Γ : Cxt) (ss : List A.Stm) → Cxt
  Nexts = List.foldl Next

  mutual

    -- Checking a single statement.

    checkStm : ∀ {Γ} (s : A.Stm) (let mt = cext Γ s) → TCStm Γ (Γ ▷ mt) (Stm Γ mt)

    checkStm (A.sAss x e) = do
      (t , x') ← lift $ lookupVar (idToName x)
      e' ← lift $ checkExp e t
      return (sAss x' e')

    checkStm (A.sInit t x e) = do
      e' ← lift $ checkExp e t
      addVar (idToName x) t
      return (sInit e')

    checkStm (A.sWhile e ss) = do
      e'  ← lift $ checkExp e bool
      ss' ← newScope $ checkStms ss
      return (sWhile e' ss')

    checkStm (A.sIfElse e ss₁ ss₂) = do
      e'   ← lift $ checkExp e bool
      ss₁' ← newScope $ checkStms ss₁
      ss₂' ← newScope $ checkStms ss₂
      return (sIfElse e' ss₁' ss₂')

    -- Checking a list of statements.

    checkStms : ∀ {Γ} (ss : List A.Stm) (let Γ' = Nexts Γ ss) → TCStm Γ Γ' (Stms Γ Γ')
    checkStms []       = return []
    checkStms (s ∷ ss) = do
      s' ← checkStm s
      (s' ∷_) <$> checkStms ss

  -- Checking the program in TCStm.

  checkProgram : (prg : A.Program) → TCStm [] (Nexts [] (A.theStms prg)) Program
  checkProgram (A.program ss e) = do
    ss' ← checkStms ss
    e'  ← lift $ checkExp e int
    return (program ss' e')

-- Checking the program.
---------------------------------------------------------------------------

checkProgram : (prg : A.Program) → Error Program
checkProgram prg = proj₁ <$> CheckStatements.checkProgram prg .runTCStm []ⁿ
  where open ErrorMonad


-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
