-- Type checker and interpreter for WHILE language.

module runwhile where

open import Library
open import WellTypedSyntax using (Program)
-- open import TypeChecker     using (printError; module CheckProgram)

import AST as A
import Parser
-- import Interpreter

-- -- Other modules, not used here.
-- import Value
-- import Evaluation

-- Parse.

parse : String → IO A.Program
parse contents = do
  case Parser.parse contents of λ where
    (bad cs) → do
      putStrLn "SYNTAX ERROR"
      putStrLn (String.fromList cs)
      exitFailure
    (ok prg) → return prg
  where
  open IOMonad
  open Parser using (Err; ok; bad)

{-
-- Type check.

check : A.Program → IO (∃ Program)
check prg = do
  case checkProgram prg of λ where
    (fail err) → do
      putStrLn "TYPE ERROR"
      putStrLn (A.printProgram prg)
      putStrLn "The type error is:"
      putStrLn (printError err)
      exitFailure
    (ok prg') → return prg'
  where
  open IOMonad
  open ErrorMonad   using (fail; ok)
  open CheckProgram using (checkProgram)

-- Interpret.

run : ∃ Program → IO ⊤
run (Σ , prg') = runProgram prg'
  where open Interpreter using (runProgram)
-}

-- Display usage information and exit.

usage : IO ⊤
usage = do
  putStrLn "Usage: runwhile <SourceFile>"
  exitFailure
  where open IOMonad

-- Parse command line argument and send file content through pipeline.

runwhile : IO ⊤
runwhile = do
  file ∷ [] ← getArgs where _ → usage
  -- run =<< check =<< parse =<< readFiniteFile file
  putStrLn ∘ A.printProgram =<< parse =<< readFiniteFile file
  where open IOMonad

main = runwhile


-- -}
