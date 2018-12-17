import System.Environment (getArgs)
import System.Exit (exitFailure)

import While.ErrM  (Err(..))
import While.Par   (myLexer, pProgram)
import While.Print (printTree)

-- | Parse, type check, and interpret a program given by the @String@.

check :: String -> IO ()
check s = do
  case pProgram (myLexer s) of
    Bad err  -> do
      putStrLn "SYNTAX ERROR"
      putStrLn err
      exitFailure
    Ok  tree -> putStrLn $ printTree tree

-- | Main: read file passed by only command line argument and call 'check'.

main :: IO ()
main = do
  args <- getArgs
  case args of
    [file] -> readFile file >>= check
    _      -> do
      putStrLn "Usage: Main <SourceFile>"
      exitFailure
