
open import Data.Integer using (ℤ)
open import Data.List    using (List)
open import Data.String  using (String)
open import Data.Unit    using (⊤)

open import Library.Monad

module Library.IO where

open import IO.Primitive public using (IO)

{-# FOREIGN GHC import qualified Data.Text #-}
{-# FOREIGN GHC import qualified Data.Text.IO #-}
{-# FOREIGN GHC import qualified System.Exit #-}
{-# FOREIGN GHC import qualified System.Environment #-}
{-# FOREIGN GHC import qualified System.IO #-}

postulate
  exitFailure    : ∀{a} {A : Set a} → IO A
  getArgs        : IO (List String)
  putStr         : String → IO ⊤
  putStrLn       : String → IO ⊤
  readFiniteFile : String → IO String
  readInt        : IO ℤ

{-# COMPILE GHC exitFailure    = \ _ _ -> System.Exit.exitFailure #-}
{-# COMPILE GHC getArgs        = map Data.Text.pack <$> System.Environment.getArgs #-}
{-# COMPILE GHC putStr         = System.IO.putStr   . Data.Text.unpack #-}
{-# COMPILE GHC putStrLn       = System.IO.putStrLn . Data.Text.unpack #-}
{-# COMPILE GHC readFiniteFile = Data.Text.IO.readFile . Data.Text.unpack #-}
{-# COMPILE GHC readInt        = (System.IO.readLn :: System.IO.IO Integer) #-}

instance
  FunctorIO : ∀ {a} → Functor (IO {a})
  FunctorIO .fmap f mx = mx IO.Primitive.>>= λ x → IO.Primitive.return (f x)

  ApplicativeIO : ∀ {a} → Applicative (IO {a})
  ApplicativeIO .pure        = IO.Primitive.return
  ApplicativeIO ._<*>_ mf mx = mf IO.Primitive.>>= λ f → f <$> mx

  MonadIO : ∀ {a} → Monad (IO {a})
  MonadIO ._>>=_ = IO.Primitive._>>=_
