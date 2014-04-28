{-# LANGUAGE GADTs #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE FlexibleContexts #-}
module Main where

import Control.Monad
import Control.Monad.Free
import Control.Monad.Free.TH
import Control.Monad.IO.Class
import Control.Monad.Trans.Maybe
import qualified Data.Foldable as F
import Text.Read (readMaybe)

-- | A data type representing basic commands for a retriable eDSL.
data RetryF next where
  -- | Simple output command.
  Output    :: String -> next -> RetryF next
  -- | Get anything readable from input.
  Input     :: Read a => (a -> next) -> RetryF next
  -- | Declare a retriable block.
  WithRetry :: Retry a -> (a -> next) -> RetryF next
  -- | Force retry command (retries innermost retriable block).
  Retry     :: RetryF next

-- | Unfortunately this Functor instance cannot yet be derived
-- automatically by GHC.
instance Functor RetryF where
  fmap f (Output s x) = Output s (f x)
  fmap f (Input g) = Input (f . g)
  fmap f (WithRetry block g) = WithRetry block (f . g)
  fmap _ Retry = Retry

-- | The monad for a retriable eDSL.
type Retry = Free RetryF

-- automacally generate convenience functions
makeFree ''RetryF

-- The following functions have been made available:
--
-- output     :: MonadFree RetryF m => String -> m ()
-- input      :: (MonadFree RetryF m, Read a) => m a
-- withRetry  :: MonadFree RetryF m => Retry a -> m a
-- retry      :: MonadFree RetryF m => m a

-- | We can run a retriable program in any MonadIO.
runRetry :: MonadIO m => Retry a -> m a
runRetry = iterM run
  where
    run :: MonadIO m => RetryF (m a) -> m a

    run (Output s next) = do
      liftIO $ putStrLn s
      next

    run (Input next) = do
      s <- liftIO getLine
      case readMaybe s of
        Just x  -> next x
        Nothing -> fail "invalid input"

    run (WithRetry block next) = do
      -- Here we use
      -- runRetry :: MonadIO m => Retry a -> MaybeT (m a)
      -- to control failure with MaybeT.
      -- We repeatedly run retriable block until we get it to work.
      Just x <- runMaybeT . F.msum $ repeat (runRetry block)
      next x

    run Retry = fail "forced retry"

-- | Sample program.
test :: Retry ()
test = do
  n <- withRetry $ do
    output "Enter any positive number: "
    n <- input
    when (n <= 0) $ do
      output "The number should be positive."
      retry
    return n
  output $ "You've just entered " ++ show (n :: Int)

main :: IO ()
main = runRetry test

