{-# LANGUAGE GADTs, ViewPatterns #-}
module Control.Monad.Trans.Iter.Reflection
  ( IterT(..)
  , IterView(..)
  , view
  , unview
  ) where

import Control.Applicative
import Control.Arrow (Kleisli(..))
import Control.Category
import Control.Category.Free.Cat
import Control.Category.Free.View
import Control.Monad
import Prelude hiding (id,(.))

data IterT m a where
  IterRefl :: m (IterView m x) -> Cat (Kleisli (IterT m)) x b -> IterT m b

data IterView m a
  = Pure a
  | Iter (IterT m a)

instance Monad m => Functor (IterT m) where
  fmap = liftM

instance Monad m => Applicative (IterT m) where
  pure = return
  (<*>) = ap

instance Monad m => Monad (IterT m) where
  return x = IterRefl (return $ Pure x) id
  {-# INLINE return #-}
  IterRefl m r >>= f = IterRefl m (Kleisli f <| r)
  {-# INLINE (>>=) #-}\\

view :: Monad m => IterT m a -> m (IterView m a)
view (IterRefl mh t) = do
  h <- mh
  case h of
    Pure a -> case unsnoc t of
      Empty    -> return $ Pure a
      tc :| hc -> view $ runKleisli hc a ^>>= tc
    Iter f -> return $ Iter $ f ^>>= t

unview :: Monad m => m (IterView m a) -> IterT m a
unview x = IterRefl x id
{-# INLINE unview #-}

(^>>=) :: IterT m x -> Cat (Kleisli (IterT m)) x b -> IterT m b
IterRefl h t ^>>= r = IterRefl h (r . t)
{-# INLINE (^>>=) #-}
