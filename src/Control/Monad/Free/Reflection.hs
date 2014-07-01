{-# LANGUAGE PatternSynonyms, GADTs, ViewPatterns #-}
module Control.Monad.Free.Reflection
  ( Free(..)
  , pattern Pure
  , pattern Free
  ) where

import Control.Applicative
import Control.Arrow (Kleisli(..))
import Control.Category
import Control.Category.Free.Cat
import Control.Category.Free.View
import Control.Monad
import Prelude hiding (id,(.))

data Free f a where
  FreeRefl :: Either x (f (Free f x)) -> Cat (Kleisli (Free f)) x b -> Free f b

instance Functor (Free f) where
  fmap = liftM

instance Applicative (Free f) where
  pure = return
  (<*>) = ap

instance Monad (Free f) where
  return x = FreeRefl (Left x) id
  FreeRefl m r >>= f = FreeRefl m (Kleisli f <| r)

view :: Functor f => Free f a -> Either a (f (Free f a))
view (FreeRefl h t) = case h of
  Left a -> case unsnoc t of
    Empty -> Left a
    tc :| hc -> view (runKleisli hc a ^>>= tc)
  Right f -> Right $ fmap (^>>= t) f

(^>>=) :: Free f x -> Cat (Kleisli (Free f)) x b -> Free f b
FreeRefl h t ^>>= r = FreeRefl h (r . t)

-- playing with view patterns here. probably won't last into the public API
pattern Pure a <- (view -> Left a)
pattern Free f <- (view -> Right f)
