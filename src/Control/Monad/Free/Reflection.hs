{-# LANGUAGE GADTs, ViewPatterns #-}
module Control.Monad.Free.Reflection
  ( Free(..)
  , FreeView(..)
  ) where

import Control.Applicative
import Control.Arrow (Kleisli(..))
import Control.Category
import Control.Category.Free.Cat
import Control.Category.Free.View
import Control.Monad
import Prelude hiding (id,(.))

data Free f a where
  FreeRefl :: FreeView f x -> Cat (Kleisli (Free f)) x b -> Free f b

data FreeView f a
  = Pure a
  | Free (f (Free f a))

instance Functor (Free f) where
  fmap = liftM

instance Applicative (Free f) where
  pure = return
  (<*>) = ap

instance Monad (Free f) where
  return x = FreeRefl (Pure x) id
  FreeRefl m r >>= f = FreeRefl m (Kleisli f <| r)

view :: Functor f => Free f a -> FreeView f a
view (FreeRefl h t) = case h of
  Pure a -> case unsnoc t of
    Empty    -> Pure a
    tc :| hc -> view $ runKleisli hc a ^>>= tc
  Free f -> Free $ fmap (^>>= t) f

unview :: FreeView f a -> Free f a
unview x = FreeRefl x id

(^>>=) :: Free f x -> Cat (Kleisli (Free f)) x b -> Free f b
FreeRefl h t ^>>= r = FreeRefl h (r . t)
