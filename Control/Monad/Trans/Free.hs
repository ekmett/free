{-# LANGUAGE FlexibleContexts, FlexibleInstances, UndecidableInstances #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Control.Monad.Trans.Free
-- Copyright   :  (C) 2008-2011 Edward Kmett,
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  provisional
-- Portability :  portable
--
-- Haskell 98 free monads
--
----------------------------------------------------------------------------
module Control.Monad.Trans.Free
  ( Free(..)
  , retract
  , liftF
  , iter
  , wrap
  ) where

import Control.Applicative
import Control.Monad (liftM, MonadPlus(..))
import Control.Monad.Trans.Class
import Data.Functor.Bind
import Data.Foldable
import Data.Traversable
import Data.Semigroup.Foldable
import Data.Semigroup.Traversable

data Free f a = Pure a | Free (f (Free f a))

instance (Eq (f (Free f a)), Eq a) => Eq (Free f a) where
  Pure a == Pure b = a == b
  Free fa == Free fb = fa == fb
  _ == _ = False

instance (Ord (f (Free f a)), Ord a) => Ord (Free f a) where
  Pure a `compare` Pure b = a `compare` b
  Pure _ `compare` Free _ = LT
  Free _ `compare` Pure _ = GT
  Free fa `compare` Free fb = fa `compare` fb

instance (Show (f (Free f a)), Show a) => Show (Free f a) where
  showsPrec d (Pure a) = showParen (d > 10) $
    showString "Pure " . showsPrec 11 a
  showsPrec d (Free m) = showParen (d > 10) $
    showString "Free " . showsPrec 11 m

instance (Read (f (Free f a)), Read a) => Read (Free f a) where
  readsPrec d r = readParen (d > 10)
      (\r' -> [ (Pure m, t) 
             | ("Pure", s) <- lex r'
             , (m, t) <- readsPrec 11 s]) r
    ++ readParen (d > 10)
      (\r' -> [ (Free m, t)
             | ("Free", s) <- lex r'
             , (m, t) <- readsPrec 11 s]) r

instance Functor f => Functor (Free f) where
  fmap f (Pure a)  = Pure (f a)
  fmap f (Free fa) = Free (fmap f <$> fa)

instance Functor f => Apply (Free f) where
  Pure a  <.> Pure b = Pure (a b)
  Pure a  <.> Free fb = Free $ fmap a <$> fb
  Free fa <.> b = Free $ (<.> b) <$> fa
  
instance Functor f => Applicative (Free f) where
  pure = Pure
  Pure a <*> Pure b = Pure $ a b
  Pure a <*> Free mb = Free $ fmap a <$> mb
  Free ma <*> b = Free $ (<*> b) <$> ma

instance Functor f => Bind (Free f) where
  Pure a >>- f = f a
  Free m >>- f = Free ((>>- f) <$> m)
  
instance Functor f => Monad (Free f) where
  return = Pure
  Pure a >>= f = f a
  Free m >>= f = Free ((>>= f) <$> m)

instance Alternative v => Alternative (Free v) where
  empty = Free empty
  a <|> b = Free (pure a <|> pure b)

instance (Functor v, MonadPlus v) => MonadPlus (Free v) where
  mzero = Free mzero
  a `mplus` b = Free (return a `mplus` return b)

instance MonadTrans Free where
  lift = Free . liftM Pure

instance Foldable f => Foldable (Free f) where
  foldMap f (Pure a) = f a
  foldMap f (Free fa) = foldMap (foldMap f) fa

instance Foldable1 f => Foldable1 (Free f) where
  foldMap1 f (Pure a) = f a
  foldMap1 f (Free fa) = foldMap1 (foldMap1 f) fa

instance Traversable f => Traversable (Free f) where
  traverse f (Pure a) = Pure <$> f a 
  traverse f (Free fa) = Free <$> traverse (traverse f) fa

instance Traversable1 f => Traversable1 (Free f) where
  traverse1 f (Pure a) = Pure <$> f a
  traverse1 f (Free fa) = Free <$> traverse1 (traverse1 f) fa

liftF :: Functor f => f a -> Free f a
liftF = Free . fmap Pure

wrap :: f (Free f a) -> Free f a 
wrap = Free

-- | retract . lift = id
-- | retract . liftF = id
retract :: Monad f => Free f a -> f a
retract (Pure a) = return a
retract (Free as) = as >>= retract

iter :: Functor f => (f a -> a) -> Free f a -> a
iter _ (Pure a) = a
iter phi (Free m) = phi (iter phi <$> m)
