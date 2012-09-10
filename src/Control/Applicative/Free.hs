{-# LANGUAGE CPP #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE GADTs #-}
{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Control.Applicative.Free
-- Copyright   :  (C) 2012 Edward Kmett
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  provisional
-- Portability :  GADTs, Rank2Types
--
-- 'Applicative' functors for free
----------------------------------------------------------------------------
module Control.Applicative.Free
  ( Ap(..)
  , runAp
  , liftAp
  , hoistAp
  ) where

import Control.Applicative
import Data.Functor.Apply

#ifdef GHC_TYPEABLE
import Data.Typeable
#endif

-- | The free 'Applicative' for a 'Functor' @f@.
data Ap f a where
  Pure :: a -> Ap f a
  Ap   :: f a -> Ap f (a -> b) -> Ap f b

runAp :: Applicative g => (forall x. f x -> g x) -> Ap f a -> g a
runAp _ (Pure x) = pure x
runAp u (Ap f x) = flip id <$> u f <*> runAp u x

instance Functor (Ap f) where
  fmap f (Pure a)   = Pure (f a)
  fmap f (Ap x y)   = Ap x ((f .) <$> y)

instance Apply (Ap f) where
  Pure f <.> y = fmap f y
  Ap x y <.> z = Ap x (flip <$> y <.> z)

instance Applicative (Ap f) where
  pure = Pure
  Pure f <*> y = fmap f y
  Ap x y <*> z = Ap x (flip <$> y <*> z)

-- | A version of 'lift' that can be used with just a 'Functor' for @f@.
liftAp :: Functor f => f a -> Ap f a
liftAp x = Ap x (Pure id)
{-# INLINE liftAp #-}

hoistAp :: Functor g => (forall a. f a -> g a) -> Ap f b -> Ap g b
hoistAp _ (Pure a) = Pure a
hoistAp f (Ap x y) = Ap (f x) (hoistAp f y)
{-# INLINE hoistAp #-}

#ifdef GHC_TYPEABLE
instance Typeable1 f => Typeable1 (Ap f) where
  typeOf1 t = mkTyConApp apTyCon [typeOf1 (f t)] where
    f :: Ap f a -> f a
    f = undefined

apTyCon :: TyCon
#if __GLASGOW_HASKELL__ < 704
apTyCon = mkTyCon "Control.Applicative.Free.Ap"
#else
apTyCon = mkTyCon3 "free" "Control.Applicative.Free" "Ap"
#endif
{-# NOINLINE apTyCon #-}

#endif
