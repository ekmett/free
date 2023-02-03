{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE Safe #-}
{-# LANGUAGE StandaloneDeriving #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Control.Comonad.Trans.Coiter
-- Copyright   :  (C) 2008-2013 Edward Kmett
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  provisional
-- Portability :  MPTCs, fundeps
--
-- The coiterative comonad generated by a comonad
----------------------------------------------------------------------------
module Control.Comonad.Trans.Coiter
  (
  -- |
  -- Coiterative comonads represent non-terminating, productive computations.
  --
  -- They are the dual notion of iterative monads. While iterative computations
  -- produce no values or eventually terminate with one, coiterative
  -- computations constantly produce values and they never terminate.
  --
  -- It's simpler form, 'Coiter', is an infinite stream of data. 'CoiterT'
  -- extends this so that each step of the computation can be performed in
  -- a comonadic context.

  -- * The coiterative comonad transformer
    CoiterT(..)
  -- * The coiterative comonad
  , Coiter, coiter, runCoiter
  -- * Generating coiterative comonads
  , unfold
  -- * Cofree comonads
  , ComonadCofree(..)
  -- * Examples
  -- $example
  ) where

import Control.Arrow hiding (second)
import Control.Comonad
import Control.Comonad.Cofree.Class
import Control.Comonad.Env.Class
import Control.Comonad.Hoist.Class
import Control.Comonad.Store.Class
import Control.Comonad.Traced.Class
import Control.Comonad.Trans.Class
import Control.Category
import Data.Bifunctor
import Data.Bifoldable
import Data.Bitraversable
import Data.Data
import Data.Foldable
import Data.Functor.Classes
import Data.Functor.Identity
import Data.Traversable
import Prelude hiding (id,(.))

-- | This is the coiterative comonad generated by a comonad
newtype CoiterT w a = CoiterT { runCoiterT :: w (a, CoiterT w a) }

instance (Eq1 w) => Eq1 (CoiterT w) where
  liftEq eq = go
    where
      go (CoiterT x) (CoiterT y) = liftEq (liftEq2 eq go) x y

instance (Ord1 w) => Ord1 (CoiterT w) where
  liftCompare cmp = go
    where
      go (CoiterT x) (CoiterT y) = liftCompare (liftCompare2 cmp go) x y

instance (Show1 w) => Show1 (CoiterT w) where
  liftShowsPrec sp sl = go
    where
      goList = liftShowList sp sl
      go d (CoiterT x) = showsUnaryWith
        (liftShowsPrec (liftShowsPrec2 sp sl go goList) (liftShowList2 sp sl go goList))
        "CoiterT" d x

instance (Read1 w) => Read1 (CoiterT w) where
  liftReadsPrec rp rl = go
    where
      goList = liftReadList rp rl
      go = readsData $ readsUnaryWith
        (liftReadsPrec (liftReadsPrec2 rp rl go goList) (liftReadList2 rp rl go goList))
        "CoiterT" CoiterT

-- | The coiterative comonad
type Coiter = CoiterT Identity

-- | Prepends a result to a coiterative computation.
--
-- prop> runCoiter . uncurry coiter == id
coiter :: a -> Coiter a -> Coiter a
coiter a as = CoiterT $ Identity (a,as)
{-# INLINE coiter #-}

-- | Extracts the first result from a coiterative computation.
--
-- prop> uncurry coiter . runCoiter == id
runCoiter :: Coiter a -> (a, Coiter a)
runCoiter = runIdentity . runCoiterT
{-# INLINE runCoiter #-}

instance Functor w => Functor (CoiterT w) where
  fmap f = CoiterT . fmap (bimap f (fmap f)) . runCoiterT

instance Comonad w => Comonad (CoiterT w) where
  extract = fst . extract . runCoiterT
  {-# INLINE extract #-}
  extend f = CoiterT . extend (\w -> (f (CoiterT w), extend f $ snd $ extract w)) . runCoiterT

instance Foldable w => Foldable (CoiterT w) where
  foldMap f = foldMap (bifoldMap f (foldMap f)) . runCoiterT

instance Traversable w => Traversable (CoiterT w) where
  traverse f = fmap CoiterT . traverse (bitraverse f (traverse f)) . runCoiterT

instance ComonadTrans CoiterT where
  lower = fmap fst . runCoiterT

instance Comonad w => ComonadCofree Identity (CoiterT w) where
  unwrap = Identity . snd . extract . runCoiterT
  {-# INLINE unwrap #-}

instance ComonadEnv e w => ComonadEnv e (CoiterT w) where
  ask = ask . lower
  {-# INLINE ask #-}

instance ComonadHoist CoiterT where
  cohoist g = CoiterT . fmap (second (cohoist g)) . g . runCoiterT

instance ComonadTraced m w => ComonadTraced m (CoiterT w) where
  trace m = trace m . lower
  {-# INLINE trace #-}

instance ComonadStore s w => ComonadStore s (CoiterT w) where
  pos = pos . lower
  peek s = peek s . lower
  peeks f = peeks f . lower
  seek = seek
  seeks = seeks
  experiment f = experiment f . lower
  {-# INLINE pos #-}
  {-# INLINE peek #-}
  {-# INLINE peeks #-}
  {-# INLINE seek #-}
  {-# INLINE seeks #-}
  {-# INLINE experiment #-}

instance (Show1 w, Show a) => Show (CoiterT w a) where
  showsPrec = showsPrec1

instance (Read1 w, Read a) => Read (CoiterT w a) where
  readsPrec = readsPrec1

instance (Eq1 w, Eq a) => Eq (CoiterT w a) where
  (==) = eq1
  {-# INLINE (==) #-}

instance (Ord1 w, Ord a) => Ord (CoiterT w a) where
  compare = compare1
  {-# INLINE compare #-}

-- | Unfold a @CoiterT@ comonad transformer from a cokleisli arrow and an initial comonadic seed.
unfold :: Comonad w => (w a -> a) -> w a -> CoiterT w a
unfold psi = CoiterT . extend (extract &&& unfold psi . extend psi)

deriving instance
  ( Typeable w, Typeable a
  , Data (w (a, CoiterT w a))
  , Data a
  ) => Data (CoiterT w a)

{- $example

<examples/NewtonCoiter.lhs Newton's method>

-}
