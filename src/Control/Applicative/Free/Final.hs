{-# LANGUAGE CPP #-}
{-# LANGUAGE RankNTypes #-}
#include "free-common.h"

-----------------------------------------------------------------------------
-- |
-- Module      :  Control.Applicative.Free.Final
-- Copyright   :  (C) 2012-2013 Edward Kmett
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  provisional
-- Portability :  GADTs, Rank2Types
--
-- Final encoding of free 'Applicative' functors.
----------------------------------------------------------------------------
module Control.Applicative.Free.Final
  (
  -- | Compared to the free monad, they are less expressive. However, they are also more
  -- flexible to inspect and interpret, as the number of ways in which
  -- the values can be nested is more limited.

    Ap(..)
  , runAp
  , runAp_
  , liftAp
  , hoistAp
  , retractAp

  -- * Examples
  -- $examples
  ) where

import Control.Applicative
import Data.Functor.Apply

#if !(MIN_VERSION_base(4,8,0))
import Data.Monoid
#endif

-- | The free 'Applicative' for a 'Functor' @f@.
newtype Ap f a = Ap { _runAp :: forall g. Applicative g => (forall x. f x -> g x) -> g a }

-- | Given a natural transformation from @f@ to @g@, this gives a canonical monoidal natural transformation from @'Ap' f@ to @g@.
--
-- prop> runAp t == retractApp . hoistApp t
runAp :: Applicative g => (forall x. f x -> g x) -> Ap f a -> g a
runAp phi m = _runAp m phi

-- | Perform a monoidal analysis over free applicative value.
--
-- Example:
--
-- @
-- count :: Ap f a -> Int
-- count = getSum . runAp_ (\\_ -> Sum 1)
-- @
runAp_ :: Monoid m => (forall a. f a -> m) -> Ap f b -> m
runAp_ f = getConst . runAp (Const . f)

instance Functor (Ap f) where
  fmap f (Ap g) = Ap (\k -> fmap f (g k))

instance Apply (Ap f) where
  Ap f <.> Ap x = Ap (\k -> f k <*> x k)

instance Applicative (Ap f) where
  pure x = Ap (\_ -> pure x)
  Ap f <*> Ap x = Ap (\k -> f k <*> x k)

-- | A version of 'lift' that can be used with just a 'Functor' for @f@.
liftAp :: f a -> Ap f a
liftAp x = Ap (\k -> k x)

-- | Given a natural transformation from @f@ to @g@ this gives a monoidal natural transformation from @Ap f@ to @Ap g@.
hoistAp :: (forall a. f a -> g a) -> Ap f b -> Ap g b
hoistAp f (Ap g) = Ap (\k -> g (k . f))

-- | Interprets the free applicative functor over f using the semantics for
--   `pure` and `<*>` given by the Applicative instance for f.
--
--   prop> retractApp == runAp id
retractAp :: Applicative f => Ap f a -> f a
retractAp (Ap g) = g id

{- $examples

<examples/ValidationForm.hs Validation form>

-}
