{-# LANGUAGE CPP #-}
{-# LANGUAGE RankNTypes #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Control.Alternative.Free.Final
-- Copyright   :  (C) 2012 Edward Kmett
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  provisional
-- Portability :  GADTs, Rank2Types
--
-- Final encoding of free 'Alternative' functors.
----------------------------------------------------------------------------
module Control.Alternative.Free.Final
  ( Alt(..)
  , runAlt
  , liftAlt
  , hoistAlt
  ) where

import Control.Applicative
import Data.Functor.Apply
import Data.Functor.Alt ((<!>))
import qualified Data.Functor.Alt as Alt

#if !(MIN_VERSION_base(4,11,0))
import Data.Semigroup
#endif

-- | The free 'Alternative' for any @f@.
newtype Alt f a = Alt { _runAlt :: forall g. Alternative g => (forall x. f x -> g x) -> g a }

instance Functor (Alt f) where
  fmap f (Alt g) = Alt (\k -> fmap f (g k))

instance Apply (Alt f) where
  Alt f <.> Alt x = Alt (\k -> f k <*> x k)

instance Applicative (Alt f) where
  pure x = Alt (\_ -> pure x)
  Alt f <*> Alt x = Alt (\k -> f k <*> x k)

instance Alt.Alt (Alt f) where
  Alt x <!> Alt y = Alt (\k -> x k <|> y k)

instance Alternative (Alt f) where
  empty = Alt (\_ -> empty)
  Alt x <|> Alt y = Alt (\k -> x k <|> y k)
  some (Alt x) = Alt $ \k -> some (x k)
  many (Alt x) = Alt $ \k -> many (x k)

instance Semigroup (Alt f a) where
  (<>) = (<|>)

instance Monoid (Alt f a) where
  mempty = empty
  mappend = (<>)

-- | A version of 'lift' that can be used with @f@.
liftAlt :: f a -> Alt f a
liftAlt f = Alt (\k -> k f)

-- | Given a natural transformation from @f@ to @g@, this gives a canonical monoidal natural transformation from @'Alt' f@ to @g@.
runAlt :: forall f g a. Alternative g => (forall x. f x -> g x) -> Alt f a -> g a
runAlt phi g = _runAlt g phi

-- | Given a natural transformation from @f@ to @g@ this gives a monoidal natural transformation from @Alt f@ to @Alt g@.
hoistAlt :: (forall a. f a -> g a) -> Alt f b -> Alt g b
hoistAlt phi (Alt g) = Alt (\k -> g (k . phi))

