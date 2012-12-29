{-# LANGUAGE CPP #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE GADTs #-}
{-# OPTIONS_GHC -Wall #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Control.Alternative.Free
-- Copyright   :  (C) 2012 Edward Kmett
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  provisional
-- Portability :  GADTs, Rank2Types
--
-- Left distributive 'Alternative' functors for free, based on a design
-- by Stijn van Drongelen.
----------------------------------------------------------------------------
module Control.Alternative.Free
  ( Alt(..)
  , runAlt
  , liftAlt
  , hoistAlt
  ) where

import Control.Applicative
import Data.Functor.Apply
import Data.Semigroup

#ifdef GHC_TYPEABLE
import Data.Typeable
#endif

-- | The free 'Applicative' for a 'Functor' @f@.
data Alt f a where
  Pure :: a -> Alt f a
  Ap   :: f a -> Alt f (a -> b) -> Alt f b
  Alt  :: [Alt f a] -> Alt f a

-- | Given a natural transformation from @f@ to @g@, this gives a canonical monoidal natural transformation from @'Ap' f@ to @g@.
runAlt :: Alternative g => (forall x. f x -> g x) -> Alt f a -> g a
runAlt _ (Pure x) = pure x
runAlt u (Ap f x) = flip id <$> u f <*> runAlt u x
runAlt u (Alt as) = foldr (\a r -> runAlt u a <|> r) empty as

instance Functor (Alt f) where
  fmap f (Pure a)   = Pure (f a)
  fmap f (Ap x y)   = Ap x ((f .) <$> y)
  fmap f (Alt as)   = Alt (fmap f <$> as)

instance Apply (Alt f) where
  Pure f <.> y = fmap f y
  Ap x y <.> z = Ap x (flip <$> y <.> z)
  Alt as <.> z = Alt (map (<.> z) as) -- This assumes 'left distribution'

instance Applicative (Alt f) where
  pure = Pure
  Pure f <*> y = fmap f y
  Ap x y <*> z = Ap x (flip <$> y <*> z)
  Alt as <*> z = Alt (map (<*> z) as) -- This assumes 'left distribution'

instance Alternative (Alt f) where
  empty = Alt []
  {-# INLINE empty #-}
  Alt [] <|> r      = r
  l      <|> Alt [] = l
  Alt as <|> Alt bs = Alt (as ++ bs)
  l      <|> r      = Alt [l, r]
  {-# INLINE (<|>) #-}

instance Semigroup (Alt f a) where
  (<>) = (<|>)
  {-# INLINE (<>) #-}

instance Monoid (Alt f a) where
  mempty = empty
  {-# INLINE mempty #-}
  mappend = (<|>)
  {-# INLINE mappend #-}
  mconcat as = fromList (as >>= toList)
    where
      toList (Alt xs) = xs
      toList x       = [x]
      fromList [x] = x
      fromList xs  = Alt xs
  {-# INLINE mconcat #-}

-- | A version of 'lift' that can be used with just a 'Functor' for @f@.
liftAlt :: f a -> Alt f a
liftAlt x = Ap x (Pure id)
{-# INLINE liftAlt #-}

-- | Given a natural transformation from @f@ to @g@ this gives a monoidal natural transformation from @Ap f@ to @Ap g@.
hoistAlt :: (forall a. f a -> g a) -> Alt f b -> Alt g b
hoistAlt _ (Pure a) = Pure a
hoistAlt f (Ap x y) = Ap (f x) (hoistAlt f y)
hoistAlt f (Alt as) = Alt (map (hoistAlt f) as)

#ifdef GHC_TYPEABLE
instance Typeable1 f => Typeable1 (Alt f) where
  typeOf1 t = mkTyConApp altTyCon [typeOf1 (f t)] where
    f :: Alt f a -> f a
    f = undefined

altTyCon :: TyCon
#if __GLASGOW_HASKELL__ < 704
altTyCon = mkTyCon "Control.Alternative.Free.Alt"
#else
altTyCon = mkTyCon3 "free" "Control.Alternative.Free" "Alt"
#endif
{-# NOINLINE altTyCon #-}

#endif
