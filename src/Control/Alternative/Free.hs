{-# LANGUAGE CPP #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE Safe #-}

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
  , AltF(..)
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

infixl 3 `Ap`

data AltF f a where
  Ap     :: f a -> Alt f (a -> b) -> AltF f b
  Pure   :: a                     -> AltF f a

newtype Alt f a = Alt { alternatives :: [AltF f a] }

instance Functor (AltF f) where
  fmap f (Pure a) = Pure $ f a
  fmap f (Ap x g) = x `Ap` fmap (f .) g

instance Functor (Alt f) where
  fmap f (Alt xs) = Alt $ map (fmap f) xs

instance Applicative (AltF f) where
  pure = Pure
  {-# INLINE pure #-}
  (Pure f)   <*> y         = fmap f y      -- fmap
  y          <*> (Pure a)  = fmap ($ a) y  -- interchange
  (Ap a f)   <*> b         = a `Ap` (flip <$> f <*> (Alt [b]))
  {-# INLINE (<*>) #-}

instance Applicative (Alt f) where
  pure a = Alt [pure a]
  {-# INLINE pure #-}

  (Alt xs) <*> ys = Alt (xs >>= alternatives . (`ap'` ys))
    where
      ap' :: AltF f (a -> b) -> Alt f a -> Alt f b

      Pure f `ap'` u      = fmap f u
      (u `Ap` f) `ap'` v  = Alt [u `Ap` (flip <$> f) <*> v]
  {-# INLINE (<*>) #-}

liftAltF :: f a -> AltF f a
liftAltF x = x `Ap` pure id
{-# INLINE liftAltF #-}

-- | A version of 'lift' that can be used with any @f@.
liftAlt :: f a -> Alt f a
liftAlt = Alt . (:[]) . liftAltF
{-# INLINE liftAlt #-}

-- | Given a natural transformation from @f@ to @g@, this gives a canonical monoidal natural transformation from @'Alt' f@ to @g@.
runAlt :: forall f g a. Alternative g => (forall x. f x -> g x) -> Alt f a -> g a
runAlt u xs0 = go xs0 where

  go  :: Alt f b -> g b
  go (Alt xs) = foldr (\r a -> (go2 r) <|> a) empty xs

  go2 :: AltF f b -> g b
  go2 (Pure a) = pure a
  go2 (Ap x f) = flip id <$> u x <*> go f
{-# INLINABLE runAlt #-}

instance Apply (Alt f) where
  (<.>) = (<*>)
  {-# INLINE (<.>) #-}

instance Alt.Alt (Alt f) where
  (<!>) = (<|>)
  {-# INLINE (<!>) #-}

instance Alternative (Alt f) where
  empty = Alt []
  {-# INLINE empty #-}
  Alt as <|> Alt bs = Alt (as ++ bs)
  {-# INLINE (<|>) #-}

instance Semigroup (Alt f a) where
  (<>) = (<|>)
  {-# INLINE (<>) #-}

instance Monoid (Alt f a) where
  mempty = empty
  {-# INLINE mempty #-}
  mappend = (<>)
  {-# INLINE mappend #-}
  mconcat as = Alt (as >>= alternatives)
  {-# INLINE mconcat #-}

hoistAltF :: (forall a. f a -> g a) -> AltF f b -> AltF g b
hoistAltF _ (Pure a) = Pure a
hoistAltF f (Ap x y) = Ap (f x) (hoistAlt f y)
{-# INLINE hoistAltF #-}

-- | Given a natural transformation from @f@ to @g@ this gives a monoidal natural transformation from @Alt f@ to @Alt g@.
hoistAlt :: (forall a. f a -> g a) -> Alt f b -> Alt g b
hoistAlt f (Alt as) = Alt (map (hoistAltF f) as)
{-# INLINE hoistAlt #-}
