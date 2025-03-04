{-# LANGUAGE DeriveFunctor       #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving  #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeInType          #-}
{-# LANGUAGE TypeOperators       #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Functor.Apply.Free
-- Copyright   :  (C) 2008-2015 Edward Kmett
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  provisional
-- Portability :  MPTCs, fundeps
--
-- Applys for free
----------------------------------------------------------------------------
module Data.Functor.Apply.Free (
    Ap1(..)
  , liftAp1
  , hoistAp1
  , runAp1
  , toAp
  ) where

import           Control.Applicative.Free
import           Data.Function
import           Data.Functor.Apply

-- | The free 'Apply'.  Basically a "non-empty" 'Ap'.
--
-- Represents multiple @f@s sequenced together.  The producer may provide
-- several (at least one), and the consumer must consume all of them to
-- produce the final @a@.
--
-- The construction here is based on 'Ap', similar to now
-- 'Data.List.NonEmpty.NonEmpty' is built on list.
data Ap1 f a where
    Ap1 :: f a -> Ap f (a -> b) -> Ap1 f b

deriving instance Functor (Ap1 f)

instance Apply (Ap1 f) where
    Ap1 x xs <.> ys = Ap1 x (flip <$> xs <*> toAp ys)

-- | Lift an @f@ into @'Ap1' f@.
liftAp1 :: f a -> Ap1 f a
liftAp1 x = Ap1 x (Pure id)

-- | Given a natural transformation from @f@ to @g@, this gives a canonical
-- natural transformation from @'Ap1' f@ to @g@.
runAp1
    :: Apply g
    => (forall x. f x -> g x)
    -> Ap1 f a
    -> g a
runAp1 f (Ap1 x xs) = runAp1_ f x xs

-- | Given a natural transformation from @f@ to @g@, this gives a canonical
-- natural transformation from @'Ap1' f@ to @'Ap1' g@.
hoistAp1
    :: (forall x. f x -> g x)
    -> Ap1 f a
    -> Ap1 g a
hoistAp1 f (Ap1 x xs) = Ap1 (f x) (hoistAp f xs)

runAp1_
    :: forall f g a b. Apply g
    => (forall x. f x -> g x)
    -> f a
    -> Ap f (a -> b)
    -> g b
runAp1_ f = go
  where
    go :: f x -> Ap f (x -> y) -> g y
    go x = \case
      Pure y  ->   y <$> f x
      Ap y ys -> (&) <$> f x <.> go y ys
{-# INLINE runAp1_ #-}

-- | Convert an 'Ap1' into an 'Ap', gaining an 'Applicative' instance in
-- the process.
toAp :: Ap1 f a -> Ap f a
toAp (Ap1 x xs) = Ap x xs

