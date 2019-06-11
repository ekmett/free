{-# LANGUAGE CPP                  #-}
{-# LANGUAGE DeriveFoldable       #-}
{-# LANGUAGE DeriveFunctor        #-}
{-# LANGUAGE DeriveTraversable    #-}
{-# LANGUAGE RankNTypes           #-}
{-# LANGUAGE StandaloneDeriving   #-}
{-# LANGUAGE UndecidableInstances #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Functor.Bind.Free
-- Copyright   :  (C) 2008-2015 Edward Kmett
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  provisional
-- Portability :  MPTCs, fundeps
--
-- Binds for free
----------------------------------------------------------------------------
module Data.Functor.Bind.Free (
    Free1(..)
  , liftFree1
  , runFree1
  , hoistFree1
  , toFree
  ) where

import           Control.Monad.Free
import           Data.Functor.Bind

-- | The free 'Bind' on @f@.  Can be considered a "non-empty" 'Free'.
--
-- The producer may provide many (at least one) "ordered" @f@s, and the
-- consumer must consume them sequentially.
--
-- The construction here is inspired by iteratees.
data Free1 f a = Done (f a)
               | More (f (Free1 f a))
  deriving (Functor, Foldable, Traversable)

deriving instance (Show (f a), Show (f (Free1 f a))) => Show (Free1 f a)
deriving instance (Read (f a), Read (f (Free1 f a))) => Read (Free1 f a)
deriving instance (Eq (f a), Eq (f (Free1 f a))) => Eq (Free1 f a)
deriving instance (Ord (f a), Ord (f (Free1 f a))) => Ord (Free1 f a)

instance Functor f => Apply (Free1 f) where
    (<.>) = apDefault

instance Functor f => Bind (Free1 f) where
    Done x >>- f = More $ fmap f x
    More x >>- f = More $ fmap (>>- f) x

-- | Lift an @f@ into @'Free1' f@.
liftFree1 :: f a -> Free1 f a
liftFree1 = Done

-- | Given a natural transformation from @f@ to @g@, this gives a canonical
-- natural transformation from @'Free1' f@ to @g@.
runFree1
    :: Bind g
    => (forall x. f x -> g x)
    -> Free1 f a
    -> g a
runFree1 f = go
  where
    go (Done x) = f x
    go (More x) = f x >>- go

-- | Given a natural transformation from @f@ to @g@, this gives a canonical
-- natural transformation from @'Free1' f@ to @'Free1' g@.
hoistFree1
    :: Functor g
    => (forall x. f x -> g x)
    -> Free1 f a
    -> Free1 g a
hoistFree1 f = go
  where
    go (Done x) = Done (f x)
    go (More x) = More (go <$> f x)

-- | Convert an 'Free1' into any instance of 'MonadFree'.
toFree :: (MonadFree f m, Functor f) => Free1 f a -> m a
toFree (Done x) = liftF x
toFree (More x) = wrap (fmap toFree x)
