{-# LANGUAGE DeriveFoldable    #-}
{-# LANGUAGE DeriveFunctor     #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE RankNTypes        #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Functor.Plus.Free
-- Copyright   :  (C) 2008-2015 Edward Kmett
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  provisional
-- Portability :  MPTCs, fundeps
--
-- Plusses for free.
----------------------------------------------------------------------------
module Data.Functor.Plus.Free (
    ListF(..)
  , runListF
  , liftListF
  , hoistListF
  ) where

import           Data.Functor.Plus

-- | The free 'Plus'.  Represents a free "choice" of @f a@s.  The producer
-- can supply as many as they like, and the consumer has the free choice to
-- use any that they like.
newtype ListF f a = ListF { plusses :: [f a] }
  deriving (Functor, Foldable, Traversable, Show, Eq, Ord, Read)

instance Functor f => Alt (ListF f) where
    ListF xs <!> ListF ys = ListF (xs <> ys)

instance Functor f => Plus (ListF f) where
    zero = ListF []

instance Semigroup (ListF f a) where
    ListF xs <> ListF ys = ListF (xs <> ys)

instance Monoid (ListF f a) where
    mempty = ListF []

-- | Given a natural transformation from @f@ to @g@, this gives a canonical
-- natural transformation from @'ListF' f@ to @g@.
runListF
    :: Plus g
    => (forall x. f x -> g x)
    -> ListF f a
    -> g a
runListF f (ListF xs) = foldr ((<!>) . f) zero xs

-- | Lift an @f@ into @'ListF' f@.
liftListF :: f a -> ListF f a
liftListF x = ListF [x]

-- | Given a natural transformation from @f@ to @g@, this gives a canonical
-- natural transformation from @'ListF' f@ to @'ListF' g@.
hoistListF
    :: (forall a. f a -> g a)
    -> ListF f b
    -> ListF g b
hoistListF f (ListF xs) = ListF (fmap f xs)
