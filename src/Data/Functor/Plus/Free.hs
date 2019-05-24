{-# LANGUAGE DeriveFoldable    #-}
{-# LANGUAGE DeriveFunctor     #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE RankNTypes        #-}

module Data.Functor.Plus.Free (
    ListF(..)
  , runListF
  , liftListF
  , hoistListF
  ) where

import           Data.Functor.Plus

-- | The free 'Plus'
newtype ListF f a = ListF { plusses :: [f a] }
  deriving (Functor, Foldable, Traversable)

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

-- | A version of 'lift' that can be used with any @f@.
liftListF :: f a -> ListF f a
liftListF x = ListF [x]

-- | Given a natural transformation from @f@ to @g@, this gives a canonical
-- natural transformation from @'ListF' f@ to @'ListF' g@.
hoistListF
    :: (forall a. f a -> g a)
    -> ListF f b
    -> ListF g b
hoistListF f (ListF xs) = ListF (fmap f xs)
