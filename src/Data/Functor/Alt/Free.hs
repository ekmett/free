{-# LANGUAGE DeriveFoldable    #-}
{-# LANGUAGE DeriveFunctor     #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE RankNTypes        #-}

module Data.Functor.Alt.Free (
    NonEmptyF(..)
  , runNonEmptyF
  , liftNonEmptyF
  , hoistNonEmptyF
  , toListF
  ) where

import           Data.Functor.Alt
import           Data.Functor.Plus.Free
import           Data.List.NonEmpty         (NonEmpty(..))
import           Data.Semigroup.Foldable
import           Data.Semigroup.Traversable
import qualified Data.List.NonEmpty         as NE

-- | The free 'Alt'
newtype NonEmptyF f a = NonEmptyF { alts :: NonEmpty (f a) }
  deriving (Functor, Foldable, Traversable)

instance Functor f => Alt (NonEmptyF f) where
    NonEmptyF xs <!> NonEmptyF ys = NonEmptyF (xs <> ys)

instance Semigroup (NonEmptyF f a) where
    NonEmptyF xs <> NonEmptyF ys = NonEmptyF (xs <> ys)

instance Foldable1 f => Foldable1 (NonEmptyF f) where
    foldMap1 f (NonEmptyF ys) = (foldMap1 . foldMap1) f ys

instance Traversable1 f => Traversable1 (NonEmptyF f) where
    traverse1 f (NonEmptyF ys) = NonEmptyF <$> (traverse1 . traverse1) f ys

-- | Given a natural transformation from @f@ to @g@, this gives a canonical
-- natural transformation from @'NonEmptyF' f@ to @g@.
runNonEmptyF
    :: Alt g
    => (forall x. f x -> g x)
    -> NonEmptyF f a
    -> g a
runNonEmptyF f (NonEmptyF xs) = asum1 (fmap f xs)

-- | A version of 'lift' that can be used with any @f@.
liftNonEmptyF :: f a -> NonEmptyF f a
liftNonEmptyF x = NonEmptyF (x :| [])

-- | Given a natural transformation from @f@ to @g@, this gives a canonical
-- natural transformation from @'NonEmptyF' f@ to @'NonEmptyF' g@.
hoistNonEmptyF
    :: (forall a. f a -> g a)
    -> NonEmptyF f b
    -> NonEmptyF g b
hoistNonEmptyF f (NonEmptyF xs) = NonEmptyF (fmap f xs)

-- | Convert a 'NonEmptyF' into a 'ListF', gaining a 'Plus' instance in the
-- process.
toListF :: NonEmptyF f a -> ListF f a
toListF (NonEmptyF xs) = ListF (NE.toList xs)
