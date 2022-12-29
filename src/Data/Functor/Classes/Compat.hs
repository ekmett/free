#include "free-common.h"
#ifdef LIFTED_FUNCTOR_CLASSES
{-# LANGUAGE Safe #-}
module Data.Functor.Classes.Compat (
    mappend,
    boringEq,
    emptyEq,
    boringCompare,
    module Data.Functor.Classes,
    ) where

import Data.Functor.Classes

#if !(MIN_VERSION_base(4,8,0))
import Data.Monoid (mappend)
#endif

boringEq :: Eq1 f => f a -> f b -> Bool
boringEq = liftEq (\_ _ -> True)

emptyEq :: Eq1 f => f a -> f b -> Bool
emptyEq = liftEq (\_ _ -> False)

boringCompare :: Ord1 f => f a -> f b -> Ordering
boringCompare = liftCompare (\_ _ -> EQ)
#else
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE Trustworthy #-}
module Data.Functor.Classes.Compat (
    Lift1 (..),
    on,
    boringEq,
    emptyEq,
    liftEq,
    boringCompare,
    liftCompare,
    module Data.Functor.Classes,
    ) where

-------------------------------------------------------------------------------
-- transformers-0.4 helpers, copied from prelude-extras
-------------------------------------------------------------------------------

# if !(MIN_VERSION_base(4,8,0))
import Data.Foldable
import Data.Traversable
# endif
import Data.Functor.Classes
import Data.Function (on)

-- If Show1 and Read1 are ever derived by the same mechanism as
-- Show and Read, rather than GND, that will change their behavior
-- here.
newtype Lift1 f a = Lift1 { lower1 :: f a }
  deriving (Functor, Foldable, Traversable, Eq1, Ord1, Show1, Read1)

instance (Eq1 f, Eq a) => Eq (Lift1 f a)       where (==) = eq1
instance (Ord1 f, Ord a) => Ord (Lift1 f a)    where compare = compare1
instance (Show1 f, Show a) => Show (Lift1 f a) where showsPrec = showsPrec1
instance (Read1 f, Read a) => Read (Lift1 f a) where readsPrec = readsPrec1

boringEq :: (Eq1 f, Functor f) => f a -> f b -> Bool
boringEq fa fb = eq1 (() <$ fa) (() <$ fb)

-- | Internal only, do not export
data AlwaysFalse = AlwaysFalse

instance Eq AlwaysFalse where
  _ == _ = False

emptyEq :: (Eq1 f, Functor f) => f a -> f b -> Bool
emptyEq fa fb = eq1 (AlwaysFalse <$ fa) (AlwaysFalse <$ fb)

-- | Internal only, do not export
data EqualityTmp b = EqualityLeft (b -> Bool) | EqualityRight b

instance Eq (EqualityTmp b) where
  EqualityLeft f == EqualityRight x = f x
  EqualityRight x == EqualityLeft f = f x
  _ == _ = error "Undefined combination for equality"

-- | Emulated @liftEq@ using old @eq1@
liftEq :: (Eq1 f, Functor f) => (a -> b -> Bool) -> f a -> f b -> Bool
liftEq eq fa fb = eq1 (fmap (EqualityLeft . eq) fa) (fmap EqualityRight fb)

boringCompare :: (Ord1 f, Functor f) => f a -> f b -> Ordering
boringCompare fa fb = compare1 (() <$ fa) (() <$ fb)

-- | Internal only, do not export
data ComparisonTmp b = ComparisonLeft (b -> Ordering) | ComparisonRight b

instance Eq (ComparisonTmp b) where
  x == y = compare x y == EQ
instance Ord (ComparisonTmp b) where
  compare (ComparisonLeft f) (ComparisonRight b) = f b
  compare (ComparisonRight b) (ComparisonLeft f) = case f b of
    LT -> GT
    EQ -> EQ
    GT -> LT
  compare _ _ = error "Unexpected combination for comparison"

-- | Emulated @liftCompare@ using old @compare1@
liftCompare :: (Ord1 f, Functor f) => (a -> b -> Ordering) -> f a -> f b -> Ordering
liftCompare cmp fa fb = compare1 (fmap (ComparisonLeft . cmp) fa) (fmap ComparisonRight fb)
#endif
