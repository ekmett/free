{-# LANGUAGE CPP #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE GADTs #-}
#if __GLASGOW_HASKELL__ >= 707
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE Safe #-}
#else
-- Manual Typeable instances
{-# LANGUAGE Trustworthy #-}
#endif
#include "free-common.h"

-----------------------------------------------------------------------------
-- |
-- Module      :  Control.Applicative.Free
-- Copyright   :  (C) 2012-2013 Edward Kmett
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  provisional
-- Portability :  GADTs, Rank2Types
--
-- 'Applicative' functors for free
----------------------------------------------------------------------------
module Control.Applicative.Free
  (
  -- | Compared to the free monad, they are less expressive. However, they are also more
  -- flexible to inspect and interpret, as the number of ways in which
  -- the values can be nested is more limited.
  --
  -- See <http://arxiv.org/abs/1403.0749 Free Applicative Functors>,
  -- by Paolo Capriotti and Ambrus Kaposi, for some applications.

    Ap(..)
  , runAp
  , runAp_
  , liftAp
  , iterAp
  , hoistAp
  , retractAp

  -- * Examples
  -- $examples
  ) where

import Control.Applicative
import Control.Comonad (Comonad(..))
import Data.Functor.Apply
import Data.Typeable
import Data.Functor.Classes.Compat

#if !(MIN_VERSION_base(4,8,0))
import Data.Monoid
#endif

-- | The free 'Applicative' for a 'Functor' @f@.
data Ap f a where
  Pure :: a -> Ap f a
  Ap   :: f a -> Ap f (a -> b) -> Ap f b
#if __GLASGOW_HASKELL__ >= 707
  deriving Typeable
#endif

-- | Given a natural transformation from @f@ to @g@, this gives a canonical monoidal natural transformation from @'Ap' f@ to @g@.
--
-- prop> runAp t == retractApp . hoistApp t
runAp :: Applicative g => (forall x. f x -> g x) -> Ap f a -> g a
runAp _ (Pure x) = pure x
runAp u (Ap f x) = flip id <$> u f <*> runAp u x

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
  fmap f (Pure a)   = Pure (f a)
  fmap f (Ap x y)   = Ap x ((f .) <$> y)

instance Apply (Ap f) where
  Pure f <.> y = fmap f y
  Ap x y <.> z = Ap x (flip <$> y <.> z)

instance Applicative (Ap f) where
  pure = Pure
  Pure f <*> y = fmap f y
  Ap x y <*> z = Ap x (flip <$> y <*> z)

instance Comonad f => Comonad (Ap f) where
  extract (Pure a) = a
  extract (Ap x y) = extract y (extract x)
  duplicate (Pure a) = Pure (Pure a)
  duplicate (Ap x y) = Ap (duplicate x) (extend (flip Ap) y)

instance (Eq1 f, Eq a) => Eq (Ap f a) where
  (==) = eq1

instance Eq1 f => Eq1 (Ap f) where
  liftEq eq (Pure a1) (Pure a2) = eq a1 a2
  liftEq eq (Ap x1 y1) (Ap x2 y2)
    | emptyEq x1 x2 = boringEqAp1 y1 y2
    | otherwise = liftEq (\a1 a2 -> liftEq (\g1 g2 -> eq (g1 a1) (g2 a2)) y1 y2) x1 x2
  liftEq _ _ _ = False

instance (Ord1 f, Ord a) => Ord (Ap f a) where
  compare = compare1

instance Ord1 f => Ord1 (Ap f) where
  liftCompare cmp (Pure a1) (Pure a2) = cmp a1 a2
  liftCompare _   (Pure _) (Ap _ _) = LT
  liftCompare cmp (Ap x1 y1) (Ap x2 y2)
    | emptyEq x1 x2 = boringCompareAp1 y1 y2
    | otherwise     = liftCompare (\a1 a2 -> liftCompare (\g1 g2 -> cmp (g1 a1) (g2 a2)) y1 y2) x1 x2
  liftCompare _   (Ap _ _) (Pure _) = GT

-- | @emptyEq = 'liftEq' (\_ _ -> False)@
--
--   When @f@ is 'Traversable', there is a function recognizing that an functor
--   contains no value:
--   
--   > toEmpty :: Traversable f => f a -> Maybe (f b)
--   > toEmpty = traverse (const Nothing)
--   
--   Using @toEmpty@, for any @eq :: c -> d -> Bool@, @emptyEq@ is equivalent to the following function
--   
--   > emptyEq fa fb = case (,) <$> toEmpty fa <*> toEmpty fb of
--   >    Just (fc,fd) -> liftEq eq fc fd
--   >    Nothing      -> False
emptyEq :: Eq1 f => f a -> f b -> Bool
emptyEq = liftEq (\_ _ -> False)

-- | @boringEq = 'liftEq' (\_ _ -> True)@
--
--   When @f@ is 'Functor', it's equivalent to the following definition
--
--   > boringEq = (==) \`'on'\` fmap (const ())
boringEq :: Eq1 f => f a -> f b -> Bool
boringEq = liftEq (\_ _ -> True)

-- | 'boringEq' optimized for @Ap f@
boringEqAp1 :: Eq1 f => Ap f a -> Ap f b -> Bool
boringEqAp1 (Pure _) (Pure _) = True
boringEqAp1 (Ap x1 y1) (Ap x2 y2) = boringEq x1 x2 && boringEqAp1 y1 y2
boringEqAp1 _ _ = False

-- | @boringEq = 'liftCompare' (\_ _ -> EQ)@
--
--   When @f@ is 'Functor', it's equivalent to the following definition
--
--   > boringCompare = compare \`'on'\` fmap (const ())
boringCompare :: Ord1 f => f a -> f b -> Ordering
boringCompare = liftCompare (\_ _ -> EQ)

-- | 'boringCompare' optimized for @Ap f@
boringCompareAp1 :: Ord1 f => Ap f a -> Ap f b -> Ordering
boringCompareAp1 (Pure _) (Pure _) = EQ
boringCompareAp1 (Pure _) (Ap _ _) = LT
boringCompareAp1 (Ap x1 y1) (Ap x2 y2) = boringCompare x1 x2 <> boringCompareAp1 y1 y2
boringCompareAp1 (Ap _ _) (Pure _) = GT

-- | A version of 'lift' that can be used with just a 'Functor' for @f@.
liftAp :: f a -> Ap f a
liftAp x = Ap x (Pure id)
{-# INLINE liftAp #-}

-- | Tear down a free 'Applicative' using iteration.
iterAp :: Functor g => (g a -> a) -> Ap g a -> a
iterAp algebra = go
  where go (Pure a) = a
        go (Ap underlying apply) = algebra (go . (apply <*>) . pure <$> underlying)

-- | Given a natural transformation from @f@ to @g@ this gives a monoidal natural transformation from @Ap f@ to @Ap g@.
hoistAp :: (forall a. f a -> g a) -> Ap f b -> Ap g b
hoistAp _ (Pure a) = Pure a
hoistAp f (Ap x y) = Ap (f x) (hoistAp f y)

-- | Interprets the free applicative functor over f using the semantics for
--   `pure` and `<*>` given by the Applicative instance for f.
--
--   prop> retractApp == runAp id
retractAp :: Applicative f => Ap f a -> f a
retractAp (Pure a) = pure a
retractAp (Ap x y) = x <**> retractAp y

#if __GLASGOW_HASKELL__ < 707
instance Typeable1 f => Typeable1 (Ap f) where
  typeOf1 t = mkTyConApp apTyCon [typeOf1 (f t)] where
    f :: Ap f a -> f a
    f = undefined

apTyCon :: TyCon
#if __GLASGOW_HASKELL__ < 704
apTyCon = mkTyCon "Control.Applicative.Free.Ap"
#else
apTyCon = mkTyCon3 "free" "Control.Applicative.Free" "Ap"
#endif
{-# NOINLINE apTyCon #-}

#endif

{- $examples

<examples/ValidationForm.hs Validation form>

-}
