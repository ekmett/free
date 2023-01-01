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

{- $note_eq1

This comment section is an internal documentation, but written in proper
Haddock markup. It is to allow rendering them to ease reading this rather long document.

=== About the definition of @Eq1 (Ap f)@ instance

The @Eq1 (Ap f)@ instance below have a complex definition. This comment
explains why it is defined like that.

The discussion given here also applies to @Ord1 (Ap f)@ instance with a little change.

==== General discussion about @Eq1@ type class

Currently, there isn't a law on @Eq1@ type class, but the following
property can be expected.

* If @Eq (f ())@, and @Functor f@ holds, @Eq1 f@ satisfies

    > liftEq (\_ _ -> True) x y == (() <$ x) == (() <$ y)

* If @Foldable f@ holds, @Eq1 f@ satisfies:

    * @boringEq x y@ implies @length (toList x) == length (toList y)@

    * @liftEq eq x y == liftEq (\_ _ -> True) && all (\(a,b) -> eq a b)) (zip (toList x) (toList y))@

Let's define the commonly used function @liftEq (\\_ _ -> True)@ as @boringEq@.

> boringEq :: Eq1 f => f a -> f b -> Bool
> boringEq = liftEq (\_ _ -> True)

Changing constant @True@ to constant @False@ in the @boringEq@, let @emptyEq@ function be defined.

> emptyEq :: Eq1 f => f a -> f b -> Bool
> emptyEq = liftEq (\_ _ -> False)

From the above properties expectated on a @Eq1@ instance, @emptyEq@ satisfies the following.

> emptyEq x y = boringEq x y && null (zip (toList x) (toList y))

==== About @instance (Eq1 (Ap f))@

If we're to define @Eq1 (Ap f)@ satisfying these properties expected, @Eq (Ap f ())@ will determine
how @liftEq@ should behave. It's not unreasonable to define equality between @Ap f ()@ as below.

> boringEqAp (Pure _) (Pure _) = True
> boringEqAp (Ap x1 y1) (Ap x2 y2) = boringEq x1 x2 && boringEqAp y1 y2
>    {-  = ((() <$ x1) == (() <$ x2)) && (y1 == y2)  -} 
> boringEqAp _ _ = False

Its type can be more general than equality between @Ap f ()@:

> boringEqAp :: Eq1 f => Ap f a -> Ap f b -> Bool

Using @boringEqAp@, the specification of @liftEq@ will be:

> liftEq eq x y = boringEqAp x y && and (zipWith eq (toList x) (toList y))

Then unfold @toList@ to remove the dependency to @Foldable@.

> liftEq eq (Pure a1) (Pure a2)
>   = boringEqAp (Pure a1) (Pure a2) && all (\(a,b) -> eq a b)) (zip (toList (Pure x)) (toList Pure y))
>   = True && all (\(a,b) -> eq a b) (zip [a1] [a2])
>   = eq a1 a2
> liftEq eq (Ap x1 y1) (Ap x2 y2)
>   = boringEqAp (Ap x1 y1) (Ap x2 y2) && all (\(b1, b2) -> eq b1 b2) (zip (toList (Ap x1 y1)) (toList (Ap x2 y2)))
>   = boringEq x1 y1 && boringEqAp y1 y2 && all (\(b1, b2) -> eq b1 b2) (zip (toList x1 <**> toList y1) (toList x2 <**> toList y2))
>   = boringEq x1 y1 && boringEqAp y1 y2 && all (\(b1, b2) -> eq b1 b2) (zip (as1 <**> gs1) (as2 <**> gs2))
>        where as1 = toList x1
>              as2 = toList x2
>              gs1 = toList y1
>              gs2 = toList y2
>   = boringEq x1 y1 && boringEqAp y1 y2 && all (\(a1, a2) -> all (\(g1, g2) -> eq (g1 a1) (g2 a2)) (zip gs1 gs2)) (zip as1 as2)

If @zip as1 as2@ is /not/ empty, the following transformation is valid.

> (...) | not (null (zip as1 as2))
>   = boringEq x1 x2 && boringEqAp y1 y2 && all (\(a1, a2) -> all (\(g1, g2) -> eq (g1 a1) (g2 a2)) (zip gs1 gs2)) (zip as1 as2)
>   = boringEq x1 x2 && all (\(a1, a2) -> boringEqAp y1 y2 && all (\(g1, g2) -> eq (g1 a1) (g2 a2)) (zip gs1 gs2)) (zip as1 as2)
> --                                      ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
>   = boringEq x1 x2 && all (\(a1, a2) -> liftEq (\g1 g2 -> eq (g1 a1) (g2 a2)) y1 y2) (zip as1 as2)
>   = liftEq (\a1 a2 -> liftEq (\g1 g2 -> eq (g1 a1) (g2 a2)) y1 y2)) x1 x2

Because, generally, the following transformation is valid if @xs@ is nonempty list.

> cond && all p xs = all (\x -> cond && p x) xs -- Only when xs is not empty!

If @zip as1 as2@ is empty, @all (...) (zip as1 as2)@ is vacuously true, so the following transformation is valid.

> (...) | null (zip as1 as2)
>   = boringEq x1 x2 && boringEqAp y1 y2 && all (\(a1, a2) -> all (\(g1, g2) -> eq (g1 a1) (g2 a2)) (zip gs1 gs2)) (zip as1 as2)
>   = boringEq x1 x2 && boringEqAp y1 y2

Combining two cases:

> liftEq eq (Ap x1 y1) (Ap x2 y2)
>   = null (zip as1 as2) && boringEq x1 x2 && boringEqAp y1 y2
>       || not (null (zip as1 as2)) && liftEq (\a1 a2 -> liftEq (\g1 g2 -> eq (g1 a1) (g2 a2)) y1 y2)) x1 x2
>   = null (zip as1 as2) && boringEq x1 x2 && boringEqAp y1 y2
>       || liftEq (\a1 a2 -> liftEq (\g1 g2 -> eq (g1 a1) (g2 a2)) y1 y2)) x1 x2
>   = emptyEq x1 x2 && boringEqAp y1 y2
>       || liftEq (\a1 a2 -> liftEq (\g1 g2 -> eq (g1 a1) (g2 a2)) y1 y2)) x1 x2

The property about @emptyEq@ is used in the last equation.

Hence it's defined as this source code.

-}

-- | Specialized 'boringEq' for @Ap f@.
#ifdef LIFTED_FUNCTOR_CLASSES
boringEqAp :: Eq1 f => Ap f a -> Ap f b -> Bool
#else
boringEqAp :: (Eq1 f, Functor f) => Ap f a -> Ap f b -> Bool
#endif
boringEqAp (Pure _) (Pure _) = True
boringEqAp (Ap x1 y1) (Ap x2 y2) = boringEq x1 x2 && boringEqAp y1 y2
boringEqAp _ _ = False

-- | Implementaion of 'liftEq' for @Ap f@.
#ifdef LIFTED_FUNCTOR_CLASSES
liftEqAp :: Eq1 f => (a -> b -> Bool) -> Ap f a -> Ap f b -> Bool
#else
liftEqAp :: (Eq1 f, Functor f) => (a -> b -> Bool) -> Ap f a -> Ap f b -> Bool
#endif
liftEqAp eq (Pure a1) (Pure a2) = eq a1 a2
liftEqAp eq (Ap x1 y1) (Ap x2 y2)
    -- This branching is not an optimization and necessary.
    -- See the above comment for more
  | emptyEq x1 x2 = boringEqAp y1 y2
  | otherwise =
      liftEq (\a1 a2 -> liftEqAp (\g1 g2 -> eq (g1 a1) (g2 a2)) y1 y2) x1 x2
liftEqAp _ _ _ = False

#ifdef LIFTED_FUNCTOR_CLASSES
instance Eq1 f => Eq1 (Ap f) where
  liftEq = liftEqAp
#else
instance (Eq1 f, Functor f) => Eq1 (Ap f) where
  eq1 = liftEqAp (==)
#endif

#ifdef LIFTED_FUNCTOR_CLASSES
instance (Eq1 f, Eq a) => Eq (Ap f a) where
#else
instance (Eq1 f, Functor f, Eq a) => Eq (Ap f a) where
#endif
  (==) = eq1

-- | Specialized 'boringCompare' for @Ap f@.
#ifdef LIFTED_FUNCTOR_CLASSES
boringCompareAp :: Ord1 f => Ap f a -> Ap f b -> Ordering
#else
boringCompareAp :: (Ord1 f, Functor f) => Ap f a -> Ap f b -> Ordering
#endif
boringCompareAp (Pure _) (Pure _) = EQ
boringCompareAp (Pure _) (Ap _ _) = LT
boringCompareAp (Ap x1 y1) (Ap x2 y2) = boringCompare x1 x2 `mappend` boringCompareAp y1 y2
boringCompareAp (Ap _ _) (Pure _) = GT

-- | Implementation of 'liftCompare' for @Ap f@
#ifdef LIFTED_FUNCTOR_CLASSES
liftCompareAp :: Ord1 f => (a -> b -> Ordering) -> Ap f a -> Ap f b -> Ordering
#else
liftCompareAp :: (Ord1 f, Functor f) => (a -> b -> Ordering) -> Ap f a -> Ap f b -> Ordering
#endif
liftCompareAp cmp (Pure a1) (Pure a2) = cmp a1 a2
liftCompareAp _   (Pure _) (Ap _ _) = LT
liftCompareAp cmp (Ap x1 y1) (Ap x2 y2)
    -- This branching is not an optimization and necessary.
    -- See the above comment for more
  | emptyEq x1 x2 = boringCompareAp y1 y2
  | otherwise     = liftCompare (\a1 a2 -> liftCompareAp (\g1 g2 -> cmp (g1 a1) (g2 a2)) y1 y2) x1 x2
liftCompareAp _   (Ap _ _) (Pure _) = GT

#ifdef LIFTED_FUNCTOR_CLASSES
instance Ord1 f => Ord1 (Ap f) where
  liftCompare = liftCompareAp
#else
instance (Ord1 f, Functor f) => Ord1 (Ap f) where
  compare1 = liftCompareAp compare
#endif

#ifdef LIFTED_FUNCTOR_CLASSES
instance (Ord1 f, Ord a) => Ord (Ap f a) where
#else
instance (Ord1 f, Functor f, Ord a) => Ord (Ap f a) where
#endif
  compare = compare1

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
