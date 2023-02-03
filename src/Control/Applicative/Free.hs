{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE Safe #-}

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
import Data.Foldable
import Data.Semigroup.Foldable
import Data.Functor.Classes

import Prelude hiding (null)

-- | The free 'Applicative' for a 'Functor' @f@.
data Ap f a where
  Pure :: a -> Ap f a
  Ap   :: f a -> Ap f (a -> b) -> Ap f b

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

-- | @foldMap f == foldMap f . 'runAp' 'Data.Foldable.toList'@
instance Foldable f => Foldable (Ap f) where
  foldMap f (Pure a) = f a
  foldMap f (Ap x y) = foldMap (\a -> foldMap (\g -> f (g a)) y) x

  null (Pure _) = False
  null (Ap x y) = null x || null y

  length = go 1
    where
      -- This type annotation is required to do polymorphic recursion
      go :: Foldable t => Int -> Ap t a -> Int
      go n (Pure _) = n
      go n (Ap x y) = case n * length x of
        0  -> 0
        n' -> go n' y

-- | @foldMap f == foldMap f . 'runAp' 'toNonEmpty'@
instance Foldable1 f => Foldable1 (Ap f) where
  foldMap1 f (Pure a) = f a
  foldMap1 f (Ap x y) = foldMap1 (\a -> foldMap1 (\g -> f (g a)) y) x


{- $note_eq1

This comment section is an internal documentation, but written in proper
Haddock markup. It is to allow rendering them to ease reading this rather long document.

=== About the definition of @Eq1 (Ap f)@ instance

The @Eq1 (Ap f)@ instance below has a complex definition. This comment
explains why it is defined like that.

The discussion given here also applies to @Ord1 (Ap f)@ instance with a little change.

==== General discussion about @Eq1@ type class

Currently, there isn't a law on the @Eq1@ type class, but the following
properties can be expected.

* If @Eq (f ())@, and @Functor f@ holds, @Eq1 f@ satisfies

    > liftEq (\_ _ -> True) x y == (() <$ x) == (() <$ y)

* If @Foldable f@ holds, @Eq1 f@ satisfies:

    * @boringEq x y@ implies @length (toList x) == length (toList y)@

    * @liftEq eq x y == liftEq (\_ _ -> True) && all (\(a,b) -> eq a b)) (zip (toList x) (toList y))@

Let's define the commonly used function @liftEq (\\_ _ -> True)@ as @boringEq@.

> boringEq :: Eq1 f => f a -> f b -> Bool
> boringEq = liftEq (\_ _ -> True)

Changing the constant @True@ to the constant @False@ in the definition of
@boringEq@, let @emptyEq@ function be defined as:

> emptyEq :: Eq1 f => f a -> f b -> Bool
> emptyEq = liftEq (\_ _ -> False)

From the above properties expectated on a @Eq1@ instance, @emptyEq@ satisfies the following.

> emptyEq x y = boringEq x y && null (zip (toList x) (toList y))

==== About @instance (Eq1 (Ap f))@

If we're to define @Eq1 (Ap f)@ satisfying these properties as expected, @Eq (Ap f ())@ will determine
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

Because, generally, the following transformation is valid if @xs@ is a nonempty list.

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
boringEqAp :: Eq1 f => Ap f a -> Ap f b -> Bool
boringEqAp (Pure _) (Pure _) = True
boringEqAp (Ap x1 y1) (Ap x2 y2) = boringEq x1 x2 && boringEqAp y1 y2
boringEqAp _ _ = False

-- | Implementaion of 'liftEq' for @Ap f@.
liftEqAp :: Eq1 f => (a -> b -> Bool) -> Ap f a -> Ap f b -> Bool
liftEqAp eq (Pure a1) (Pure a2) = eq a1 a2
liftEqAp eq (Ap x1 y1) (Ap x2 y2)
    -- This branching is necessary and not just an optimization.
    -- See the above comment for more
  | emptyEq x1 x2 = boringEqAp y1 y2
  | otherwise =
      liftEq (\a1 a2 -> liftEqAp (\g1 g2 -> eq (g1 a1) (g2 a2)) y1 y2) x1 x2
liftEqAp _ _ _ = False

-- | @boringEq fa fb@ tests if @fa@ and @fb@ are equal ignoring any difference between
--   their content (the values of their last parameters @a@ and @b@.)
--
--   It is named \'boring\' because the type parameters @a@ and @b@ are
--   treated as if they are the most boring type @()@.
boringEq :: Eq1 f => f a -> f b -> Bool
boringEq = liftEq (\_ _ -> True)

-- | @emptyEq fa fb@ tests if @fa@ and @fb@ are equal /and/ they don't have any content
--   (the values of their last parameters @a@ and @b@.)
--
--   It is named \'empty\' because it only tests for values without any content,
--   like an empty list or @Nothing@.
--
--   If @f@ is also @Foldable@, @emptyEq fa fb@ would be equivalent to
--   @null fa && null fb && liftEq eq@ for any @eq :: a -> b -> Bool@.
--
--   (It depends on each instance of @Eq1@. Since @Eq1@ does not have
--   any laws currently, this is not a hard guarantee. But all instances in "base", "transformers",
--   "containers", "array", and "free" satisfy it.)
--
--   Note that @emptyEq@ is not a equivalence relation, since it's possible @emptyEq x x == False@.
emptyEq :: Eq1 f => f a -> f b -> Bool
emptyEq = liftEq (\_ _ -> False)

instance Eq1 f => Eq1 (Ap f) where
  liftEq = liftEqAp

instance (Eq1 f, Eq a) => Eq (Ap f a) where
  (==) = eq1

-- | Specialized 'boringCompare' for @Ap f@.
boringCompareAp :: Ord1 f => Ap f a -> Ap f b -> Ordering
boringCompareAp (Pure _) (Pure _) = EQ
boringCompareAp (Pure _) (Ap _ _) = LT
boringCompareAp (Ap x1 y1) (Ap x2 y2) = boringCompare x1 x2 `mappend` boringCompareAp y1 y2
boringCompareAp (Ap _ _) (Pure _) = GT

-- | Implementation of 'liftCompare' for @Ap f@
liftCompareAp :: Ord1 f => (a -> b -> Ordering) -> Ap f a -> Ap f b -> Ordering
liftCompareAp cmp (Pure a1) (Pure a2) = cmp a1 a2
liftCompareAp _   (Pure _) (Ap _ _) = LT
liftCompareAp cmp (Ap x1 y1) (Ap x2 y2)
    -- This branching is necessary and not just an optimization.
    -- See the above comment for more
  | emptyEq x1 x2 = boringCompareAp y1 y2
  | otherwise     = liftCompare (\a1 a2 -> liftCompareAp (\g1 g2 -> cmp (g1 a1) (g2 a2)) y1 y2) x1 x2
liftCompareAp _   (Ap _ _) (Pure _) = GT

-- | @boringCompare fa fb@ compares @fa@ and @fb@ ignoring any difference between
--   their content (the values of their last parameters @a@ and @b@.)
--
--   It is named \'boring\' because the type parameters @a@ and @b@ are
--   treated as if they are the most boring type @()@.
boringCompare :: Ord1 f => f a -> f b -> Ordering
boringCompare = liftCompare (\_ _ -> EQ)

instance Ord1 f => Ord1 (Ap f) where
  liftCompare = liftCompareAp

instance (Ord1 f, Ord a) => Ord (Ap f a) where
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

{- $examples

<examples/ValidationForm.hs Validation form>

-}
