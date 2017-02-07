{-# LANGUAGE CPP #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE GADTs #-}
#if __GLASGOW_HASKELL__ >= 707
{-# LANGUAGE DeriveDataTypeable #-}
#endif
{-# OPTIONS_GHC -Wall #-}
#include "free-common.h"

-----------------------------------------------------------------------------
-- |
-- Module      :  Control.Applicative.Trans.Free
-- Copyright   :  (C) 2012-2013 Edward Kmett
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  provisional
-- Portability :  GADTs, Rank2Types
--
-- 'Applicative' functor transformers for free
----------------------------------------------------------------------------
module Control.Applicative.Trans.Free
  (
  -- | Compared to the free monad transformers, they are less expressive. However, they are also more
  -- flexible to inspect and interpret, as the number of ways in which
  -- the values can be nested is more limited.
  --
  -- See <http://paolocapriotti.com/assets/applicative.pdf Free Applicative Functors>,
  -- by Paolo Capriotti and Ambrus Kaposi, for some applications.
    ApT(..)
  , ApF(..)
  , liftApT
  , liftApO
  , runApT
  , runApF
  , runApT_
  , hoistApT
  , hoistApF
  , transApT
  , transApF
  , joinApT
  -- * Free Applicative
  , Ap
  , runAp
  , runAp_
  , retractAp
  -- * Free Alternative
  , Alt
  , runAlt
  ) where

import Control.Applicative
import Control.Monad (liftM)
import Data.Functor.Apply
import Data.Functor.Identity
import Data.Typeable
#if !(MIN_VERSION_base(4,8,0))
import Data.Monoid (Monoid)
#endif
import qualified Data.Foldable as F

-- | The free 'Applicative' for a 'Functor' @f@.
data ApF f g a where
  Pure :: a -> ApF f g a
  Ap   :: f a -> ApT f g (a -> b) -> ApF f g b
#if __GLASGOW_HASKELL__ >= 707
  deriving Typeable
#endif

-- | The free 'Applicative' transformer for a 'Functor' @f@ over
-- 'Applicative' @g@.
newtype ApT f g a = ApT { getApT :: g (ApF f g a) }
#if __GLASGOW_HASKELL__ >= 707
  deriving Typeable
#endif

instance Functor g => Functor (ApF f g) where
  fmap f (Pure a) = Pure (f a)
  fmap f (Ap x g) = x `Ap` fmap (f .) g

instance Functor g => Functor (ApT f g) where
  fmap f (ApT g) = ApT (fmap f <$> g)

instance Applicative g => Applicative (ApF f g) where
  pure = Pure
  {-# INLINE pure #-}
  Pure f   <*> y       = fmap f y      -- fmap
  y        <*> Pure a  = fmap ($ a) y  -- interchange
  Ap a f   <*> b       = a `Ap` (flip <$> f <*> ApT (pure b))
  {-# INLINE (<*>) #-}

instance Applicative g => Applicative (ApT f g) where
  pure = ApT . pure . pure
  {-# INLINE pure #-}
  ApT xs <*> ApT ys = ApT ((<*>) <$> xs <*> ys)
  {-# INLINE (<*>) #-}

instance Applicative g => Apply (ApF f g) where
  (<.>) = (<*>)
  {-# INLINE (<.>) #-}

instance Applicative g => Apply (ApT f g) where
  (<.>) = (<*>)
  {-# INLINE (<.>) #-}

instance Alternative g => Alternative (ApT f g) where
  empty = ApT empty
  {-# INLINE empty #-}
  ApT g <|> ApT h = ApT (g <|> h)
  {-# INLINE (<|>) #-}

-- | A version of 'lift' that can be used with no constraint for @f@.
liftApT :: Applicative g => f a -> ApT f g a
liftApT x = ApT (pure (Ap x (pure id)))

-- | Lift an action of the \"outer\" 'Functor' @g a@ to @'ApT' f g a@.
liftApO :: Functor g => g a -> ApT f g a
liftApO g = ApT (Pure <$> g)

-- | Given natural transformations @f ~> h@ and @g . h ~> h@ this gives
-- a natural transformation @ApF f g ~> h@.
runApF :: (Applicative h, Functor g) => (forall a. f a -> h a) -> (forall a. g (h a) -> h a) -> ApF f g b -> h b
runApF _ _ (Pure x) = pure x
runApF f g (Ap x y) = f x <**> runApT f g y

-- | Given natural transformations @f ~> h@ and @g . h ~> h@ this gives
-- a natural transformation @ApT f g ~> h@.
runApT :: (Applicative h, Functor g) => (forall a. f a -> h a) -> (forall a. g (h a) -> h a) -> ApT f g b -> h b
runApT f g (ApT a) = g (runApF f g <$> a)

-- | Perform a monoidal analysis over @'ApT' f g b@ value.
--
-- Examples:
--
-- @
-- height :: ('Functor' g, 'F.Foldable' g) => 'ApT' f g a -> 'Int'
-- height = 'getSum' . runApT_ (\_ -> 'Sum' 1) 'F.maximum'
-- @
--
-- @
-- size :: ('Functor' g, 'F.Foldable' g) => 'ApT' f g a -> 'Int'
-- size = 'getSum' . runApT_ (\_ -> 'Sum' 1) 'F.fold'
-- @
runApT_ :: (Functor g, Monoid m) => (forall a. f a -> m) -> (g m -> m) -> ApT f g b -> m
runApT_ f g = getConst . runApT (Const . f) (Const . g . fmap getConst)

-- | Given a natural transformation from @f@ to @f'@ this gives a monoidal natural transformation from @ApF f g@ to @ApF f' g@.
hoistApF :: Functor g => (forall a. f a -> f' a) -> ApF f g b -> ApF f' g b
hoistApF _ (Pure x) = Pure x
hoistApF f (Ap x y) = f x `Ap` hoistApT f y

-- | Given a natural transformation from @f@ to @f'@ this gives a monoidal natural transformation from @ApT f g@ to @ApT f' g@.
hoistApT :: Functor g => (forall a. f a -> f' a) -> ApT f g b -> ApT f' g b
hoistApT f (ApT g) = ApT (hoistApF f <$> g)

-- | Given a natural transformation from @g@ to @g'@ this gives a monoidal natural transformation from @ApF f g@ to @ApF f g'@.
transApF :: Functor g => (forall a. g a -> g' a) -> ApF f g b -> ApF f g' b
transApF _ (Pure x) = Pure x
transApF f (Ap x y) = x `Ap` transApT f y

-- | Given a natural transformation from @g@ to @g'@ this gives a monoidal natural transformation from @ApT f g@ to @ApT f g'@.
transApT :: Functor g => (forall a. g a -> g' a) -> ApT f g b -> ApT f g' b
transApT f (ApT g) = ApT $ f (transApF f <$> g)

-- | Pull out and join @m@ layers of @'ApT' f m a@.
joinApT :: Monad m => ApT f m a -> m (Ap f a)
joinApT (ApT m) = m >>= joinApF
  where
    joinApF (Pure x) = return (pure x)
    joinApF (Ap x y) = (liftApT x <**>) `liftM` joinApT y

-- | The free 'Applicative' for a 'Functor' @f@.
type Ap f = ApT f Identity

-- | Given a natural transformation from @f@ to @g@, this gives a canonical monoidal natural transformation from @'Ap' f@ to @g@.
--
-- prop> runAp t == retractApp . hoistApp t
runAp :: Applicative g => (forall x. f x -> g x) -> Ap f a -> g a
runAp f = runApT f runIdentity

-- | Perform a monoidal analysis over free applicative value.
--
-- Example:
--
-- @
-- count :: 'Ap' f a -> 'Int'
-- count = 'getSum' . runAp_ (\\_ -> 'Sum' 1)
-- @
runAp_ :: Monoid m => (forall x. f x -> m) -> Ap f a -> m
runAp_ f = runApT_ f runIdentity

-- | Interprets the free applicative functor over f using the semantics for
--   `pure` and `<*>` given by the Applicative instance for f.
--
--   prop> retractApp == runAp id
retractAp :: Applicative f => Ap f a -> f a
retractAp = runAp id

-- | The free 'Alternative' for a 'Functor' @f@.
type Alt f = ApT f []

-- | Given a natural transformation from @f@ to @g@, this gives a canonical monoidal natural transformation from @'Alt' f@ to @g@.
runAlt :: (Alternative g, F.Foldable t) => (forall x. f x -> g x) -> ApT f t a -> g a
runAlt f (ApT xs) = F.foldr (\x acc -> h x <|> acc) empty xs
  where
    h (Pure x) = pure x
    h (Ap x g) = f x <**> runAlt f g

#if __GLASGOW_HASKELL__ < 707
instance (Typeable1 f, Typeable1 g) => Typeable1 (ApT f g) where
  typeOf1 t = mkTyConApp apTTyCon [typeOf1 (f t)] where
    f :: ApT f g a -> g (f a)
    f = undefined

instance (Typeable1 f, Typeable1 g) => Typeable1 (ApF f g) where
  typeOf1 t = mkTyConApp apFTyCon [typeOf1 (f t)] where
    f :: ApF f g a -> g (f a)
    f = undefined

apTTyCon, apFTyCon :: TyCon
#if __GLASGOW_HASKELL__ < 704
apTTyCon = mkTyCon "Control.Applicative.Trans.Free.ApT"
apFTyCon = mkTyCon "Control.Applicative.Trans.Free.ApF"
#else
apTTyCon = mkTyCon3 "free" "Control.Applicative.Trans.Free" "ApT"
apFTyCon = mkTyCon3 "free" "Control.Applicative.Trans.Free" "ApF"
#endif
{-# NOINLINE apTTyCon #-}
{-# NOINLINE apFTyCon #-}
#endif
