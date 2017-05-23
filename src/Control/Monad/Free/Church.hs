{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
#include "free-common.h"

-----------------------------------------------------------------------------
-- |
-- Module      :  Control.Monad.Free.Church
-- Copyright   :  (C) 2011-2015 Edward Kmett
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  provisional
-- Portability :  non-portable (rank-2 polymorphism)
--
-- \"Free Monads for Less\"
--
-- The most straightforward way of implementing free monads is as a recursive
-- datatype that allows for arbitrarily deep nesting of the base functor. This is
-- akin to a tree, with the leaves containing the values, and the nodes being a
-- level of 'Functor' over subtrees.
--
-- For each time that the `fmap` or `>>=` operations is used, the old tree is
-- traversed up to the leaves, a new set of nodes is allocated, and
-- the old ones are garbage collected. Even if the Haskell runtime
-- optimizes some of the overhead through laziness and generational garbage
-- collection, the asymptotic runtime is still quadratic.
--
-- On the other hand, if the Church encoding is used, the tree only needs to be
-- constructed once, because:
--
-- * All uses of `fmap` are collapsed into a single one, so that the values on the
--   _leaves_ are transformed in one pass.
--
--   prop> fmap f . fmap g == fmap (f . g)
--
-- * All uses of `>>=` are right associated, so that every new subtree created
--   is final.
--
--   prop> (m >>= f) >>= g == m >>= (\x -> f x >>= g)
--
-- Asymptotically, the Church encoding supports the monadic operations more
-- efficiently than the naïve 'Free'.
--
-- This is based on the \"Free Monads for Less\" series of articles by Edward Kmett:
--
-- * <http://comonad.com/reader/2011/free-monads-for-less/   Free monads for less — Part 1>
--
-- * <http://comonad.com/reader/2011/free-monads-for-less-2/ Free monads for less — Part 2>
----------------------------------------------------------------------------
module Control.Monad.Free.Church
  ( F(..)
  , improve
  , fromF
  , iter
  , iterM
  , toF
  , retract
  , hoistF
  , foldF
  , MonadFree(..)
  , liftF
  , cutoff
  ) where

import Control.Applicative
import Control.Monad as Monad
import Control.Monad.Fix
import Control.Monad.Free hiding (retract, iter, iterM, cutoff)
import Control.Monad.Reader.Class
import Control.Monad.Writer.Class
import Control.Monad.Cont.Class
import Control.Monad.Trans.Class
import Control.Monad.State.Class
import Data.Foldable
import Data.Traversable
import Data.Functor.Bind
import Data.Semigroup.Foldable
import Data.Semigroup.Traversable
import Prelude hiding (foldr)

-- | The Church-encoded free monad for a functor @f@.
--
-- It is /asymptotically/ more efficient to use ('>>=') for 'F' than it is to ('>>=') with 'Free'.
--
-- <http://comonad.com/reader/2011/free-monads-for-less-2/>
newtype F f a = F { runF :: forall r. (a -> r) -> (f r -> r) -> r }

-- | Tear down a 'Free' 'Monad' using iteration.
iter :: (f a -> a) -> F f a -> a
iter phi xs = runF xs id phi

-- | Like iter for monadic values.
iterM :: Monad m => (f (m a) -> m a) -> F f a -> m a
iterM phi xs = runF xs return phi

instance Functor (F f) where
  fmap f (F g) = F (\kp -> g (kp . f))

instance Apply (F f) where
  (<.>) = (<*>)

instance Applicative (F f) where
  pure a = F (\kp _ -> kp a)
  F f <*> F g = F (\kp kf -> f (\a -> g (kp . a) kf) kf)

-- | This violates the Alternative laws, handle with care.
instance Alternative f => Alternative (F f) where
  empty = F (\_ kf -> kf empty)
  F f <|> F g = F (\kp kf -> kf (pure (f kp kf) <|> pure (g kp kf)))

instance Bind (F f) where
  (>>-) = (>>=)

instance Monad (F f) where
  return = pure
  F m >>= f = F (\kp kf -> m (\a -> runF (f a) kp kf) kf)

instance MonadFix (F f) where
  mfix f = a where
    a = f (impure a)
    impure (F x) = x id (error "MonadFix (F f): wrap")

instance Foldable f => Foldable (F f) where
    foldMap f xs = runF xs f fold
    {-# INLINE foldMap #-}

    foldr f r xs = runF xs f (foldr (.) id) r
    {-# INLINE foldr #-}

#if MIN_VERSION_base(4,6,0)
    foldl' f z xs = runF xs (\a !r -> f r a) (flip $ foldl' $ \r g -> g r) z
    {-# INLINE foldl' #-}
#endif

instance Traversable f => Traversable (F f) where
    traverse f m = runF m (fmap return . f) (fmap wrap . sequenceA)
    {-# INLINE traverse #-}

instance Foldable1 f => Foldable1 (F f) where
    foldMap1 f m = runF m f fold1

instance Traversable1 f => Traversable1 (F f) where
    traverse1 f m = runF m (fmap return . f) (fmap wrap . sequence1)

-- | This violates the MonadPlus laws, handle with care.
instance MonadPlus f => MonadPlus (F f) where
  mzero = F (\_ kf -> kf mzero)
  F f `mplus` F g = F (\kp kf -> kf (return (f kp kf) `mplus` return (g kp kf)))

instance MonadTrans F where
  lift f = F (\kp kf -> kf (liftM kp f))

instance Functor f => MonadFree f (F f) where
  wrap f = F (\kp kf -> kf (fmap (\ (F m) -> m kp kf) f))

instance MonadState s m => MonadState s (F m) where
  get = lift get
  put = lift . put

instance MonadReader e m => MonadReader e (F m) where
  ask = lift ask
  local f = lift . local f . retract

instance MonadWriter w m => MonadWriter w (F m) where
  tell = lift . tell
  pass = lift . pass . retract
  listen = lift . listen . retract

instance MonadCont m => MonadCont (F m) where
  callCC f = lift $ callCC (retract . f . fmap lift)

-- |
-- 'retract' is the left inverse of 'lift' and 'liftF'
--
-- @
-- 'retract' . 'lift' = 'id'
-- 'retract' . 'liftF' = 'id'
-- @
retract :: Monad m => F m a -> m a
retract (F m) = m return Monad.join
{-# INLINE retract #-}

-- | Lift a natural transformation from @f@ to @g@ into a natural transformation from @F f@ to @F g@.
hoistF :: (forall x. f x -> g x) -> F f a -> F g a
hoistF t (F m) = F (\p f -> m p (f . t))

-- | The very definition of a free monad is that given a natural transformation you get a monad homomorphism.
foldF :: Monad m => (forall x. f x -> m x) -> F f a -> m a
foldF f (F m) = m return (Monad.join . f)

-- | Convert to another free monad representation.
fromF :: MonadFree f m => F f a -> m a
fromF (F m) = m return wrap
{-# INLINE fromF #-}

-- | Generate a Church-encoded free monad from a 'Free' monad.
toF :: Functor f => Free f a -> F f a
toF xs = F (\kp kf -> go kp kf xs) where
  go kp _  (Pure a) = kp a
  go kp kf (Free fma) = kf (fmap (go kp kf) fma)

-- | Improve the asymptotic performance of code that builds a free monad with only binds and returns by using 'F' behind the scenes.
--
-- This is based on the \"Free Monads for Less\" series of articles by Edward Kmett:
--
-- * <http://comonad.com/reader/2011/free-monads-for-less/   Free monads for less — Part 1>
--
-- * <http://comonad.com/reader/2011/free-monads-for-less-2/ Free monads for less — Part 2>
--
-- and <http://www.iai.uni-bonn.de/~jv/mpc08.pdf \"Asymptotic Improvement of Computations over Free Monads\"> by Janis Voightländer.
improve :: Functor f => (forall m. MonadFree f m => m a) -> Free f a
improve m = fromF m
{-# INLINE improve #-}


-- | Cuts off a tree of computations at a given depth.
-- If the depth is 0 or less, no computation nor
-- monadic effects will take place.
--
-- Some examples (@n ≥ 0@):
--
-- prop> cutoff 0     _        == return Nothing
-- prop> cutoff (n+1) . return == return . Just
-- prop> cutoff (n+1) . lift   == lift . liftM Just
-- prop> cutoff (n+1) . wrap   == wrap . fmap (cutoff n)
--
-- Calling @'retract' . 'cutoff' n@ is always terminating, provided each of the
-- steps in the iteration is terminating.
{-# INLINE cutoff #-}
cutoff :: (Functor f) => Integer -> F f a -> F f (Maybe a)
cutoff n m
    | n <= 0 = return Nothing
    | n <= toInteger (maxBound :: Int) = cutoffI (fromInteger n :: Int) m
    | otherwise = cutoffI n m

{-# SPECIALIZE cutoffI :: (Functor f) => Int -> F f a -> F f (Maybe a) #-}
{-# SPECIALIZE cutoffI :: (Functor f) => Integer -> F f a -> F f (Maybe a) #-}
cutoffI :: (Functor f, Integral n) => n -> F f a -> F f (Maybe a)
cutoffI n m = F m' where
    m' kp kf = runF m kpn kfn n where
        kpn a i
            | i <= 0 = kp Nothing
            | otherwise = kp (Just a)
        kfn fr i
            | i <= 0 = kp Nothing
            | otherwise = let
                i' = i - 1
                in i' `seq` kf (fmap ($ i') fr)
