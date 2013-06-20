{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Control.Monad.Free.Church
-- Copyright   :  (C) 2011-2012 Edward Kmett
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  provisional
-- Portability :  non-portable (rank-2 polymorphism)
--
-- \"Free Monads for Less\"
--
-- This is based on the \"Free Monads for Less\" series of articles:
--
-- <http://comonad.com/reader/2011/free-monads-for-less/>
-- <http://comonad.com/reader/2011/free-monads-for-less-2/>
----------------------------------------------------------------------------
module Control.Monad.Free.Church
  ( F(..)
  , improve
  , fromF
  , toF
  , retract
  , MonadFree(..)
  , liftF
  ) where

import Control.Applicative
import Control.Monad as Monad
import Control.Monad.Free hiding (retract)
import Control.Monad.Reader.Class
import Control.Monad.Writer.Class
import Control.Monad.Cont.Class
import Control.Monad.Trans.Class
import Control.Monad.State.Class
import Data.Functor.Bind

-- | The Church-encoded free monad for a functor @f@.
--
-- It is /asymptotically/ more efficient to use ('>>=') for 'F' than it is to ('>>=') with 'Free'.
--
-- <http://comonad.com/reader/2011/free-monads-for-less-2/>
newtype F f a = F { runF :: forall r. (a -> r) -> (f r -> r) -> r }

instance Functor (F f) where
  fmap f (F g) = F (\kp -> g (kp . f))

instance Apply (F f) where
  (<.>) = (<*>)

instance Applicative (F f) where
  pure a = F (\kp _ -> kp a)
  F f <*> F g = F (\kp kf -> f (\a -> g (\b -> kp (a b)) kf) kf)

instance Alternative f => Alternative (F f) where
  empty = F (\_ kf -> kf empty)
  F f <|> F g = F (\kp kf -> kf (pure (f kp kf) <|> pure (g kp kf)))

instance Bind (F f) where
  (>>-) = (>>=)

instance Monad (F f) where
  return a = F (\kp _ -> kp a)
  F m >>= f = F (\kp kf -> m (\a -> runF (f a) kp kf) kf)

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
-- <http://comonad.com/reader/2011/free-monads-for-less/>
-- <http://comonad.com/reader/2011/free-monads-for-less-2/>
--
-- and \"Asymptotic Improvement of Computations over Free Monads\" by Janis Voightländer:
--
-- <http://www.iai.uni-bonn.de/~jv/mpc08.pdf>
improve :: Functor f => (forall m. MonadFree f m => m a) -> Free f a
improve m = fromF m
{-# INLINE improve #-}
