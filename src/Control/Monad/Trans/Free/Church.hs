{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE UndecidableInstances #-}
#include "free-common.h"

-----------------------------------------------------------------------------
-- |
-- Module      :  Control.Monad.Trans.Free.Church
-- Copyright   :  (C) 2008-2014 Edward Kmett
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  provisional
-- Portability :  non-portable (rank-2 polymorphism, MTPCs)
--
-- Church-encoded free monad transformer.
--
-----------------------------------------------------------------------------
module Control.Monad.Trans.Free.Church
  (
  -- * The free monad transformer
    FT(..)
  -- * The free monad
  , F, free, runF
  -- * Operations
  , improveT
  , toFT, fromFT
  , iterT
  , iterTM
  , hoistFT
  , transFT
  , joinFT
  , cutoff
  -- * Operations of free monad
  , improve
  , fromF, toF
  , retract
  , retractT
  , iter
  , iterM
  -- * Free Monads With Class
  , MonadFree(..)
  , liftF
  ) where

import Control.Applicative
import Control.Category ((<<<), (>>>))
import Control.Monad
import Control.Monad.Catch (MonadCatch(..), MonadThrow(..))
import Control.Monad.Identity
import Control.Monad.Trans.Class
import Control.Monad.IO.Class
import Control.Monad.Reader.Class
import Control.Monad.Writer.Class
import Control.Monad.State.Class
import Control.Monad.Error.Class
import Control.Monad.Cont.Class
import Control.Monad.Free.Class
import Control.Monad.Trans.Free (FreeT(..), FreeF(..), Free)
import qualified Control.Monad.Trans.Free as FreeT
import qualified Data.Foldable as F
import qualified Data.Traversable as T
import Data.Functor.Bind hiding (join)
import Data.Functor.Classes.Compat

#if !(MIN_VERSION_base(4,8,0))
import Data.Foldable (Foldable)
import Data.Traversable (Traversable)
#endif

-- | The \"free monad transformer\" for a functor @f@
newtype FT f m a = FT { runFT :: forall r. (a -> m r) -> (forall x. (x -> m r) -> f x -> m r) -> m r }

#ifdef LIFTED_FUNCTOR_CLASSES
instance (Functor f, Monad m, Eq1 f, Eq1 m) => Eq1 (FT f m) where
  liftEq eq x y = liftEq eq (fromFT x) (fromFT y)

instance (Functor f, Monad m, Ord1 f, Ord1 m) => Ord1 (FT f m) where
  liftCompare cmp x y= liftCompare cmp (fromFT x) (fromFT y)
#else
instance ( Functor f, Monad m, Eq1 f, Eq1 m
# if !(MIN_VERSION_base(4,8,0))
         , Functor m
# endif
         ) => Eq1 (FT f m) where
  eq1 x y = eq1 (fromFT x) (fromFT y)

instance ( Functor f, Monad m, Ord1 f, Ord1 m
# if !(MIN_VERSION_base(4,8,0))
         , Functor m
# endif
         ) => Ord1 (FT f m) where
  compare1 x y = compare1 (fromFT x) (fromFT y)
#endif

instance (Eq1 (FT f m), Eq a) => Eq (FT f m a) where
  (==) = eq1

instance (Ord1 (FT f m), Ord a) => Ord (FT f m a) where
  compare = compare1

instance Functor (FT f m) where
  fmap f (FT k) = FT $ \a fr -> k (a . f) fr

instance Apply (FT f m) where
  (<.>) = (<*>)

instance Applicative (FT f m) where
  pure a = FT $ \k _ -> k a
  FT fk <*> FT ak = FT $ \b fr -> fk (\e -> ak (\d -> b (e d)) fr) fr

instance Bind (FT f m) where
  (>>-) = (>>=)

instance Monad (FT f m) where
  return = pure
  FT fk >>= f = FT $ \b fr -> fk (\d -> runFT (f d) b fr) fr

instance MonadFree f (FT f m) where
  wrap f = FT (\kp kf -> kf (\ft -> runFT ft kp kf) f)

instance MonadTrans (FT f) where
  lift m = FT (\a _ -> m >>= a)

instance Alternative m => Alternative (FT f m) where
  empty = FT (\_ _ -> empty)
  FT k1 <|> FT k2 = FT $ \a fr -> k1 a fr <|> k2 a fr

instance MonadPlus m => MonadPlus (FT f m) where
  mzero = FT (\_ _ -> mzero)
  mplus (FT k1) (FT k2) = FT $ \a fr -> k1 a fr `mplus` k2 a fr

instance (Foldable f, Foldable m, Monad m) => Foldable (FT f m) where
  foldr f r xs = F.foldr (<<<) id inner r
    where
      inner = runFT xs (return . f) (\xg xf -> F.foldr (liftM2 (<<<) . xg) (return id) xf)
  {-# INLINE foldr #-}

#if MIN_VERSION_base(4,6,0)
  foldl' f z xs = F.foldl' (!>>>) id inner z
    where
      (!>>>) h g = \r -> g $! h r
      inner = runFT xs (return . flip f) (\xg xf -> F.foldr (liftM2 (>>>) . xg) (return id) xf)
  {-# INLINE foldl' #-}
#endif

instance (Monad m, Traversable m, Traversable f) => Traversable (FT f m) where
  traverse f (FT k) = fmap (join . lift) . T.sequenceA $ k traversePure traverseFree
    where
      traversePure = return . fmap return . f
      traverseFree xg = return . fmap (wrap . fmap (join . lift)) . T.traverse (T.sequenceA . xg)

instance (MonadIO m) => MonadIO (FT f m) where
  liftIO = lift . liftIO
  {-# INLINE liftIO #-}

instance (Functor f, MonadError e m) => MonadError e (FT f m) where
  throwError = lift . throwError
  {-# INLINE throwError #-}
  m `catchError` f = toFT $ fromFT m `catchError` (fromFT . f)

instance MonadCont m => MonadCont (FT f m) where
  callCC f = join . lift $ callCC (\k -> return $ f (lift . k . return))

instance MonadReader r m => MonadReader r (FT f m) where
  ask = lift ask
  {-# INLINE ask #-}
  local f = hoistFT (local f)
  {-# INLINE local #-}

instance (Functor f, MonadWriter w m) => MonadWriter w (FT f m) where
  tell = lift . tell
  {-# INLINE tell #-}
  listen = toFT . listen . fromFT
  pass = toFT . pass . fromFT
#if MIN_VERSION_mtl(2,1,1)
  writer w = lift (writer w)
  {-# INLINE writer #-}
#endif

instance MonadState s m => MonadState s (FT f m) where
  get = lift get
  {-# INLINE get #-}
  put = lift . put
  {-# INLINE put #-}
#if MIN_VERSION_mtl(2,1,1)
  state f = lift (state f)
  {-# INLINE state #-}
#endif

instance MonadThrow m => MonadThrow (FT f m) where
  throwM = lift . throwM
  {-# INLINE throwM #-}

instance (Functor f, MonadCatch m) => MonadCatch (FT f m) where
  catch m f = toFT $ fromFT m `Control.Monad.Catch.catch` (fromFT . f)
  {-# INLINE catch #-}

-- | Generate a Church-encoded free monad transformer from a 'FreeT' monad
-- transformer.
toFT :: Monad m => FreeT f m a -> FT f m a
toFT (FreeT f) = FT $ \ka kfr -> do
  freef <- f
  case freef of
    Pure a -> ka a
    Free fb -> kfr (\x -> runFT (toFT x) ka kfr) fb

-- | Convert to a 'FreeT' free monad representation.
fromFT :: (Monad m, Functor f) => FT f m a -> FreeT f m a
fromFT (FT k) = FreeT $ k (return . Pure) (\xg -> runFreeT . wrap . fmap (FreeT . xg))

-- | The \"free monad\" for a functor @f@.
type F f = FT f Identity

-- | Unwrap the 'Free' monad to obtain it's Church-encoded representation.
runF :: Functor f => F f a -> (forall r. (a -> r) -> (f r -> r) -> r)
runF (FT m) = \kp kf -> runIdentity $ m (return . kp) (\xg -> return . kf . fmap (runIdentity . xg))

-- | Wrap a Church-encoding of a \"free monad\" as the free monad for a functor.
free :: (forall r. (a -> r) -> (f r -> r) -> r) -> F f a
free f = FT (\kp kf -> return $ f (runIdentity . kp) (runIdentity . kf return))

-- | Tear down a free monad transformer using iteration.
iterT :: (Functor f, Monad m) => (f (m a) -> m a) -> FT f m a -> m a
iterT phi (FT m) = m return (\xg -> phi . fmap xg)
{-# INLINE iterT #-}

-- | Tear down a free monad transformer using iteration over a transformer.
iterTM :: (Functor f, Monad m, MonadTrans t, Monad (t m)) => (f (t m a) -> t m a) -> FT f m a -> t m a
iterTM f (FT m) = join . lift $ m (return . return) (\xg -> return . f . fmap (join . lift . xg))

-- | Lift a monad homomorphism from @m@ to @n@ into a monad homomorphism from @'FT' f m@ to @'FT' f n@
--
-- @'hoistFT' :: ('Monad' m, 'Monad' n, 'Functor' f) => (m ~> n) -> 'FT' f m ~> 'FT' f n@
hoistFT :: (Monad m, Monad n) => (forall a. m a -> n a) -> FT f m b -> FT f n b
hoistFT phi (FT m) = FT (\kp kf -> join . phi $ m (return . kp) (\xg -> return . kf (join . phi . xg)))

-- | Lift a natural transformation from @f@ to @g@ into a monad homomorphism from @'FT' f m@ to @'FT' g n@
transFT :: (forall a. f a -> g a) -> FT f m b -> FT g m b
transFT phi (FT m) = FT (\kp kf -> m kp (\xg -> kf xg . phi))

-- | Pull out and join @m@ layers of @'FreeT' f m a@.
joinFT :: (Monad m, Traversable f) => FT f m a -> m (F f a)
joinFT (FT m) = m (return . return) (\xg -> liftM wrap . T.mapM xg)

-- | Cuts off a tree of computations at a given depth.
-- If the depth is 0 or less, no computation nor
-- monadic effects will take place.
--
-- Some examples (n ≥ 0):
--
-- prop> cutoff 0     _        == return Nothing
-- prop> cutoff (n+1) . return == return . Just
-- prop> cutoff (n+1) . lift   ==   lift . liftM Just
-- prop> cutoff (n+1) . wrap   ==  wrap . fmap (cutoff n)
--
-- Calling 'retract . cutoff n' is always terminating, provided each of the
-- steps in the iteration is terminating.
cutoff :: (Functor f, Monad m) => Integer -> FT f m a -> FT f m (Maybe a)
cutoff n = toFT . FreeT.cutoff n . fromFT

-- |
-- 'retract' is the left inverse of 'liftF'
--
-- @
-- 'retract' . 'liftF' = 'id'
-- @
#if __GLASGOW_HASKELL__ < 710
retract :: (Functor f, Monad f) => F f a -> f a
#else
retract :: Monad f => F f a -> f a
#endif
retract m = runF m return join
{-# INLINE retract #-}

-- | Tear down a free monad transformer using iteration over a transformer.
retractT :: (MonadTrans t, Monad (t m), Monad m) => FT (t m) m a -> t m a
retractT (FT m) = join . lift $ m (return . return) (\xg xf -> return $ xf >>= join . lift . xg)

-- | Tear down an 'F' 'Monad' using iteration.
iter :: Functor f => (f a -> a) -> F f a -> a
iter phi = runIdentity . iterT (Identity . phi . fmap runIdentity)
{-# INLINE iter #-}

-- | Like 'iter' for monadic values.
iterM :: (Functor f, Monad m) => (f (m a) -> m a) -> F f a -> m a
iterM phi = iterT phi . hoistFT (return . runIdentity)

-- | Convert to another free monad representation.
fromF :: (Functor f, MonadFree f m) => F f a -> m a
fromF m = runF m return wrap
{-# INLINE fromF #-}

-- | Generate a Church-encoded free monad from a 'Free' monad.
toF :: Free f a -> F f a
toF = toFT
{-# INLINE toF #-}

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

-- | Improve the asymptotic performance of code that builds a free monad transformer
-- with only binds and returns by using 'FT' behind the scenes.
--
-- Similar to 'improve'.
improveT :: (Functor f, Monad m) => (forall t. MonadFree f (t m) => t m a) -> FreeT f m a
improveT m = fromFT m
{-# INLINE improveT #-}

