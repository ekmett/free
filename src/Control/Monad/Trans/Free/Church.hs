{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE UndecidableInstances #-}
module Control.Monad.Trans.Free.Church where

import Control.Applicative
import Control.Monad
import Control.Monad.Identity
import Control.Monad.Trans.Class
import Control.Monad.IO.Class
import Control.Monad.Trans.Free
import Data.Foldable (Foldable)
import qualified Data.Foldable as F
import Data.Monoid
import Data.Functor.Bind hiding (join)

newtype FT f m a = FT {runFT :: forall r. (a -> m r) -> (f (m r) -> m r) -> m r}

instance Functor (FT f m) where
  fmap f (FT k) = FT $ \a fr -> k (a . f) fr

instance Apply (FT f m) where
  (<.>) = (<*>)

instance Applicative (FT f m) where
  pure a = FT $ \k _ -> k a
  FT fk <*> FT ak = FT $ \b fr -> ak (\d -> fk (\e -> b (e d)) fr) fr

instance Bind (FT f m) where
  (>>-) = (>>=)

instance Monad (FT f m) where
  return = pure
  FT fk >>= f = FT $ \b fr -> fk (\d -> runFT (f d) b fr) fr

instance (Functor f) => MonadFree f (FT f m) where
  wrap f = FT (\kp kf -> kf (fmap (\(FT m) -> m kp kf) f))

instance MonadTrans (FT f) where
  lift m = FT (\a _ -> m >>= a)

instance Alternative m => Alternative (FT f m) where
  empty = FT (\_ _ -> empty)
  FT k1 <|> FT k2 = FT $ \a fr -> k1 a fr <|> k2 a fr

instance MonadPlus m => MonadPlus (FT f m) where
  mzero = FT (\_ _ -> mzero)
  mplus (FT k1) (FT k2) = FT $ \a fr -> k1 a fr `mplus` k2 a fr

instance (Foldable f, Foldable m, Monad m) => Foldable (FT f m) where
  foldMap f (FT k) = F.fold $ k (return . f) (F.foldr (liftM2 mappend) (return mempty))

instance (MonadIO m) => MonadIO (FT f m) where
  liftIO = lift . liftIO
  {-# INLINE liftIO #-}

foo :: (Monad m, Functor f) => FreeT f m a -> FT f m a
foo (FreeT f) = FT $ \ka kfr -> do
  freef <- f
  case freef of
    Pure a -> ka a
    Free fb -> kfr $ fmap (($ kfr) . ($ ka) . runFT . foo) fb

bar :: (Monad m, Functor f) => FT f m a -> FreeT f m a
bar (FT k) = FreeT $ k (return . Pure) (runFreeT . wrap . fmap FreeT)

type F f = FT f Identity

runF :: Functor f => F f a -> (forall r. (a -> r) -> (f r -> r) -> r)
runF (FT m) = \kp kf -> runIdentity $ m (return . kp) (return . kf . fmap runIdentity)

free :: Functor f => (forall r. (a -> r) -> (f r -> r) -> r) -> F f a
free f = FT (\kp kf -> return $ f (runIdentity . kp) (runIdentity . kf . fmap return))








