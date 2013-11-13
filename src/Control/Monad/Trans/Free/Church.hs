{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE UndecidableInstances #-}
module Control.Monad.Trans.Free.Church where

import Control.Applicative
import Control.Monad
import Control.Monad.Trans.Class
import Control.Monad.Trans.Free
import Data.Foldable (Foldable)
import qualified Data.Foldable as F
import Data.Monoid

newtype FT f m a = FT {runFT :: forall r. (a -> m r) -> (f (m r) -> m r) -> m r}

instance Functor (FT f m) where
  fmap f (FT k) = FT $ \a fr -> k (a . f) fr

instance Applicative (FT f m) where
  pure a = FT $ \k _ -> k a
  FT fk <*> FT ak = FT $ \b fr -> ak (\d -> fk (\e -> b (e d)) fr) fr

instance Monad (FT f m) where
  return = pure
  FT fk >>= f = FT $ \b fr -> fk (\d -> runFT (f d) b fr) fr

instance (Monad m, Functor f) => MonadFree f (FT f m) where
  wrap f = FT (\kp kf -> kf (fmap (\(FT m) -> m kp kf) f))

instance MonadTrans (FT f) where
  lift m = FT (\a _ -> m >>= a)

instance MonadPlus m => MonadPlus (FT f m) where
  mzero = FT (\_ _ -> mzero)
  mplus (FT k1) (FT k2) = FT $ \a fr -> k1 a fr `mplus` k2 a fr

instance (Foldable f, Foldable m, Monad m) => Foldable (FT f m) where
  foldMap f (FT k) = F.fold $ k (return . f) (F.foldr (liftM2 mappend) (return mempty))

foo :: (Monad m, Functor f) => FreeT f m a -> FT f m a
foo (FreeT f) = FT $ \ka kfr -> do
  freef <- f
  case freef of
    Pure a -> ka a
    Free fb -> kfr $ fmap (($ kfr) . ($ ka) . runFT . foo) fb

bar :: (Monad m, Functor f) => FT f m a -> FreeT f m a
bar (FT k) = FreeT $ k (return . Pure) (runFreeT . wrap . fmap FreeT)










