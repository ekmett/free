{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, FlexibleInstances, UndecidableInstances #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Control.Monad.Free.Class
-- Copyright   :  (C) 2008-2011 Edward Kmett
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  experimental
-- Portability :  non-portable (fundeps, MPTCs)
----------------------------------------------------------------------------
module Control.Monad.Free.Class 
  ( MonadFree(..)
  ) where

import Control.Applicative
import Control.Monad.Trans.Free (Free(..))
import Control.Monad.Trans.Reader
import qualified Control.Monad.Trans.State.Strict as Strict
import qualified Control.Monad.Trans.State.Lazy as Lazy
import qualified Control.Monad.Trans.Writer.Strict as Strict
import qualified Control.Monad.Trans.Writer.Lazy as Lazy
import qualified Control.Monad.Trans.RWS.Strict as Strict
import qualified Control.Monad.Trans.RWS.Lazy as Lazy
import Control.Monad.Trans.Maybe
import Control.Monad.Trans.List
import Control.Monad.Trans.Error
import Control.Monad.Trans.Identity 
import Data.Monoid

class (Functor f, Monad m) => MonadFree f m | m -> f where
  wrap :: f (m a) -> m a

instance Functor f => MonadFree f (Free f) where
  wrap = Free

instance MonadFree f m => MonadFree f (ReaderT e m) where
  wrap fm = ReaderT $ \e -> wrap $ flip runReaderT e <$> fm

instance MonadFree f m => MonadFree f (Lazy.StateT s m) where
  wrap fm = Lazy.StateT $ \s -> wrap $ flip Lazy.runStateT s <$> fm

instance MonadFree f m => MonadFree f (Strict.StateT s m) where
  wrap fm = Strict.StateT $ \s -> wrap $ flip Strict.runStateT s <$> fm

instance (MonadFree f m, Monoid w) => MonadFree f (Lazy.WriterT w m) where
  wrap = Lazy.WriterT . wrap . fmap Lazy.runWriterT

instance (MonadFree f m, Monoid w) => MonadFree f (Strict.WriterT w m) where
  wrap = Strict.WriterT . wrap . fmap Strict.runWriterT

instance (MonadFree f m, Monoid w) => MonadFree f (Strict.RWST r w s m) where
  wrap fm = Strict.RWST $ \r s -> wrap $ fmap (\m -> Strict.runRWST m r s) fm

instance (MonadFree f m, Monoid w) => MonadFree f (Lazy.RWST r w s m) where
  wrap fm = Lazy.RWST $ \r s -> wrap $ fmap (\m -> Lazy.runRWST m r s) fm

instance MonadFree f m => MonadFree f (MaybeT m) where
  wrap = MaybeT . wrap . fmap runMaybeT

instance MonadFree f m => MonadFree f (IdentityT m) where
  wrap = IdentityT . wrap . fmap runIdentityT 

instance MonadFree f m => MonadFree f (ListT m) where
  wrap = ListT . wrap . fmap runListT

instance (MonadFree f m, Error e) => MonadFree f (ErrorT e m) where
  wrap = ErrorT . wrap . fmap runErrorT
  
