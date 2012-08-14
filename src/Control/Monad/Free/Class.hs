{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
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

-- |
-- Note: The 'kan-extensions' package provides an 'MonadFree' that can
-- improve the asymptotic performance of code written using 'Control.Monad.Free.Free'
-- monads.
class Monad m => MonadFree f m | m -> f where
  -- | Add a layer.
  wrap :: f (m a) -> m a

instance (Functor f, MonadFree f m) => MonadFree f (ReaderT e m) where
  wrap fm = ReaderT $ \e -> wrap $ flip runReaderT e <$> fm

instance (Functor f, MonadFree f m) => MonadFree f (Lazy.StateT s m) where
  wrap fm = Lazy.StateT $ \s -> wrap $ flip Lazy.runStateT s <$> fm

instance (Functor f, MonadFree f m) => MonadFree f (Strict.StateT s m) where
  wrap fm = Strict.StateT $ \s -> wrap $ flip Strict.runStateT s <$> fm

instance (Functor f, MonadFree f m, Monoid w) => MonadFree f (Lazy.WriterT w m) where
  wrap = Lazy.WriterT . wrap . fmap Lazy.runWriterT

instance (Functor f, MonadFree f m, Monoid w) => MonadFree f (Strict.WriterT w m) where
  wrap = Strict.WriterT . wrap . fmap Strict.runWriterT

instance (Functor f, MonadFree f m, Monoid w) => MonadFree f (Strict.RWST r w s m) where
  wrap fm = Strict.RWST $ \r s -> wrap $ fmap (\m -> Strict.runRWST m r s) fm

instance (Functor f, MonadFree f m, Monoid w) => MonadFree f (Lazy.RWST r w s m) where
  wrap fm = Lazy.RWST $ \r s -> wrap $ fmap (\m -> Lazy.runRWST m r s) fm

instance (Functor f, MonadFree f m) => MonadFree f (MaybeT m) where
  wrap = MaybeT . wrap . fmap runMaybeT

instance (Functor f, MonadFree f m) => MonadFree f (IdentityT m) where
  wrap = IdentityT . wrap . fmap runIdentityT

instance (Functor f, MonadFree f m) => MonadFree f (ListT m) where
  wrap = ListT . wrap . fmap runListT

instance (Functor f, MonadFree f m, Error e) => MonadFree f (ErrorT e m) where
  wrap = ErrorT . wrap . fmap runErrorT
