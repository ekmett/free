{-# LANGUAGE MultiParamTypeClasses
           , FunctionalDependencies
           , FlexibleInstances
           , UndecidableInstances #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Control.Comonad.Cofree.Class
-- Copyright   :  (C) 2008-2011 Edward Kmett
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  experimental
-- Portability :  fundeps, MPTCs
----------------------------------------------------------------------------
module Control.Comonad.Cofree.Class 
  ( ComonadCofree(..)
  ) where

import Control.Applicative
import Control.Comonad
import qualified Control.Comonad.Trans.Env.Strict as Strict
import qualified Control.Comonad.Trans.Store.Strict as Strict
import qualified Control.Comonad.Trans.Discont.Strict as Strict
import qualified Control.Comonad.Trans.Env.Lazy as Lazy
import qualified Control.Comonad.Trans.Store.Lazy as Lazy
import qualified Control.Comonad.Trans.Discont.Lazy as Lazy
import qualified Control.Comonad.Trans.Traced as Simple
import qualified Control.Comonad.Trans.Traced.Memo as Memo
import qualified Control.Comonad.Trans.Store.Memo as Memo
import qualified Control.Comonad.Trans.Discont.Memo as Memo
import Control.Comonad.Trans.Identity 
import Data.Semigroup

class (Functor f, Comonad w) => ComonadCofree f w | w -> f where
  unwrap :: w a -> f (w a)

instance ComonadCofree f w => ComonadCofree f (IdentityT w) where
  unwrap = fmap IdentityT . unwrap . runIdentityT
  
instance ComonadCofree f w => ComonadCofree f (Strict.EnvT e w) where
  unwrap (Strict.EnvT e wa) = Strict.EnvT e <$> unwrap wa

instance ComonadCofree f w => ComonadCofree f (Lazy.EnvT e w) where
  unwrap (Lazy.EnvT e wa) = Lazy.EnvT e <$> unwrap wa

instance ComonadCofree f w => ComonadCofree f (Strict.StoreT s w) where
  unwrap (Strict.StoreT wsa s) = flip Strict.StoreT s <$> unwrap wsa

instance ComonadCofree f w => ComonadCofree f (Lazy.StoreT s w) where
  unwrap (Lazy.StoreT wsa s) = flip Lazy.StoreT s <$> unwrap wsa

instance ComonadCofree f w => ComonadCofree f (Memo.StoreT s w) where
  unwrap w = flip Memo.storeT s <$> unwrap wsa
    where (wsa, s) = Memo.runStoreT w

instance (ComonadCofree f w, Semigroup m, Monoid m) => ComonadCofree f (Simple.TracedT m w) where
  unwrap (Simple.TracedT wma) = Simple.TracedT <$> unwrap wma

instance (ComonadCofree f w, Semigroup m, Monoid m) => ComonadCofree f (Memo.TracedT m w) where
  unwrap = fmap Memo.tracedT . unwrap . Memo.runTracedT

instance ComonadCofree f w => ComonadCofree f (Strict.DiscontT k w) where
  unwrap (Strict.DiscontT f ws) = Strict.DiscontT f <$> unwrap ws

instance ComonadCofree f w => ComonadCofree f (Lazy.DiscontT k w) where
  unwrap (Lazy.DiscontT f ws) = Lazy.DiscontT f <$> unwrap ws

instance ComonadCofree f w => ComonadCofree f (Memo.DiscontT k w) where
  unwrap w = Memo.discontT f <$> unwrap wa
    where (f, wa) = Memo.runDiscontT w
