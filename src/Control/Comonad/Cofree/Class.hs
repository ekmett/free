{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
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
import Control.Comonad.Trans.Env
import Control.Comonad.Trans.Store
import Control.Comonad.Trans.Traced
import Control.Comonad.Trans.Identity
import Data.Semigroup

class (Functor f, Comonad w) => ComonadCofree f w | w -> f where
  unwrap :: w a -> f (w a)

instance ComonadCofree f w => ComonadCofree f (IdentityT w) where
  unwrap = fmap IdentityT . unwrap . runIdentityT

instance ComonadCofree f w => ComonadCofree f (EnvT e w) where
  unwrap (EnvT e wa) = EnvT e <$> unwrap wa

instance ComonadCofree f w => ComonadCofree f (StoreT s w) where
  unwrap (StoreT wsa s) = flip StoreT s <$> unwrap wsa

instance (ComonadCofree f w, Semigroup m, Monoid m) => ComonadCofree f (TracedT m w) where
  unwrap (TracedT wma) = TracedT <$> unwrap wma
