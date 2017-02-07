{-# LANGUAGE CPP #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
#include "free-common.h"
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
import Data.List.NonEmpty
import Data.Tree
#if __GLASGOW_HASKELL__ < 710
import Data.Monoid
#endif

-- | Allows you to peel a layer off a cofree comonad.
class (Functor f, Comonad w) => ComonadCofree f w | w -> f where
  -- | Remove a layer.
  unwrap :: w a -> f (w a)

instance ComonadCofree Maybe NonEmpty where
  unwrap (_ :| [])       = Nothing
  unwrap (_ :| (a : as)) = Just (a :| as)

instance ComonadCofree [] Tree where
  unwrap = subForest

instance ComonadCofree (Const b) ((,) b) where
  unwrap = Const . fst

instance ComonadCofree f w => ComonadCofree f (IdentityT w) where
  unwrap = fmap IdentityT . unwrap . runIdentityT

instance ComonadCofree f w => ComonadCofree f (EnvT e w) where
  unwrap (EnvT e wa) = EnvT e <$> unwrap wa

instance ComonadCofree f w => ComonadCofree f (StoreT s w) where
  unwrap (StoreT wsa s) = flip StoreT s <$> unwrap wsa

instance (ComonadCofree f w, Monoid m) => ComonadCofree f (TracedT m w) where
  unwrap (TracedT wma) = TracedT <$> unwrap wma
