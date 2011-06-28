-----------------------------------------------------------------------------
-- |
-- Module      :  Control.Comonad.Cofree
-- Copyright   :  (C) 2008-2011 Edward Kmett
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  experimental
-- Portability :  non-portable (fundeps, MPTCs)
----------------------------------------------------------------------------
module Control.Comonad.Cofree 
  ( ComonadCofree(..)
  , Cofree(..)
  , coiter
  , unfold
  , section
  ) where

import Control.Comonad.Cofree.Class
import Control.Comonad.Trans.Cofree
