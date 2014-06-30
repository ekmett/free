{-# LANGUAGE RankNTypes, PolyKinds #-}
module Control.Category.Free.Catenated where

import Control.Applicative
import Control.Category
import Data.Functor.Identity
import Prelude hiding ((.),id)

class Catenated t where
  foldCat     :: Category s => (forall a b. r a b -> s a b) -> t r a b -> s a b
  traverseCat :: Applicative m => (forall a b. r a b -> m (s a b)) -> t r a b -> m (t s a b)

mapCat :: Catenated t => (forall a b. r a b -> s a b) -> t r a b -> t s a b
mapCat f = runIdentity . traverseCat (Identity . f)
