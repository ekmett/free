{-# LANGUAGE PolyKinds, RankNTypes, GADTs #-}
module Ok where

import Control.Category
import Control.Applicative
import Prelude hiding ((.), id)

class Cat t where
  foldCat     :: Category s => (forall a b. r a b -> s a b) -> t r a b -> s a b
  traverseCat :: Applicative m => (forall a b. r a b -> m (s a b)) -> t r a b -> m (t s a b)

data Digit :: (i -> i -> *) -> i -> i -> * where
  D0 :: Digit r a a
  D1 :: r a b -> Digit r a b
  D2 :: r b c -> r a b -> Digit r a c
  D3 :: r c d -> r b c -> r a b -> Digit r a d

instance Cat Digit where
  foldCat _ D0             = id
  foldCat k (D1 a)         = k a
  foldCat k (D2 a b)       = k a . k b
  foldCat k (D3 a b c)     = k a . k b . k c

  traverseCat _ D0         = pure D0
  traverseCat k (D1 a)     = D1 <$> k a
  traverseCat k (D2 a b)   = D2 <$> k a <*> k b
  traverseCat k (D3 a b c) = D3 <$> k a <*> k b <*> k c
