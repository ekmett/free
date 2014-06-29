{-# LANGUAGE PolyKinds, RankNTypes, GADTs #-}
module Ok where

import Control.Category
import Control.Applicative
import Prelude hiding ((.), id)

class Catenated t where
  foldCat     :: Category s => (forall a b. r a b -> s a b) -> t r a b -> s a b
  traverseCat :: Applicative m => (forall a b. r a b -> m (s a b)) -> t r a b -> m (t s a b)

data Digit :: (i -> i -> *) -> i -> i -> * where
  D0 :: Digit r a a
  D1 :: r a b -> Digit r a b
  D2 :: r b c -> r a b -> Digit r a c
  D3 :: r c d -> r b c -> r a b -> Digit r a d

instance Catenated Digit where
  foldCat _ D0             = id
  foldCat k (D1 a)         = k a
  foldCat k (D2 a b)       = k a . k b
  foldCat k (D3 a b c)     = k a . k b . k c

  traverseCat _ D0         = pure D0
  traverseCat k (D1 a)     = D1 <$> k a
  traverseCat k (D2 a b)   = D2 <$> k a <*> k b
  traverseCat k (D3 a b c) = D3 <$> k a <*> k b <*> k c

data Pair :: (i -> i -> *) -> i -> i -> * where
  Pair :: r b c -> r a b -> Pair r a c

instance Catenated Pair where
  foldCat k (Pair a b) = k a . k b
  traverseCat k (Pair a b) = Pair <$> k a <*> k b

data Deque :: (i -> i -> *) -> i -> i -> * where
  Shallow :: !(Digit r a b) -> Deque r a b
  Deep    :: !(Digit r c d) -> Deque (Pair r) b c -> !(Digit r a b) -> Deque r a d

instance Catenated Deque where
  foldCat k (Shallow a) = foldCat k a
  foldCat k (Deep a b c) = foldCat k a . foldCat (foldCat k) b . foldCat k c
  traverseCat k (Shallow a) = Shallow <$> traverseCat k a
  traverseCat k (Deep a b c) = Deep <$> traverseCat k a <*> traverseCat (traverseCat k) b <*> traverseCat k c

