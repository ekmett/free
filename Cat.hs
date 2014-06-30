{-# LANGUAGE RankNTypes, BangPatterns, PolyKinds, GADTs #-}
module Cat where

import Catenated
import Control.Applicative
import Control.Category
import qualified Deque as D
import Prelude hiding ((.),id)
import View

-- okasaki implicit recursive catenable deque

data Component r a b where
  C1 :: !(D.Deque r a b) -> Component r a b
  C2 :: !(D.Deque r c d) -> Cat (Component r) b c -> !(D.Deque r a b) -> Component r a d

instance Catenated Component where
  foldCat k (C1 a) = foldCat k a
  foldCat k (C2 a b c) = foldCat k a . foldCat (foldCat k) b . foldCat k c
  traverseCat k (C1 a)     = C1 <$> traverseCat k a
  traverseCat k (C2 a b c) = C2 <$> traverseCat k a <*> traverseCat (traverseCat k) b <*> traverseCat k c

data Cat r a c where
  Shallow :: !(D.Deque r a b) -> Cat r a b
  Deep    :: !(D.Deque r e f) -> Cat (Component r) d e -> !(D.Deque r c d) -> Cat (Component r) b c -> !(D.Deque r a b) -> Cat r a f

instance Catenated Cat where
  foldCat k (Shallow a)      = foldCat k a
  foldCat k (Deep a b c d e) = foldCat k a . foldCat (foldCat k) b . foldCat k c . foldCat (foldCat k) d . foldCat k e
  traverseCat k (Shallow a)      = Shallow <$> traverseCat k a
  traverseCat k (Deep a b c d e) = Deep <$> traverseCat k a <*> traverseCat (traverseCat k) b
                                        <*> traverseCat k c <*> traverseCat (traverseCat k) d
                                        <*> traverseCat k e

instance Category (Cat r) where
  id = Shallow D.empty
