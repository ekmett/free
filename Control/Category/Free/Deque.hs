{-# LANGUAGE PolyKinds, RankNTypes, GADTs #-}
module Deque
  ( Deque(..)
  , Digit(..)
  , null
  , empty
  , (<|), (|>)
  ) where

-- deque by implicit recursive slowdown

import Control.Applicative hiding (empty)
import Control.Category
import Control.Category.Free.Catenated
import Control.Category.Free.View
import Prelude hiding ((.), id, null)

data Digit :: (i -> i -> *) -> i -> i -> * where
  D1 :: r a b -> Digit r a b
  D2 :: r b c -> r a b -> Digit r a c
  D3 :: r c d -> r b c -> r a b -> Digit r a d

instance Catenated Digit where
  foldCat k (D1 a)         = k a
  foldCat k (D2 a b)       = k a . k b
  foldCat k (D3 a b c)     = k a . k b . k c

  traverseCat k (D1 a)     = D1 <$> k a
  traverseCat k (D2 a b)   = D2 <$> k a <*> k b
  traverseCat k (D3 a b c) = D3 <$> k a <*> k b <*> k c

data Pair :: (i -> i -> *) -> i -> i -> * where
  Pair :: r b c -> r a b -> Pair r a c

instance Catenated Pair where
  foldCat k (Pair a b) = k a . k b
  traverseCat k (Pair a b) = Pair <$> k a <*> k b

data Deque :: (i -> i -> *) -> i -> i -> * where
  Id    :: Deque r a a
  Digit :: !(Digit r a b) -> Deque r a b
  Deque :: !(Digit r c d) -> Deque (Pair r) b c -> !(Digit r a b) -> Deque r a d

instance Catenated Deque where
  foldCat _ Id            = id
  foldCat k (Digit a)     = foldCat k a
  foldCat k (Deque a b c) = foldCat k a . foldCat (foldCat k) b . foldCat k c
  traverseCat _ Id            = pure Id
  traverseCat k (Digit a)     = Digit <$> traverseCat k a
  traverseCat k (Deque a b c) = Deque <$> traverseCat k a <*> traverseCat (traverseCat k) b <*> traverseCat k c

null :: Deque r a b -> Bool
null Id = True
null _ = False

empty :: Deque r a a
empty = Id

instance Cons Deque where
  a <| Id                   = Digit (D1 a)
  a <| Digit (D1 b)         = Digit (D2 a b)
  a <| Digit (D2 b c)       = Digit (D3 a b c)
  a <| Digit (D3 b c d)     = Deque (D2 a b) Id (D2 c d)
  a <| Deque (D1 b) m r     = Deque (D2 a b) m r
  a <| Deque (D2 b c) m r   = Deque (D3 a b c) m r
  a <| Deque (D3 b c d) m r = Deque (D2 a b) (Pair c d <| m) r

instance Snoc Deque where
  Id |> a                   = Digit (D1 a)
  Digit (D1 b) |> a         = Digit (D2 b a)
  Digit (D2 c b) |> a       = Digit (D3 c b a)
  Digit (D3 d c b) |> a     = Deque (D2 d c) Id (D2 b a)
  Deque l m (D1 b) |> a     = Deque l m (D2 b a)
  Deque l m (D2 c b) |> a   = Deque l m (D3 c b a)
  Deque l m (D3 d c b) |> a = Deque l (m |> Pair d c) (D2 b a)

instance Uncons Deque where
  uncons (Deque (D3 a b c) m r) = a :| Deque (D2 b c) m r
  uncons (Deque (D2 a b) m r)   = a :| Deque (D1 b) m r
  uncons (Deque (D1 a) m r)     = a :| case uncons m of
    Empty          -> Digit r
    Pair b c :| m' -> Deque (D2 b c) m' r
  uncons (Digit (D3 a b c)) = a :| Digit (D2 b c)
  uncons (Digit (D2 a b))   = a :| Digit (D1 b)
  uncons (Digit (D1 a))     = a :| Id
  uncons Id                 = Empty

instance Unsnoc Deque where
  unsnoc (Deque l m (D3 c b a)) = Deque l m (D2 c b) :| a
  unsnoc (Deque l m (D2 b a))   = Deque l m (D1 b) :| a
  unsnoc (Deque l m (D1 a))     = (:| a) $ case unsnoc m of
    Empty -> Digit l
    m' :| Pair b c -> Deque l m' (D2 b c)
  unsnoc (Digit (D3 c b a)) = Digit (D2 c b)  :| a
  unsnoc (Digit (D2 b a))   = Digit (D1 b) :| a
  unsnoc (Digit (D1 a))     = Id :| a
  unsnoc Id                 = Empty
