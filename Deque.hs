{-# LANGUAGE PolyKinds, RankNTypes, GADTs #-}
module Deque
  ( Deque
  , null
  , empty
  , (<|), (|>)
  ) where

-- deque by implicit recursive slowdown

import Control.Category
import Control.Applicative hiding (empty)
import Catenated
import Prelude hiding ((.), id, null)
import View

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
  Q0   :: Deque r a a
  Q1   :: r a b -> Deque r a b
  Q2   :: r b c -> r a b -> Deque r a c
  Q3   :: r c d -> r b c -> r a b -> Deque r a d
  Deep :: !(Digit r c d) -> Deque (Pair r) b c -> !(Digit r a b) -> Deque r a d

instance Catenated Deque where
  foldCat _ Q0           = id
  foldCat k (Q1 a)       = k a
  foldCat k (Q2 a b)     = k a . k b
  foldCat k (Q3 a b c)   = k a . k b . k c
  foldCat k (Deep a b c) = foldCat k a . foldCat (foldCat k) b . foldCat k c
  traverseCat _ Q0           = pure Q0
  traverseCat k (Q1 a)       = Q1 <$> k a
  traverseCat k (Q2 a b)     = Q2 <$> k a <*> k b
  traverseCat k (Q3 a b c)   = Q3 <$> k a <*> k b <*> k c
  traverseCat k (Deep a b c) = Deep <$> traverseCat k a <*> traverseCat (traverseCat k) b <*> traverseCat k c

null :: Deque r a b -> Bool
null Q0 = True
null _ = False

empty :: Deque r a a
empty = Q0

(<|) :: r b c -> Deque r a b -> Deque r a c
a <| Q0                  = Q1 a
a <| Q1 b                = Q2 a b
a <| Q2 b c              = Q3 a b c
a <| Q3 b c d            = Deep (D2 a b) Q0 (D2 c d)
a <| Deep (D1 b) m r     = Deep (D2 a b) m r
a <| Deep (D2 b c) m r   = Deep (D3 a b c) m r
a <| Deep (D3 b c d) m r = Deep (D2 a b) (Pair c d <| m) r

(|>) :: Deque r b c -> r a b -> Deque r a c
Q0 |> a                  = Q1 a
Q1 b |> a                = Q2 b a
Q2 c b |> a              = Q3 c b a
Q3 d c b |> a            = Deep (D2 d c) Q0 (D2 b a)
Deep l m (D1 b) |> a     = Deep l m (D2 b a)
Deep l m (D2 c b) |> a   = Deep l m (D3 c b a)
Deep l m (D3 d c b) |> a = Deep l (m |> Pair d c) (D2 b a)

digit :: Digit r a b -> Deque r a b
digit (D1 a)     = Q1 a
digit (D2 a b)   = Q2 a b
digit (D3 a b c) = Q3 a b c

instance Uncons Deque where
  uncons (Deep (D3 a b c) m r) = a :| Deep (D2 b c) m r
  uncons (Deep (D2 a b) m r)   = a :| Deep (D1 b) m r
  uncons (Deep (D1 a) m r)     = a :| case uncons m of
    Empty          -> digit r
    Pair b c :| m' -> Deep (D2 b c) m' r
  uncons (Q3 a b c) = a :| Q2 b c
  uncons (Q2 a b)   = a :| Q1 b
  uncons (Q1 a)     = a :| Q0
  uncons Q0         = Empty

instance Unsnoc Deque where
  unsnoc (Deep l m (D3 c b a)) = Deep l m (D2 c b) :| a
  unsnoc (Deep l m (D2 b a))   = Deep l m (D1 b) :| a
  unsnoc (Deep l m (D1 a))     = (:| a) $ case unsnoc m of
    Empty -> digit l
    m' :| Pair b c -> Deep l m' (D2 b c)
  unsnoc (Q3 c b a) = Q2 c b  :| a
  unsnoc (Q2 b a)   = Q1 b :| a
  unsnoc (Q1 a)     = Q0 :| a
  unsnoc Q0         = Empty
