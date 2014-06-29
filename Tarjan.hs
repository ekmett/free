{-# LANGUAGE RankNTypes, GADTs, PolyKinds #-}
module Tarjan where

import Control.Applicative
import Control.Category
import Data.Monoid
import Prelude hiding ((.),id)

-- Radu Mihaesau and Robert Tarjan's Catenable Deque
-- TODO: we need fast access to non-4s

class Cat (t :: (i -> i -> *) -> i -> i -> *) where
  foldCat     :: Category m    => (forall a b. r a b -> m a b)     -> t r a b -> m a b
  traverseCat :: Applicative m => (forall a b. r a b -> m (s a b)) -> t r a b -> m (t s a b)

data Digit r a b where
  D3 :: r a b -> r b c -> r c d -> Digit r a d
  D4 :: r a b -> r b c -> r c d -> r d e -> Digit r a e
  D5 :: r a b -> r b c -> r c d -> r d e -> r e f -> Digit r a f
  D6 :: r a b -> r b c -> r c d -> r d e -> r e f -> r f g -> Digit r a g

instance Cat Digit where
  foldCat k (D3 a b c)         = k a >>> k b >>> k c
  foldCat k (D4 a b c d)       = k a >>> k b >>> k c >>> k d
  foldCat k (D5 a b c d e)     = k a >>> k b >>> k c >>> k d >>> k e
  foldCat k (D6 a b c d e f)   = k a >>> k b >>> k c >>> k d >>> k e >>> k f

  traverseCat k (D3 a b c)         = D3 <$> k a <*> k b <*> k c
  traverseCat k (D4 a b c d)       = D4 <$> k a <*> k b <*> k c <*> k d
  traverseCat k (D5 a b c d e)     = D5 <$> k a <*> k b <*> k c <*> k d <*> k e
  traverseCat k (D6 a b c d e f)   = D6 <$> k a <*> k b <*> k c <*> k d <*> k e <*> k f

data Node (r :: i -> i -> *) (a :: i) (b :: i) where
  N2 :: r a b -> r b c -> Node r a c
  N3 :: r a b -> r b c -> r c d -> Node r a d

instance Cat Node where
  foldCat k (N2 a b)       = k a >>> k b
  foldCat k (N3 a b c)     = k a >>> k b >>> k c

  traverseCat k (N2 a b)   = N2 <$> k a <*> k b
  traverseCat k (N3 a b c) = N3 <$> k a <*> k b <*> k c

data Entry (k :: i -> i -> *) (a :: i) (b :: i) where
  E1 :: !(Node k a b) -> Entry k a b
  E3 :: !(Node k a b) -> Deque (Entry k) b c -> !(Node k c d) -> Entry k a d

instance Cat Entry where
  foldCat k (E1 m) = foldCat k m
  foldCat k (E3 l m r) = foldCat k l >>> foldCat (foldCat k) m >>> foldCat k r
  traverseCat k (E1 m)     = E1 <$> traverseCat k m
  traverseCat k (E3 l m r) = E3 <$> traverseCat k l <*> traverseCat (traverseCat k) m <*> traverseCat k r

data Deque k a b where
  B0 :: Deque r a a
  B1 :: r a b -> Deque r a b
  B2 :: r a b -> r b c -> Deque r a c
  B3 :: r a b -> r b c -> r c d -> Deque r a d
  B4 :: r a b -> r b c -> r c d -> r d e -> Deque r a e
  B5 :: r a b -> r b c -> r c d -> r d e -> r e f -> Deque r a f
  B6 :: r a b -> r b c -> r c d -> r d e -> r e f -> r f g -> Deque r a g
  B7 :: r a b -> r b c -> r c d -> r d e -> r e f -> r f g -> r g h -> Deque r a h
  Q1 :: !(Digit k a b) -> Deque (Entry k) b c -> !(Digit k c d) -> Deque k a d
  Q2 :: !(Digit k a b) -> Deque (Entry k) b c -> k c d -> k d e -> Deque (Entry k) e f -> !(Digit k f g) -> Deque k a g

instance Cat Deque where
  foldCat _ B0                 = id
  foldCat k (B1 a)             = k a
  foldCat k (B2 a b)           = k a >>> k b
  foldCat k (B3 a b c)         = k a >>> k b >>> k c
  foldCat k (B4 a b c d)       = k a >>> k b >>> k c >>> k d
  foldCat k (B5 a b c d e)     = k a >>> k b >>> k c >>> k d >>> k e
  foldCat k (B6 a b c d e f)   = k a >>> k b >>> k c >>> k d >>> k e >>> k f
  foldCat k (B7 a b c d e f g) = k a >>> k b >>> k c >>> k d >>> k e >>> k f >>> k g
  foldCat k (Q1 f m r)         = foldCat k f >>> foldCat (foldCat k) m >>> foldCat k r
  foldCat k (Q2 f a m n p r)   = foldCat k f >>> foldCat (foldCat k) a >>> k m >>> k n >>> foldCat (foldCat k) p >>> foldCat k r

  traverseCat _ B0                 = pure B0
  traverseCat k (B1 a)             = B1 <$> k a
  traverseCat k (B2 a b)           = B2 <$> k a <*> k b
  traverseCat k (B3 a b c)         = B3 <$> k a <*> k b <*> k c
  traverseCat k (B4 a b c d)       = B4 <$> k a <*> k b <*> k c <*> k d
  traverseCat k (B5 a b c d e)     = B5 <$> k a <*> k b <*> k c <*> k d <*> k e
  traverseCat k (B6 a b c d e f)   = B6 <$> k a <*> k b <*> k c <*> k d <*> k e <*> k f
  traverseCat k (B7 a b c d e f g) = B7 <$> k a <*> k b <*> k c <*> k d <*> k e <*> k f <*> k g
  traverseCat k (Q1 f m r)         = Q1 <$> traverseCat k f <*> traverseCat (traverseCat k) m <*> traverseCat k r
  traverseCat k (Q2 f a m n p r)   = Q2 <$> traverseCat k f <*> traverseCat (traverseCat k) a <*> k m
                                        <*> k n <*> traverseCat (traverseCat k) p <*> traverseCat k r

data View l r a c where
  Empty :: View l r a a
  (:|)  :: l a b -> r b c -> View l r a c

fixl3 :: Deque k a b -> Deque k a b
fixl3 (Q1 p@D4{} m r)                     = Q1 p (fixl3 m) r
fixl3 (Q1 (D3 a b c) B0 (D3 d e f))       = B6 a b c d e f
fixl3 (Q1 (D3 a b c) B0 (D4 d e f g))     = B7 a b c d e f g
fixl3 (Q1 (D3 a b c) B0 (D5 d e f g h))   = Q1 (D4 a b c d) B0 (D4 e f g h)
fixl3 (Q1 (D3 a b c) B0 (D6 d e f g h i)) = Q1 (D4 a b c d) B0 (D5 e f g h i)
-- fixl3 (Q1 (D3 a b c) m  r                 = Q1 (E1 (N2 b c) <| m) r
fixl3 xs = xs

uncons :: Deque k a b -> View k (Deque k) a b
uncons B0                  = Empty
uncons (B1 a)              = a :| B0
uncons (B2 a b)            = a :| B1 b
uncons (B3 a b c)          = a :| B2 b c
uncons (B4 a b c d)        = a :| B3 b c d
uncons (B5 a b c d e)      = a :| B4 b c d e
uncons (B6 a b c d e f)    = a :| B5 b c d e f
uncons (B7 a b c d e f g)  = a :| B6 b c d e f g
uncons (Q1 (D3 a b c) B0 (D3 d e f))       = a :| B5 b c d e f
uncons (Q1 (D3 a b c) B0 (D4 d e f g))     = a :| B6 b c d e f g
uncons (Q1 (D3 a b c) B0 (D5 d e f g h))   = a :| B7 b c d e f g h
uncons (Q1 (D3 a b c) B0 (D6 d e f g h i)) = a :| Q1 (D4 b c d e) B0 (D4 f g h i)
{-
uncons (Q1 (D3 a b c) m r = case uncons m of
  E1 (N2 d e) :| m' -> a :| Q1 (D4 b c d e) m' r
  E3 (N2 d e) l'  :| :: !(Node k a b) -> Deque (Entry k) b c -> !(Node k c d) -> Entry k a d
-}
  --

--  a :| Q1 (E1 (N2 b c) <| m) r
uncons (Q1 (D4 a b c d) m r)     = a :| Q1 (D3 b c d) (fixl3 m) r
uncons (Q1 (D5 a b c d e) m r)   = a :| Q1 (D4 b c d e) m r
uncons (Q1 (D6 a b c d e f) m r) = a :| Q1 (D5 b c d e f) m r


infixr 5 <|, ><
infixl 5 |>
(<|) :: k a b -> Deque k b c -> Deque k a c
a <| B0                            = B1 a
a <| B1 b                          = B2 a b
a <| B2 b c                        = B3 a b c
a <| B3 b c d                      = B4 a b c d
a <| B4 b c d e                    = B5 a b c d e
a <| B5 b c d e f                  = B6 a b c d e f
a <| B6 b c d e f g                = B7 a b c d e f g
a <| B7 b c d e f g h              = Q1 (D4 a b c d) B0 (D4 e f g h)
a <| Q1 (D3 b c d) m r             = Q1 (D4 a b c d) m r
a <| Q1 (D4 b c d e) m r           = Q1 (D5 a b c d e) (fixl56 m) r
a <| Q1 (D5 b c d e f) m r         = Q1 (D4 a b c d) (E1 (N2 e f) <| m) r
a <| Q1 (D6 b c d e f g) m r       = Q1 (D4 a b c d) (E1 (N3 e f g) <| m) r
a <| Q2 (D3 b c d) l m n r s       = Q2 (D4 a b c d) l m n r s
a <| Q2 (D4 b c d e) l m n r s     = Q2 (D5 a b c d e) (fixl56 l) m n r s
a <| Q2 (D5 b c d e f) l m n r s   = Q2 (D4 a b c d) (E1 (N2 e f) <| l ) m n r s
a <| Q2 (D6 b c d e f g) l m n r s = Q2 (D4 a b c d) (E1 (N3 e f g) <| l) m n r s

-- ensure the deque is not 5,6 exposed on the left
fixl56 :: Deque k a c -> Deque k a c
fixl56 (Q1 p@D4{} m r)                 = Q1 p (fixl56 m) r
fixl56 (Q1 (D5 a b c d e) m r)         = Q1 (D3 a b c) (E1 (N2 d e)   <| m) r
fixl56 (Q1 (D6 a b c d e f) m r)       = Q1 (D3 a b c) (E1 (N3 d e f) <| m) r
fixl56 (Q2 p@D4{} l m n r s)           = Q2 p (fixl56 l) m n r s
fixl56 (Q2 (D5 a b c d e) l m n r s)   = Q2 (D3 a b c) (E1 (N2 d e)   <| l) m n r s
fixl56 (Q2 (D6 a b c d e f) l m n r s) = Q2 (D3 a b c) (E1 (N3 d e f) <| l) m n r s
fixl56 xs = xs

(|>) :: Deque k a b -> k b c -> Deque k a c
B0 |> a                            = B1 a
B1 b |> a                          = B2 b a
B2 c b |> a                        = B3 c b a
B3 d c b |> a                      = B4 d c b a
B4 e d c b |> a                    = B5 e d c b a
B5 f e d c b |> a                  = B6 f e d c b a
B6 g f e d c b |> a                = B7 g f e d c b a
B7 h g f e d c b |> a              = Q1 (D4 h g f e) B0 (D4 d c b a)
Q1 p m (D3 d c b) |> a             = Q1 p m (D4 d c b a)
Q1 p m (D4 e d c b) |> a           = Q1 p (fixr56 m) (D5 e d c b a)
Q1 p m (D5 f e d c b) |> a         = Q1 p (m |> E1 (N2 f e)) (D4 d c b a)
Q1 p m (D6 g f e d c b) |> a       = Q1 p (m |> E1 (N3 g f e)) (D4 d c b a)
Q2 p l m n r (D3 d c b) |> a       = Q2 p l m n r (D4 d c b a)
Q2 p l m n r (D4 e d c b) |> a     = Q2 p l m n (fixr56 r) (D5 e d c b a)
Q2 p l m n r (D5 f e d c b) |> a   = Q2 p l m n (r |> E1 (N2 f e)) (D4 d c b a)
Q2 p l m n r (D6 g f e d c b) |> a = Q2 p l m n (r |> E1 (N3 g f e)) (D4 d c b a)

-- ensure the deque is not 5,6 exposed on the right
fixr56 :: Deque k a c -> Deque k a c
fixr56 (Q1 p m r@D4{})                 = Q1 p (fixr56 m) r
fixr56 (Q1 p m (D5 a b c d e))         = Q1 p (m |> E1 (N2 a b)) (D3 c d e)
fixr56 (Q1 p m (D6 a b c d e f))       = Q1 p (m |> E1 (N3 a b c)) (D3 d e f)
fixr56 (Q2 p l m n r s@D4{})           = Q2 p l m n (fixr56 r) s
fixr56 (Q2 p l m n r (D5 a b c d e))   = Q2 p l m n (r |> E1 (N2 a b)) (D3 c d e)
fixr56 (Q2 p l m n r (D6 a b c d e f)) = Q2 p l m n (r |> E1 (N3 a b c)) (D3 d e f)
fixr56 xs = xs

(><) :: Deque k a b -> Deque k b c -> Deque k a c
B0 >< ys                           = ys
xs >< B0                           = xs
B1 a >< ys                         = a <| ys
xs >< B1 a                         = xs |> a
B2 a b >< ys                       = a <| b <| ys
xs >< B2 a b                       = xs |> a |> b
B3 a b c >< ys                     = a <| b <| c <| ys
xs >< B3 a b c                     = xs |> a |> b |> c
B4 a b c d >< ys                   = a <| b <| c <| d <| ys
xs >< B4 a b c d                   = xs |> a |> b |> c |> d
B5 a b c d e >< ys                 = a <| b <| c <| d <| e <| ys
xs >< B5 a b c d e                 = xs |> a |> b |> c |> d |> e
B6 a b c d e f >< ys               = a <| b <| c <| d <| e <| f <| ys
xs >< B6 a b c d e f               = xs |> a |> b |> c |> d |> e |> f
B7 a b c d e f g >< ys             = a <| b <| c <| d <| e <| f <| g <| ys
xs >< B7 a b c d e f g             = xs |> a |> b |> c |> d |> e |> f |> g
xs >< ys = case prefix xs of
  Half l m r -> case suffix ys of
    Half l' m' r' -> Q2 l m r l' m' r'

data Half l m r a c where
  Half :: l a b -> m b c -> r c d -> Half l m r a d

prefix :: Deque k a b -> Half (Digit k) (Deque (Entry k)) k a b
prefix (Q1 p m (D3 a b c))             = Half p (m |> E1 (N2 a b)) c
prefix (Q1 p m (D4 a b c d))           = Half p (m |> E1 (N3 a b c)) d
prefix (Q1 p m (D5 a b c d e))         = Half p (m |> E1 (N2 a b) |> E1 (N2 c d)) e
prefix (Q1 p m (D6 a b c d e f))       = Half p (m |> E1 (N2 a b) |> E1 (N3 c d e)) f
prefix (Q2 p l m n r (D3 a b c))       = Half p (l |> E3 (N2 m n) r (N2 a b)) c
prefix (Q2 p l m n r (D4 a b c d))     = Half p (l |> E3 (N2 m n) r (N3 a b c)) d
prefix (Q2 p l m n r (D5 a b c d e))   = Half p (l |> E3 (N2 m n) r (N2 a b)   |> E1 (N2 c d)) e
prefix (Q2 p l m n r (D6 a b c d e f)) = Half p (l |> E3 (N2 m n) r (N3 a b c) |> E1 (N2 d e)) f

suffix :: Deque k a b -> Half k (Deque (Entry k)) (Digit k) a b
suffix (Q1 (D3 a b c) m r)             = Half a (E1 (N2 b c)   <| m) r
suffix (Q1 (D4 a b c d) m r)           = Half a (E1 (N3 b c d) <| m) r
suffix (Q1 (D5 a b c d e) m r)         = Half a (E1 (N2 b c)   <| E1 (N2 d e) <| m) r
suffix (Q1 (D6 a b c d e f) m r)       = Half a (E1 (N3 b c d) <| E1 (N2 e f) <| m) r
suffix (Q2 (D3 a b c) l m n r s)       = Half a (E3 (N2 b c)   l (N2 m n) <| r) s
suffix (Q2 (D4 a b c d) l m n r s)     = Half a (E3 (N3 b c d) l (N2 m n) <| r) s
suffix (Q2 (D5 a b c d e) l m n r s)   = Half a (E1 (N2 b c)   <| E3 (N2 d e) l (N2 m n) <| r) s
suffix (Q2 (D6 a b c d e f) l m n r s) = Half a (E1 (N3 b c d) <| E3 (N2 e f) l (N2 m n) <| r) s

