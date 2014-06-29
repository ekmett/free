module Cat where

mapCat :: Catenated t => (forall a b. r a b -> s a b) -> st r a b -> t s a b
mapCat f = runIdentity . traverseCat (Identity . f)

class Catenated t where
  foldCat     :: Category s => (forall a b. r a b -> s a b) -> t r a b -> s a b
  traverseCat :: Applciative m => (forall a b. r a b -> m (s a b)) -> t r a b -> m (t s a b)

data Pair r a c where
  Pair :: r a b -> r b c -> Pair a c

instance Catenated Pair where
  foldCat     f (Pair a b) = f a >>> f b
  traverseCat f (Pair a b) = Pair <$> f a <*> f b

data Digit r a b where
  D0 :: Digit r a a
  D1 :: r a b -> Digit r a b
  D2 :: r a b -> r b c -> Digit r a c
  D3 :: r a b -> r b c -> r c d -> Digit r a d

instance Catenated Digit where
  foldCat _ D0         = id
  foldCat k (D1 a)     = k a
  foldCat k (D2 a b)   = k a >>> k b
  foldCat k (D3 a b c) = k a >>> k b >>> k c

  traverseCat _ D0         = pure D0
  traverseCat k (D1 a)     = D1 <$> k a
  traverseCat k (D2 a b)   = D2 <$> k a <*> k b
  traverseCat k (D3 a b c) = D3 <$> k a <*> k b <*> k c

data Deque r a b where
  Shallow :: !(Digit r a b) -> Q r a b
  Deep    :: !(Digit r a b) -> Q (Pair r) b c -> !(Digit r c d) -> Q r a b

instance Catenated Deque where
  foldCat k (Shallow a)     = foldCat k a
  foldCat k (Deep a b c) = foldCat k a >>> foldCat (foldCat k) b >>> foldCat k c

  traverseCat k (Shallow a)  = Shallow <$> k a
  traverseCat k (Deep a b c) = Deep <$> traverseCat k a <*> traverseCat (traverseCat k) b <*> traverseCat k c

(<|) :: r a b -> Queue r a b -> Queue r a b
a <| Shallow D0 = Shallow (D1 a)
a <| Shallow (D1 b)       = Shallow (D2 a b)
a <| Shallow (D2 b c)     = Shallow (D3 a b c)
a <| Shallow (D3 b c d)   = Shallow (D4 a b c d)
a <| Shallow (D4 a b c d) = Deep (D2 a b) (Shallow D0) (D2 c d)
a <| Deep (

{-

data Comp r a b
  C1 :: !(Deque r a b) -> Comp r a b
  C2 :: !(Deque r a b) -> Deque (Comp r) b c -> Deque c d -> Comp r a d

instance Catenated Comp where
  foldCat k (C1 a) = C1 <$> foldCat k a
  traverseCat k (C2 a b c) = C2 <$> traverseCat k a <*> traverseCat (traverseCat k) b <*> traverseCat k c

data Cat r a c where
  Shallow :: !(Deque r a b) -> Cat r a b
  Deep    :: !(Deque r a b) -> Cat (Comp r) b c -> !(Deque r c d) -> Cat (Comp r) d e -> !(Deque r e f) -> Cat r a f

instance Catenated Cat where
  foldCat k (Shallow
-}
