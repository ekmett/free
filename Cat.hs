{-# LANGUAGE RankNTypes, BangPatterns, PolyKinds, GADTs #-}
module Cat
  ( Cat
  , singleton
  , (<|), (|>)
  ) where

import Catenated
import Control.Applicative
import Control.Category
import qualified Deque as D
import Deque (Digit(..))
import Prelude hiding ((.),id)
import View

data Component r a b where
  Simple  :: !(D.Deque r a b) -> Component r a b
  Complex :: !(D.Deque r c d) -> Cat (Component r) b c -> !(D.Deque r a b) -> Component r a d

instance Catenated Component where
  foldCat k (Simple a)      = foldCat k a
  foldCat k (Complex a b c) = foldCat k a . foldCat (foldCat k) b . foldCat k c

  traverseCat k (Simple a)      = Simple <$> traverseCat k a
  traverseCat k (Complex a b c) = Complex <$> traverseCat k a <*> traverseCat (traverseCat k) b <*> traverseCat k c

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

singleton :: r a b -> Cat r a b
singleton = Shallow . D.Digit . D1

infixr 5 <|
(<|) :: r b c -> Cat r a b -> Cat r a c
x <| Shallow q      = Shallow (x D.<| q)
x <| Deep f a m b r = Deep (x D.<| f) a m b r

infixl 5 |>
(|>) :: Cat r b c -> r a b -> Cat r a c
Shallow q      |> x = Shallow (q D.|> x)
Deep f a m b r |> x = Deep f a m b (r D.|> x)

consDigit :: Digit r b c -> Cat r a b -> Cat r a c
D1 x `consDigit` Shallow q          = Shallow (x D.<| q)
D2 x y `consDigit` Shallow q        = Shallow (x D.<| y D.<| q)
D3 x y z `consDigit` Shallow q      = Shallow (x D.<| y D.<| z D.<| q)
D1 x `consDigit` Deep f a m b r     = Deep (x D.<| f) a m b r
D2 x y `consDigit` Deep f a m b r   = Deep (x D.<| y D.<| f) a m b r
D3 x y z `consDigit` Deep f a m b r = Deep (x D.<| y D.<| z D.<| f) a m b r

snocDigit :: Cat r b c -> Digit r a b -> Cat r a c
Shallow q `snocDigit` D1 x          = Shallow (q D.|> x)
Shallow q `snocDigit` D2 x y        = Shallow (q D.|> x D.|> y)
Shallow q `snocDigit` D3 x y z      = Shallow (q D.|> x D.|> y D.|> z)
Deep f a m b r `snocDigit` D1 x     = Deep f a m b (r D.|> x)
Deep f a m b r `snocDigit` D2 x y   = Deep f a m b (r D.|> x D.|> y)
Deep f a m b r `snocDigit` D3 x y z = Deep f a m b (r D.|> x D.|> y D.|> z)

instance Category (Cat r) where
  id = Shallow D.Id
  Shallow D.Id        . rs  = rs
  ls . Shallow D.Id         = ls
  Shallow (D.Digit d) . rs  = consDigit d rs
  ls . Shallow (D.Digit d)  = snocDigit ls d
  Shallow ls . Shallow rs = case unsnoc ls of
    i :| l -> case uncons rs of
      h :| t -> Deep i id (D.Digit (D.D2 l h)) id t
  Shallow d . Deep f a m b r = Deep d (Simple f <| a) m b r
  Deep f a m b r . Shallow d = Deep f a m (b |> Simple r) d
  Deep f1 a1 m1 b1 r1 . Deep f2 a2 m2 b2 r2 = case unsnoc r1 of
    i :| l -> case uncons f2 of
      h :| t -> Deep f1 (a1 |> Complex m1 b1 i) (D.Digit (D.D2 l h)) (Complex t a2 m2 <| b2) r2
