{-# LANGUAGE RankNTypes, PolyKinds, GADTs #-}
module Seq where

import Control.Applicative
import Control.Category
import Data.Monoid
import Data.Functor.Identity
import Data.Traversable
import Prelude hiding ((.),id)

-- categorical Data.Sequence

fmapCat :: Categorical t => (forall a b. c a b -> d a b) -> t c x y -> t d x y
fmapCat f = runIdentity . traverseCat (Identity . f)

class Categorical (t :: (i -> i -> *) -> i -> i -> *) where
  foldCat     :: Category d => (forall a b. c a b -> d a b) -> t c x y -> d x y
  traverseCat :: Applicative m => (forall a b. c a b -> m (d a b)) -> t c x y -> m (t d x y)

data Seq r a b where
  Empty  :: Seq r a a
  Single :: r a b -> Seq r a b
  Deep   :: !(Digit r a b) -> Seq (Node r) b c -> !(Digit r c d) -> Seq r a d

instance Categorical Seq where
  foldCat _ Empty = id
  foldCat f (Single c) = f c
  foldCat f (Deep l d r) = foldCat f l >>> foldCat (foldCat f) d >>> foldCat f r
  traverseCat _ Empty = pure Empty
  traverseCat f (Single c) = Single <$> f c
  traverseCat f (Deep l d r) = Deep <$> traverseCat f l <*> traverseCat (traverseCat f) d <*> traverseCat f r

data Node r a b where
  Node2 :: r a b -> r b c -> Node r a c
  Node3 :: r a b -> r b c -> r c d -> Node r a d

instance Categorical Node where
  foldCat f (Node2 a b) = f a >>> f b
  foldCat f (Node3 a b c) = f a >>> f b >>> f c
  traverseCat f (Node2 a b) = Node2 <$> f a <*> f b
  traverseCat f (Node3 a b c) = Node3 <$> f a <*> f b <*> f c

data Digit r a b where
  One   :: r a b -> Digit r a b
  Two   :: r a b -> r b c -> Digit r a c
  Three :: r a b -> r b c -> r c d -> Digit r a d
  Four  :: r a b -> r b c -> r c d -> r d e -> Digit r a e

instance Categorical Digit where
  foldCat f (One a) = f a
  foldCat f (Two a b) = f a >>> f b
  foldCat f (Three a b c) = f a >>> f b >>> f c
  foldCat f (Four a b c d) = f a >>> f b >>> f c >>> f d
  traverseCat f (One a) = One <$> f a
  traverseCat f (Two a b) = Two <$> f a <*> f b
  traverseCat f (Three a b c) = Three <$> f a <*> f b <*> f c
  traverseCat f (Four a b c d) = Four <$> f a <*> f b <*> f c <*> f d

snoc :: Seq r a b -> r b c -> Seq r a c
snoc Empty a                      = Single a
snoc (Single b) a                 = Deep (One b) Empty (One a)
snoc (Deep pr m (Four e d c b)) a = Deep pr (snoc m (Node3 e d c)) (Two b a)
snoc (Deep pr m (Three d c b)) a  = Deep pr m (Four d c b a)
snoc (Deep pr m (Two c b)) a      = Deep pr m (Three c b a)
snoc (Deep pr m (One b)) a        = Deep pr m (Two b a)

cons :: r a b -> Seq r b c -> Seq r a c
cons a Empty                      = Single a
cons a (Single b)                 = Deep (One a) Empty (One b)
cons a (Deep (Four b c d e) m sf) = Deep (Two a b) (cons (Node3 c d e) m) sf
cons a (Deep (Three b c d) m sf)  = Deep (Four a b c d) m sf
cons a (Deep (Two b c) m sf)      = Deep (Three a b c) m sf
cons a (Deep (One b) m sf)        = Deep (Two a b) m sf

data View l r a c where
  Nil :: Nil
  (:|) :: l a b -> r b c -> View l r a c

{-
uncons :: r a b -> View r (Seq r) a c
uncons Empty = Nil
uncons (Single b) = b :| Empty
uncons (Deep (One a) Empty (One b)) = a :| Single b
uncons (Deep (Two a b)
-}
