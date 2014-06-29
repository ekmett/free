{-# LANGUAGE GADTs, TypeFamilies, PolyKinds, RankNTypes #-}
module Thrists where

import Prelude hiding ((.),id,null)
import Control.Applicative
import Control.Category

class Cat t where
  foldCat     :: Category s    => (forall a b. r a b -> s a b)     -> t r a b -> s a b
  traverseCat :: Applicative m => (forall a b. r a b -> m (s a b)) -> t r a b -> m (t s a b)

data Cons r a b where
  NilCons :: Cons r a a
  Cons    :: r b c -> Cons r a b -> Cons r a c

instance Category (Cons r) where
  id = NilCons
  NilCons   . ys = ys
  Cons x xs . ys = Cons x (xs . ys)

data Snoc r a b where
  NilSnoc :: Snoc r a a
  Snoc    :: Snoc r b c -> r a b -> Snoc r a c

instance Category (Snoc r) where
  id = NilSnoc
  xs . NilSnoc = xs
  xs . Snoc ys y = Snoc (xs . ys) y

data Queue r a b where
  Queue :: !(Cons r b c) -> !(Snoc r a b) -> !(Cons r b x) -> Queue r a c

rotate :: Cons r c d -> Snoc r b c -> Cons r a b -> Cons r a d
rotate NilCons     (Snoc NilSnoc y) zs = Cons y zs
rotate (Cons x xs) (Snoc ys y)      zs = Cons x (rotate xs ys (Cons y zs))
rotate xs          ys               zs = error "Invariant |ys| = |xs| - (|zs| - 1) broken"

queue :: Cons r b c -> Snoc r a b -> Cons r b x -> Queue r a c
queue xs ys NilCons    = Queue xs' NilSnoc xs' where xs' = rotate xs ys NilCons
queue xs ys (Cons h t) = Queue xs ys t

-- the free category over c as a queue
data Path r x y where
  NilPath :: Path r x x
  Path    :: r y z -> !(Queue (Path r) x y) -> Path r x z

instance Category (Path p) where
  id = NilPath
  NilPath              . ys      = ys
  xs                   . NilPath = xs
  Path y (Queue f r a) . xs      = Path y (queue f (Snoc r xs) a)

-- singleton :: c ~> Path c
singleton :: c x y -> Path c x y
singleton c = Path c (Queue id id id)

data View c x z where
  Empty :: View c x x
  (:|) :: c y z -> !(Path c x y) -> View c x z

-- uncons :: Path ~> View
uncons :: Path c x z -> View c x z
uncons NilPath = Empty
uncons (Path h t) = h :| linkAll t

linkAll :: Queue (Path c) x y -> Path c x y
linkAll (Queue NilCons NilSnoc NilCons) = NilPath
linkAll (Queue (Cons (Path h pt) t) f a) = Path h $ case linkAll (queue t f a) of
  NilPath -> pt
  ys      -> case pt of
    Queue f' r' a' -> queue f' (Snoc r' ys) a'

cons :: c y z -> Path c x y -> Path c x z
cons x xs = singleton x . xs

snoc :: Path c y z -> c x y -> Path c x z
snoc xs x = xs . singleton x

null :: Path c x y -> Bool
null NilPath = True
null _       = False
