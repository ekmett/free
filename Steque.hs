{-# LANGUAGE GADTs, TypeFamilies, PolyKinds, RankNTypes #-}
module Steque
  ( Steque
  , singleton
  , (<|)
  , (|>)
  , null
  ) where

import Prelude hiding ((.),id,null)
import Control.Applicative
import Control.Category
import Catenated
import View

data Cons r a b where
  NilCons :: Cons r a a
  Cons    :: r b c -> Cons r a b -> Cons r a c

instance Catenated Cons where
  foldCat _ NilCons = id
  foldCat f (Cons a b) = f a . foldCat f b
  traverseCat _ NilCons = pure NilCons
  traverseCat f (Cons a b) = Cons <$> f a <*> traverseCat f b

instance Category (Cons r) where
  id = NilCons
  NilCons   . ys = ys
  Cons x xs . ys = Cons x (xs . ys)

instance Uncons Cons where
  uncons (Cons a b) = a :| b
  uncons NilCons    = Empty

data Snoc r a b where
  NilSnoc :: Snoc r a a
  Snoc    :: Snoc r b c -> r a b -> Snoc r a c

instance Category (Snoc r) where
  id = NilSnoc
  xs . NilSnoc = xs
  xs . Snoc ys y = Snoc (xs . ys) y

instance Catenated Snoc where
  foldCat _ NilSnoc = id
  foldCat f (Snoc a b) = foldCat f a . f b
  traverseCat _ NilSnoc = pure NilSnoc
  traverseCat f (Snoc a b) = Snoc <$> traverseCat f a <*> f b

instance Unsnoc Snoc where
  unsnoc (Snoc a b) = a :| b
  unsnoc NilSnoc    = Empty

-- okasaki realtime queue
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
data Steque r x y where
  NilSteque :: Steque r x x
  Steque    :: r y z -> !(Queue (Steque r) x y) -> Steque r x z

instance Category (Steque p) where
  id = NilSteque
  NilSteque              . ys      = ys
  xs                   . NilSteque = xs
  Steque y (Queue f r a) . xs      = Steque y (queue f (Snoc r xs) a)

instance Uncons Steque where
  uncons NilSteque = Empty
  uncons (Steque h t) = h :| linkAll t

linkAll :: Queue (Steque c) x y -> Steque c x y
linkAll (Queue NilCons NilSnoc NilCons) = NilSteque
linkAll (Queue (Cons (Steque h pt) t) f a) = Steque h $ case linkAll (queue t f a) of
  NilSteque -> pt
  ys      -> case pt of
    Queue f' r' a' -> queue f' (Snoc r' ys) a'

null :: Steque c x y -> Bool
null NilSteque = True
null _         = False

-- singleton :: c ~> Steque c
singleton :: c x y -> Steque c x y
singleton c = Steque c (Queue id id id)

(<|) :: c y z -> Steque c x y -> Steque c x z
x <| xs = singleton x . xs

(|>) :: Steque c y z -> c x y -> Steque c x z
xs |> x = xs . singleton x
