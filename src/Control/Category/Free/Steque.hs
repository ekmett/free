{-# LANGUAGE GADTs, TypeFamilies, PolyKinds, RankNTypes #-}
module Steque
  ( Steque
  , singleton
  , (<|)
  , (|>)
  , null
  ) where

import Control.Applicative
import Control.Category
import Control.Category.Free.Catenated
import Control.Category.Free.View
import Prelude hiding ((.),id,null)

data Consed r a b where
  NilCons :: Consed r a a
  Cons    :: r b c -> Consed r a b -> Consed r a c

instance Catenated Consed where
  foldCat _ NilCons = id
  foldCat f (Cons a b) = f a . foldCat f b
  traverseCat _ NilCons = pure NilCons
  traverseCat f (Cons a b) = Cons <$> f a <*> traverseCat f b

instance Category (Consed r) where
  id = NilCons
  NilCons   . ys = ys
  Cons x xs . ys = Cons x (xs . ys)

instance Uncons Consed where
  uncons (Cons a b) = a :| b
  uncons NilCons    = Empty

instance Cons Consed where
  (<|) = Cons

data Snoced r a b where
  NilSnoc :: Snoced r a a
  Snoc    :: Snoced r b c -> r a b -> Snoced r a c

instance Category (Snoced r) where
  id = NilSnoc
  xs . NilSnoc = xs
  xs . Snoc ys y = Snoc (xs . ys) y

instance Catenated Snoced where
  foldCat _ NilSnoc = id
  foldCat f (Snoc a b) = foldCat f a . f b
  traverseCat _ NilSnoc = pure NilSnoc
  traverseCat f (Snoc a b) = Snoc <$> traverseCat f a <*> f b

instance Unsnoc Snoced where
  unsnoc (Snoc a b) = a :| b
  unsnoc NilSnoc    = Empty

instance Snoc Snoced where
  (|>) = Snoc

-- okasaki realtime queue
data Queue r a b where
  Queue :: !(Consed r b c) -> !(Snoced r a b) -> !(Consed r b x) -> Queue r a c

rotate :: Consed r c d -> Snoced r b c -> Consed r a b -> Consed r a d
rotate NilCons     (Snoc NilSnoc y) zs = Cons y zs
rotate (Cons x xs) (Snoc ys y)      zs = Cons x (rotate xs ys (Cons y zs))
rotate xs          ys               zs = error "Invariant |ys| = |xs| - (|zs| - 1) broken"

queue :: Consed r b c -> Snoced r a b -> Consed r b x -> Queue r a c
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

instance Cons Steque where
  x <| xs = singleton x . xs

instance Snoc Steque where
  xs |> x = xs . singleton x
