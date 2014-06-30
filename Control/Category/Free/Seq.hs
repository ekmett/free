{-# LANGUAGE RankNTypes, PolyKinds, GADTs #-}
module Control.Category.Free.Seq
  ( Seq
  , null
  , singleton
  ) where

import Control.Applicative
import Control.Category
import Control.Category.Free.Catenated
import Control.Category.Free.View
import Data.Monoid
import Data.Functor.Identity
import Data.Traversable
import Prelude hiding ((.),id)

data Seq r a b where
  Id     :: Seq r a a
  Single :: r a b -> Seq r a b
  Deep   :: !(Digit r c d) -> Seq (Node r) b c -> !(Digit r a b) -> Seq r a d

instance Catenated Seq where
  foldCat _ Id           = id
  foldCat f (Single c)   = f c
  foldCat f (Deep l d r) = foldCat f l . foldCat (foldCat f) d . foldCat f r

  traverseCat _ Id           = pure Id
  traverseCat f (Single c)   = Single <$> f c
  traverseCat f (Deep l d r) = Deep <$> traverseCat f l <*> traverseCat (traverseCat f) d <*> traverseCat f r

data Node r a b where
  N2 ::          r b c -> r a b -> Node r a c
  N3 :: r c d -> r b c -> r a b -> Node r a d

instance Catenated where
  foldCat f (N2 a b)       = f a . f b
  foldCat f (N3 a b c)     = f a . f b . f c
  traverseCat f (N2 a b)   = N2 <$> f a <*> f b
  traverseCat f (N3 a b c) = N3 <$> f a <*> f b <*> f c

data Digit r a b where
  D1 ::                            r a b -> Digit r a b
  D2 ::                   r b c -> r a b -> Digit r a c
  D3 ::          r c d -> r b c -> r a b -> Digit r a d
  D4 :: r d e -> r c d -> r b c -> r a b -> Digit r a e

instance Categorical Digit where
  foldCat f (D1 a)       = f a
  foldCat f (D2 a b)     = f a . f b
  foldCat f (D3 a b c)   = f a . f b . f c
  foldCat f (D4 a b c d) = f a . f b . f c . f d
  traverseCat f (D1 a)       = D1 <$> f a
  traverseCat f (D2 a b)     = D2 <$> f a <*> f b
  traverseCat f (D3 a b c)   = D3 <$> f a <*> f b <*> f c
  traverseCat f (D4 a b c d) = D4 <$> f a <*> f b <*> f c <*> f d

instance Cons Seq where
  a <| Id                     = Single a
  a <| Single b               = Deep (D1 a) Id (D1 b)
  a <| Deep (D4 b c d e) m sf = Deep (D2 a b) (N3 c d e <| m) sf
  a <| Deep (D3 b c d) m sf   = Deep (D4 a b c d) m sf
  a <| Deep (D2 b c) m sf     = Deep (D3 a b c) m sf
  a <| Deep (D1 b) m sf       = Deep (D2 a b) m sf

instance Snoc Seq where
  Id |> a                     = Single a
  Single b |> a               = Deep (D1 b) Id (D1 a)
  Deep pr m (D4 e d c b) |> a = Deep pr (m |> N3 e d c) (D2 b a)
  Deep pr m (D3 d c b) |> a   = Deep pr m (D4 d c b a)
  Deep pr m (D2 c b) |> a     = Deep pr m (D3 c b a)
  Deep pr m (D1 b) |> a       = Deep pr m (D2 b a)

null :: Seq r a b -> Bool
null Id = True
null _ = False

singleton :: r a b -> Seq r a b
singleton = Single
