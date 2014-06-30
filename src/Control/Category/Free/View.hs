{-# LANGUAGE GADTs, PolyKinds #-}
module Control.Category.Free.View
  ( View(..)
  , Uncons(..)
  , Unsnoc(..)
  , Cons(..)
  , Snoc(..)
  ) where

infixr 5 :|
data View l r a c where
  Empty :: View l r a a
  (:|) :: l b c -> r a b -> View l r a c

class Uncons t where
  uncons :: t r a b -> View r (t r) a b

class Unsnoc t where
  unsnoc :: t r a b -> View (t r) r a b

infixr 5 <|
class Cons t where
  (<|) :: r b c -> t r a b -> t r a c

infixl 5 |>
class Snoc t where
  (|>) :: t r b c -> r a b -> t r a c
