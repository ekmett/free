{-# LANGUAGE GADTs, PolyKinds #-}
module View
  ( View(..)
  , Uncons(..)
  , Unsnoc(..)
  ) where

data View l r a c where
  Empty :: View l r a a
  (:|) :: l b c -> r a b -> View l r a c

class Uncons t where
  uncons :: t r a b -> View r (t r) a b

class Unsnoc t where
  unsnoc :: t r a b -> View (t r) r a b
