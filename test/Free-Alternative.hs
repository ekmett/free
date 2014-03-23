{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
-- Test for isomorphism

import Control.Alternative.Free
import Control.Monad
import Test.QuickCheck
import Control.Applicative

data TestCase a = TLift (a)
                | TPure Bool
                | TApXor (TestCase a) (TestCase a)
                | TAlt (TestCase a) (TestCase a)
                | TEmpty deriving (Show)

instance (Arbitrary a) => Arbitrary (TestCase a) where
  arbitrary = sized $ make
              where
                make 0 = leaf 0
                make d = frequency [(1,leaf d),(3,node d)]

                leaf d = frequency
                         [(1, return TEmpty),
                          (2, liftM TLift (resize (d-1) arbitrary)),
                          (1, liftM TPure arbitrary)]

                node d = let smaller = make (d `div` 2) in
                         frequency
                             [(1, liftM2 TAlt smaller smaller),
                              (1, liftM2 TApXor smaller smaller)]

  shrink (TLift x) = (TLift <$> (shrink x))
  shrink (TPure _) = []
  shrink TEmpty    = []
  shrink (TApXor x y) = [x, y] ++ (flip TApXor y <$> shrink x) ++ (TApXor x <$> shrink y)
  shrink (TAlt x y) = [x, y] ++ (flip TAlt y <$> shrink x) ++ (TAlt x <$> shrink y)

evalTest :: Alternative g => (f Bool -> g Bool) -> TestCase (f Bool) -> g Bool
evalTest _ (TEmpty) = empty
evalTest _ (TPure x) = pure x
evalTest lift (TLift f) = lift f
evalTest lift (TApXor x y) = (fmap (/=) (evalTest lift x)) <*> (evalTest lift y)
evalTest lift (TAlt x y) = (evalTest lift x) <|> (evalTest lift y)


isomorphism :: (Alternative f, Eq (f Bool)) => TestCase (f Bool) -> Bool
isomorphism test =
  let a = evalTest id test in
  let b = runAlt id $ evalTest liftAlt test in
  a == b

-- Allows for a weaker version of equality 
weakIsomorphism :: (Alternative f, QuickEq (f Bool)) => TestCase (f Bool) -> Property
weakIsomorphism test =
  let a = evalTest id test in
  let b = runAlt id $ evalTest liftAlt test in
   a `quickEq` b

--- Example with Ziplists
  
newtype ZL a = ZL { foobar :: [a] } deriving (Functor, Show, Arbitrary, Eq)

class QuickEq a where
  boundedEq :: a -> a -> Int -> Bool
  quickEq :: a -> a -> Property
  quickEq a b = forAll (sized (\n -> choose (0,2*n+5))) $ boundedEq a b

instance (Eq a) => QuickEq (ZL a) where
  boundedEq (ZL as) (ZL bs) n = (take n as) == (take n bs)

instance Applicative ZL where
  pure = ZL . repeat
  (ZL as) <*> (ZL bs) = ZL $ zipWith id as bs

instance Alternative ZL where
  empty =  ZL []
  (ZL xs) <|> (ZL ys) = ZL (xs ++ ys)

l3 :: Alt ZL (Integer -> Integer)
l3 = liftAlt $ ZL [id,id,id]

l2 :: Alt ZL (Integer -> Integer)
l2 = liftAlt $ ZL [id,id]

l5 :: Alt ZL (Integer)
l5 = liftAlt $ ZL [1,2,3,4,5]

eval :: Alt ZL a -> ZL a
eval = runAlt id

exp1 = eval $ (l2 <|>  l3) <*>  l5        -- [1,2,1,2,3]
exp2 = (eval l2 <|> eval l3) <*> eval l5  -- [1,2,3,4,5]

weakLeftCatch :: (Alternative f, QuickEq (f Bool)) => Bool -> f Bool -> Property
weakLeftCatch x f = (pure x <|> f) `quickEq` (pure x)

{-
-------
Interesting tests to perform:

quickCheck (weakLeftCatch :: Bool -> (ZL Bool) -> Property)
quickCheck (weakIsomorphism :: TestCase (ZL Bool) -> Property) -- should fail
quickCheck (isomorphism :: TestCase (Maybe Bool) -> Bool)
quickCheck (isomorphism :: TestCase [Bool] -> Bool)
--------
-}
