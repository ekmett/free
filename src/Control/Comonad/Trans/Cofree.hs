{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE Rank2Types #-}
#if __GLASGOW_HASKELL__ >= 707
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}
#endif
#include "free-common.h"

-----------------------------------------------------------------------------
-- |
-- Module      :  Control.Comonad.Trans.Cofree
-- Copyright   :  (C) 2008-2013 Edward Kmett
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  provisional
-- Portability :  MPTCs, fundeps
--
-- The cofree comonad transformer
----------------------------------------------------------------------------
module Control.Comonad.Trans.Cofree
  ( CofreeT(..)
  , Cofree, cofree, runCofree
  , CofreeF(..)
  , ComonadCofree(..)
  , headF
  , tailF
  , transCofreeT
  , coiterT
  ) where

import Control.Applicative
import Control.Comonad
import Control.Comonad.Trans.Class
import Control.Comonad.Cofree.Class
import Control.Comonad.Env.Class
import Control.Comonad.Hoist.Class
import Control.Category
import Data.Bifunctor
import Data.Bifoldable
import Data.Bitraversable
import Data.Foldable
import Data.Functor.Classes
import Data.Functor.Identity
import Data.Traversable
import Control.Monad (liftM)
import Control.Monad.Trans
import Control.Monad.Zip
import Prelude hiding (id,(.))
import Data.Data
#if __GLASGOW_HASKELL__ >= 707
import GHC.Generics hiding (Infix, Prefix)
#endif

#if !(MIN_VERSION_base(4,8,0))
import Data.Monoid
#endif

infixr 5 :<

-- | This is the base functor of the cofree comonad transformer.
data CofreeF f a b = a :< f b
  deriving (Eq,Ord,Show,Read
#if __GLASGOW_HASKELL__ >= 707
           ,Typeable, Generic, Generic1
#endif
           )

#ifdef LIFTED_FUNCTOR_CLASSES
instance Show1 f => Show2 (CofreeF f) where
  liftShowsPrec2 spa _sla spb slb d (a :< fb) =
    showParen (d > 5) $
      spa 6 a . showString " :< " . liftShowsPrec spb slb 6 fb

instance (Show1 f, Show a) => Show1 (CofreeF f a) where
  liftShowsPrec = liftShowsPrec2 showsPrec showList

#else
instance (Functor f, Show1 f, Show a) => Show1 (CofreeF f a) where
  showsPrec1 d (a :< fb) = showParen (d > 5) $
    showsPrec 6 a .  showString " :< " . showsPrec1 6 fb
#endif

#ifdef LIFTED_FUNCTOR_CLASSES
instance Read1 f => Read2 (CofreeF f) where
  liftReadsPrec2 rpa _rla rpb rlb d =
    readParen (d > 5) $
      (\r' -> [ (u :< v, w)
              | (u, s) <- rpa 6 r'
              , (":<", t) <- lex s
              , (v, w) <- liftReadsPrec rpb rlb 6 t
              ])

instance (Read1 f, Read a) => Read1 (CofreeF f a) where
  liftReadsPrec = liftReadsPrec2 readsPrec readList
#else
instance (Read1 f, Read a) => Read1 (CofreeF f a) where
  readsPrec1 d =
    readParen (d > 5) $
      (\r' -> [ (u :< v,w)
              | (u, s) <- readsPrec 6 r'
              , (":<", t) <- lex s
              , (v, w) <- readsPrec1 6 t
              ])
#endif

#ifdef LIFTED_FUNCTOR_CLASSES
instance Eq1 f => Eq2 (CofreeF f) where
  liftEq2 eqa eqfb (a :< fb) (a' :< fb') = eqa a a' && liftEq eqfb fb fb'

instance (Eq1 f, Eq a) => Eq1 (CofreeF f a) where
  liftEq = liftEq2 (==)
#else
instance (Eq1 f, Eq a) => Eq1 (CofreeF f a) where
  eq1 (a :< fb) (a' :< fb') = a == a' && eq1 fb fb'
#endif

#ifdef LIFTED_FUNCTOR_CLASSES
instance Ord1 f => Ord2 (CofreeF f) where
  liftCompare2 cmpa cmpfb (a :< fb) (a' :< fb') =
    case cmpa a a' of
      LT -> LT
      EQ -> liftCompare cmpfb fb fb'
      GT -> GT

instance (Ord1 f, Ord a) => Ord1 (CofreeF f a) where
  liftCompare = liftCompare2 compare
#else
instance (Ord1 f, Ord a) => Ord1 (CofreeF f a) where
  compare1 (a :< fb) (a' :< fb') =
    case compare a a' of
      LT -> LT
      EQ -> compare1 fb fb'
      GT -> GT
#endif

-- | Extract the head of the base functor
headF :: CofreeF f a b -> a
headF (a :< _) = a

-- | Extract the tails of the base functor
tailF :: CofreeF f a b -> f b
tailF (_ :< as) = as

instance Functor f => Functor (CofreeF f a) where
  fmap f (a :< as)  = a :< fmap f as

instance Foldable f => Foldable (CofreeF f a) where
  foldMap f (_ :< as) = foldMap f as

instance Traversable f => Traversable (CofreeF f a) where
  traverse f (a :< as) = (a :<) <$> traverse f as

instance Functor f => Bifunctor (CofreeF f) where
  bimap f g (a :< as)  = f a :< fmap g as

instance Foldable f => Bifoldable (CofreeF f) where
  bifoldMap f g (a :< as)  = f a `mappend` foldMap g as

instance Traversable f => Bitraversable (CofreeF f) where
  bitraverse f g (a :< as) = (:<) <$> f a <*> traverse g as

transCofreeF :: (forall x. f x -> g x) -> CofreeF f a b -> CofreeF g a b
transCofreeF t (a :< fb) = a :< t fb
{-# INLINE transCofreeF #-}

-- | This is a cofree comonad of some functor @f@, with a comonad @w@ threaded through it at each level.
newtype CofreeT f w a = CofreeT { runCofreeT :: w (CofreeF f a (CofreeT f w a)) }
#if __GLASGOW_HASKELL__ >= 707
  deriving Typeable
#endif

-- | The cofree `Comonad` of a functor @f@.
type Cofree f = CofreeT f Identity

{- |
Wrap another layer around a cofree comonad value.

@cofree@ is a right inverse of `runCofree`.

@
runCofree . cofree == id
@
-}
cofree :: CofreeF f a (Cofree f a) -> Cofree f a
cofree = CofreeT . Identity
{-# INLINE cofree #-}


{- |
Unpeel the first layer off a cofree comonad value.

@runCofree@ is a right inverse of `cofree`.

@
cofree . runCofree == id
@
-}
runCofree :: Cofree f a -> CofreeF f a (Cofree f a)
runCofree = runIdentity . runCofreeT
{-# INLINE runCofree #-}

instance (Functor f, Functor w) => Functor (CofreeT f w) where
  fmap f = CofreeT . fmap (bimap f (fmap f)) . runCofreeT

instance (Functor f, Comonad w) => Comonad (CofreeT f w) where
  extract = headF . extract . runCofreeT
  extend f = CofreeT . extend (\w -> f (CofreeT w) :< (extend f <$> tailF (extract w))) . runCofreeT

instance (Foldable f, Foldable w) => Foldable (CofreeT f w) where
  foldMap f = foldMap (bifoldMap f (foldMap f)) . runCofreeT

instance (Traversable f, Traversable w) => Traversable (CofreeT f w) where
  traverse f = fmap CofreeT . traverse (bitraverse f (traverse f)) . runCofreeT

instance ComonadTrans (CofreeT f) where
  lower = fmap headF . runCofreeT

instance (Functor f, Comonad w) => ComonadCofree f (CofreeT f w) where
  unwrap = tailF . extract . runCofreeT

instance (Functor f, ComonadEnv e w) => ComonadEnv e (CofreeT f w) where
  ask = ask . lower
  {-# INLINE ask #-}

instance Functor f => ComonadHoist (CofreeT f) where
  cohoist g = CofreeT . fmap (second (cohoist g)) . g . runCofreeT

instance Show (w (CofreeF f a (CofreeT f w a))) => Show (CofreeT f w a) where
  showsPrec d (CofreeT w) = showParen (d > 10) $
    showString "CofreeT " . showsPrec 11 w

instance Read (w (CofreeF f a (CofreeT f w a))) => Read (CofreeT f w a) where
  readsPrec d = readParen (d > 10) $ \r ->
     [(CofreeT w, t) | ("CofreeT", s) <- lex r, (w, t) <- readsPrec 11 s]

instance Eq (w (CofreeF f a (CofreeT f w a))) => Eq (CofreeT f w a) where
  CofreeT a == CofreeT b = a == b

instance Ord (w (CofreeF f a (CofreeT f w a))) => Ord (CofreeT f w a) where
  compare (CofreeT a) (CofreeT b) = compare a b

instance (Alternative f, Monad w) => Monad (CofreeT f w) where
#if __GLASGOW_HASKELL__ < 710
  return = CofreeT . return . (:< empty)
  {-# INLINE return #-}
#endif
  CofreeT cx >>= f = CofreeT $ do
    a :< m <- cx
    b :< n <- runCofreeT $ f a
    return $ b :< (n <|> fmap (>>= f) m)


instance (Alternative f, Applicative w) => Applicative (CofreeT f w) where
  pure = CofreeT . pure . (:< empty)
  {-# INLINE pure #-}
  wf <*> wa = CofreeT $ go <$> runCofreeT wf <*> runCofreeT wa where
    go (f :< t) a = case bimap f (fmap f) a of
      b :< n -> b :< (n <|> fmap (<*> wa) t)
  {-# INLINE (<*>) #-}

instance Alternative f => MonadTrans (CofreeT f) where
  lift = CofreeT . liftM (:< empty)

instance (Alternative f, MonadZip f, MonadZip m) => MonadZip (CofreeT f m) where
  mzip (CofreeT ma) (CofreeT mb) = CofreeT $ do
                                     (a :< fa, b :< fb) <- mzip ma mb
                                     return $ (a, b) :< (uncurry mzip <$> mzip fa fb)

-- | Lift a natural transformation from @f@ to @g@ into a comonad homomorphism from @'CofreeT' f w@ to @'CofreeT' g w@
transCofreeT :: (Functor g, Comonad w) => (forall x. f x -> g x) -> CofreeT f w a -> CofreeT g w a
transCofreeT t = CofreeT . liftW (fmap (transCofreeT t) . transCofreeF t) . runCofreeT

-- | Unfold a @CofreeT@ comonad transformer from a coalgebra and an initial comonad.
coiterT :: (Functor f, Comonad w) => (w a -> f (w a)) -> w a -> CofreeT f w a
coiterT psi = CofreeT . extend (\w -> extract w :< fmap (coiterT psi) (psi w))

#if __GLASGOW_HASKELL__ < 707

instance Typeable1 f => Typeable2 (CofreeF f) where
  typeOf2 t = mkTyConApp cofreeFTyCon [typeOf1 (f t)] where
    f :: CofreeF f a b -> f a
    f = undefined

instance (Typeable1 f, Typeable1 w) => Typeable1 (CofreeT f w) where
  typeOf1 t = mkTyConApp cofreeTTyCon [typeOf1 (f t), typeOf1 (w t)] where
    f :: CofreeT f w a -> f a
    f = undefined
    w :: CofreeT f w a -> w a
    w = undefined

cofreeFTyCon, cofreeTTyCon :: TyCon
#if __GLASGOW_HASKELL__ < 704
cofreeTTyCon = mkTyCon "Control.Comonad.Trans.Cofree.CofreeT"
cofreeFTyCon = mkTyCon "Control.Comonad.Trans.Cofree.CofreeF"
#else
cofreeTTyCon = mkTyCon3 "free" "Control.Comonad.Trans.Cofree" "CofreeT"
cofreeFTyCon = mkTyCon3 "free" "Control.Comonad.Trans.Cofree" "CofreeF"
#endif
{-# NOINLINE cofreeTTyCon #-}
{-# NOINLINE cofreeFTyCon #-}

#else
#define Typeable1 Typeable
#endif

instance
  ( Typeable1 f, Typeable a, Typeable b
  , Data a, Data (f b), Data b
  ) => Data (CofreeF f a b) where
    gfoldl f z (a :< as) = z (:<) `f` a `f` as
    toConstr _ = cofreeFConstr
    gunfold k z c = case constrIndex c of
        1 -> k (k (z (:<)))
        _ -> error "gunfold"
    dataTypeOf _ = cofreeFDataType
    dataCast1 f = gcast1 f

instance
  ( Typeable1 f, Typeable1 w, Typeable a
  , Data (w (CofreeF f a (CofreeT f w a)))
  , Data a
  ) => Data (CofreeT f w a) where
    gfoldl f z (CofreeT w) = z CofreeT `f` w
    toConstr _ = cofreeTConstr
    gunfold k z c = case constrIndex c of
        1 -> k (z CofreeT)
        _ -> error "gunfold"
    dataTypeOf _ = cofreeTDataType
    dataCast1 f = gcast1 f

cofreeFConstr, cofreeTConstr :: Constr
cofreeFConstr = mkConstr cofreeFDataType ":<" [] Infix
cofreeTConstr = mkConstr cofreeTDataType "CofreeT" [] Prefix
{-# NOINLINE cofreeFConstr #-}
{-# NOINLINE cofreeTConstr #-}

cofreeFDataType, cofreeTDataType :: DataType
cofreeFDataType = mkDataType "Control.Comonad.Trans.Cofree.CofreeF" [cofreeFConstr]
cofreeTDataType = mkDataType "Control.Comonad.Trans.Cofree.CofreeT" [cofreeTConstr]
{-# NOINLINE cofreeFDataType #-}
{-# NOINLINE cofreeTDataType #-}

-- lowerF :: (Functor f, Comonad w) => CofreeT f w a -> f a
-- lowerF = fmap extract . unwrap
