{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Control.Comonad.Trans.Cofree
-- Copyright   :  (C) 2008-2011 Edward Kmett,
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  provisional
-- Portability :  MPTCs, fundeps
--
-- The cofree comonad transformer
--
----------------------------------------------------------------------------
module Control.Comonad.Trans.Cofree
  ( CofreeT(..)
  , CofreeF(..)
  , headF
  , tailF
--  , lowerF(..)
  ) where

import Control.Applicative
import Control.Comonad
import Control.Comonad.Trans.Class
import Control.Comonad.Cofree.Class
import Control.Category
import Data.Bifunctor
import Data.Bifoldable
import Data.Bitraversable
import Data.Foldable
import Data.Semigroup
import Data.Traversable
import Prelude hiding (id,(.))

#ifdef GHC_TYPEABLE
import Data.Data
#endif

infixr 5 :<


data CofreeF f a b = a :< f b
  deriving (Eq,Ord,Show,Read)

headF :: CofreeF f a b -> a
headF (a :< _) = a

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

newtype CofreeT f w a = CofreeT { runCofreeT :: w (CofreeF f a (CofreeT f w a)) }

instance (Functor f, Functor w) => Functor (CofreeT f w) where
  fmap f = CofreeT . fmap (bimap f (fmap f)) . runCofreeT

instance (Functor f, Comonad w) => Comonad (CofreeT f w) where
  extract (CofreeT w) = case extract w of
    a :< _ -> a
  extend f = CofreeT . extend (\w -> f (CofreeT w) :< (extend f <$> tailF (extract w))) . runCofreeT

instance (Foldable f, Foldable w) => Foldable (CofreeT f w) where
  foldMap f = foldMap (bifoldMap f (foldMap f)) . runCofreeT

instance (Traversable f, Traversable w) => Traversable (CofreeT f w) where
  traverse f = fmap CofreeT . traverse (bitraverse f (traverse f)) . runCofreeT

instance Functor f => ComonadTrans (CofreeT f) where
  lower = fmap headF . runCofreeT

instance (Functor f, Comonad w) => ComonadCofree f (CofreeT f w) where
  unwrap = tailF . extract . runCofreeT

instance Show (w (CofreeF f a (CofreeT f w a))) => Show (CofreeT f w a) where
  showsPrec d w = showParen (d > 10) $
    showString "CofreeT " . showsPrec 11 w

instance Read (w (CofreeF f a (CofreeT f w a))) => Read (CofreeT f w a) where
  readsPrec d = readParen (d > 10) $ \r ->
     [(CofreeT w, t) | ("CofreeT", s) <- lex r, (w, t) <- readsPrec 11 s]

instance Eq (w (CofreeF f a (CofreeT f w a))) => Eq (CofreeT f w a) where
  CofreeT a == CofreeT b = a == b

instance Ord (w (CofreeF f a (CofreeT f w a))) => Ord (CofreeT f w a) where
  compare (CofreeT a) (CofreeT b) = compare a b

#ifdef GHC_TYPEABLE

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
cofreeFDataType = mkDataType "Control.Comonad.Cofree.CofreeF" [cofreeFConstr]
cofreeTDataType = mkDataType "Control.Comonad.Cofree.CofreeT" [cofreeTConstr]
{-# NOINLINE cofreeFDataType #-}
{-# NOINLINE cofreeTDataType #-}
#endif

-- lowerF :: (Functor f, Comonad w) => CofreeT f w a -> f a
-- lowerF = fmap extract . unwrap
